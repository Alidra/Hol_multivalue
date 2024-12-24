Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIVIDES_LE_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import INT_ABS_MUL_spec.
Require Import INT_ENTIRE_spec.
Require Import INT_LE_MUL_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import int_divides_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1482678_spec.
Require Import thm1482679_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1821_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
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
Require Import thm1982709_spec.
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
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318526_spec.
Require Import thm2318527_spec.
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
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2429417 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2429418 (x : int) (h1 : term0) : term1 x.
Proof. exact (@lem2429417 h1 x). Qed.
Lemma lem2429419 (x : int) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem2429420 (x : int) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem2429419 x) (@lem2429418 x h1)). Qed.
Lemma lem2429421 (x : int) (y : int) (h1 : term0) : term3 x y.
Proof. exact (@lem2429420 x h1 y). Qed.
Lemma lem2429422 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem2429423 (x : int) (y : int) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem2429422 x y) (@lem2429421 x y h1)). Qed.
Lemma lem2429424 (x : int) (y : int) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem2429425 (x : int) (y : int) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem2429423 x y h1 (@lem2429424 x y h2)). Qed.
Lemma lem2429426 (x : int) (y : int) (h1 : term5 x y) : term7 x y.
Proof. exact (fun h0 : term0 => @lem2429425 x y h0 h1). Qed.
Lemma lem2429427 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2429428 (x : int) (y : int) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem2429426 x y h2 (@lem2429427 h1)). Qed.
Lemma lem2429429 (x : int) (y : int) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : term5 x y => @lem2429428 x y h1 h0). Qed.
Lemma lem2429430 (x : int) (h1 : term0) : term2 x.
Proof. exact (fun y : int => @lem2429429 x y h1). Qed.
Lemma lem2429431 (h1 : term0) : term0.
Proof. exact (fun x : int => @lem2429430 x h1). Qed.
Lemma lem2429432 : term8.
Proof. exact (fun h0 : term0 => @lem2429431 h0). Qed.
Lemma lem2429433 : term0.
Proof. exact (@lem2429432 (@lem2302746)). Qed.
Lemma lem2429434 (x : int) : term1 x.
Proof. exact (@lem2429433 x). Qed.
Lemma lem2429435 (x : int) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem2429436 (x : int) : term2 x.
Proof. exact (EQ_MP (@lem2429435 x) (@lem2429434 x)). Qed.
Lemma lem2429437 (x : int) (y : int) : term3 x y.
Proof. exact (@lem2429436 x y). Qed.
Lemma lem2429438 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem2429440 (x : int) (y : int) : (term9 x y) = ((term10 x y) = (term11 x y)).
Proof. exact (@lem2318604 ((term10 x y) = (term11 x y))). Qed.
Lemma lem2429479 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (@lem17646 (term10 x y) (term11 x y)). Qed.
Lemma lem2429482 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2429483 (x : int) (y : int) : (term10 x y) = (term15 x y).
Proof. exact (@lem2429482 x (int_mul x y)). Qed.
Lemma lem2429485 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2429486 (x : int) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2429487 (x : int) (y : int) : (term15 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2429486 x) (@lem2429485 x y)). Qed.
Lemma lem2429489 (x : int) (y : int) : (term10 x y) = (term19 x y).
Proof. exact (TRANS (@lem2429483 x y) (@lem2429487 x y)). Qed.
Lemma lem2429491 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2429492 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (@lem2429491 (term24 x y) term25). Qed.
Lemma lem2429494 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2429495 (x : int) (y : int) : (term23 x y) = (term26 x y).
Proof. exact (@lem2429494 (term27 x y) term25). Qed.
Lemma lem2429497 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2429498 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (@lem2429497 (term24 x y) term32). Qed.
Lemma lem2429500 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2429501 (x : int) (y : int) : (term33 x y) = (term34 x y).
Proof. exact (@lem2429500 x (term35 y)). Qed.
Lemma lem2429503 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2429504 (y : int) : (term38 y) = (term39 y).
Proof. exact (@lem2429503 y term32). Qed.
Lemma lem2429506 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2429507 : term41 = term42.
Proof. exact (@lem2429506 term43). Qed.
Lemma lem2429508 (y : int) : (term44 y) = (term44 y).
Proof. exact (eq_refl (term44 y)). Qed.
Lemma lem2429509 (y : int) : (term39 y) = (term45 y).
Proof. exact (MK_COMB (@lem2429508 y) (@lem2429507)). Qed.
Lemma lem2429510 (y : int) : (term38 y) = (term45 y).
Proof. exact (TRANS (@lem2429504 y) (@lem2429509 y)). Qed.
Lemma lem2429511 (x : int) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem2429512 (x : int) (y : int) : (term34 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem2429511 x) (@lem2429510 y)). Qed.
Lemma lem2429513 (x : int) (y : int) : (term33 x y) = (term47 x y).
Proof. exact (TRANS (@lem2429501 x y) (@lem2429512 x y)). Qed.
Lemma lem2429514 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2429515 (x : int) (y : int) : (term48 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem2429514) (@lem2429513 x y)). Qed.
Lemma lem2429517 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2429518 : term41 = term42.
Proof. exact (@lem2429517 term43). Qed.
Lemma lem2429519 (x : int) (y : int) : (term31 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem2429515 x y) (@lem2429518)). Qed.
Lemma lem2429520 (x : int) (y : int) : (term30 x y) = (term50 x y).
Proof. exact (TRANS (@lem2429498 x y) (@lem2429519 x y)). Qed.
Lemma lem2429521 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2429522 (x : int) (y : int) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem2429521) (@lem2429520 x y)). Qed.
Lemma lem2429524 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2429525 : term53 = term54.
Proof. exact (@lem2429524 (NUMERAL 0)). Qed.
Lemma lem2429526 (x : int) (y : int) : (term26 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem2429522 x y) (@lem2429525)). Qed.
Lemma lem2429527 (x : int) (y : int) : (term23 x y) = (term55 x y).
Proof. exact (TRANS (@lem2429495 x y) (@lem2429526 x y)). Qed.
Lemma lem2429528 (x : int) (y : int) : (term22 x y) = (term55 x y).
Proof. exact (TRANS (@lem2429492 x y) (@lem2429527 x y)). Qed.
Lemma lem2429529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2429530 (x : int) (y : int) : (term56 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem2429529) (@lem2429489 x y)). Qed.
Lemma lem2429531 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem2429530 x y) (@lem2429528 x y)). Qed.
Lemma lem2429533 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2429534 (y : int) (x : int) : (term60 x y) = (term61 y x).
Proof. exact (@lem2429533 (int_mul x y) x). Qed.
Lemma lem2429536 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2429537 (y : int) (x : int) : (term61 y x) = (term62 y x).
Proof. exact (@lem2429536 (term63 x y) x). Qed.
Lemma lem2429539 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2429540 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (@lem2429539 (int_mul x y) term32). Qed.
Lemma lem2429542 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2429543 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2429544 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem2429543) (@lem2429542 x y)). Qed.
Lemma lem2429546 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2429547 : term41 = term42.
Proof. exact (@lem2429546 term43). Qed.
Lemma lem2429548 (x : int) (y : int) : (term65 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem2429544 x y) (@lem2429547)). Qed.
Lemma lem2429549 (x : int) (y : int) : (term64 x y) = (term68 x y).
Proof. exact (TRANS (@lem2429540 x y) (@lem2429548 x y)). Qed.
Lemma lem2429550 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2429551 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem2429550) (@lem2429549 x y)). Qed.
Lemma lem2429552 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2429553 (y : int) (x : int) : (term62 y x) = (term71 y x).
Proof. exact (MK_COMB (@lem2429551 x y) (@lem2429552 x)). Qed.
Lemma lem2429554 (y : int) (x : int) : (term61 y x) = (term71 y x).
Proof. exact (TRANS (@lem2429537 y x) (@lem2429553 y x)). Qed.
Lemma lem2429555 (y : int) (x : int) : (term60 x y) = (term71 y x).
Proof. exact (TRANS (@lem2429534 y x) (@lem2429554 y x)). Qed.
Lemma lem2429558 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2429559 (x : int) (y : int) : (term11 x y) = (term72 x y).
Proof. exact (@lem2429558 term25 (term24 x y)). Qed.
Lemma lem2429561 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2429562 : term53 = term54.
Proof. exact (@lem2429561 (NUMERAL 0)). Qed.
Lemma lem2429563 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2429564 : term73 = term74.
Proof. exact (MK_COMB (@lem2429563) (@lem2429562)). Qed.
Lemma lem2429566 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2429567 (x : int) (y : int) : (term33 x y) = (term34 x y).
Proof. exact (@lem2429566 x (term35 y)). Qed.
Lemma lem2429569 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2429570 (y : int) : (term38 y) = (term39 y).
Proof. exact (@lem2429569 y term32). Qed.
Lemma lem2429572 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2429573 : term41 = term42.
Proof. exact (@lem2429572 term43). Qed.
Lemma lem2429574 (y : int) : (term44 y) = (term44 y).
Proof. exact (eq_refl (term44 y)). Qed.
Lemma lem2429575 (y : int) : (term39 y) = (term45 y).
Proof. exact (MK_COMB (@lem2429574 y) (@lem2429573)). Qed.
Lemma lem2429576 (y : int) : (term38 y) = (term45 y).
Proof. exact (TRANS (@lem2429570 y) (@lem2429575 y)). Qed.
Lemma lem2429577 (x : int) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem2429578 (x : int) (y : int) : (term34 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem2429577 x) (@lem2429576 y)). Qed.
Lemma lem2429579 (x : int) (y : int) : (term33 x y) = (term47 x y).
Proof. exact (TRANS (@lem2429567 x y) (@lem2429578 x y)). Qed.
Lemma lem2429580 (x : int) (y : int) : (term72 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem2429564) (@lem2429579 x y)). Qed.
Lemma lem2429582 (x : int) (y : int) : (term11 x y) = (term75 x y).
Proof. exact (TRANS (@lem2429559 x y) (@lem2429580 x y)). Qed.
Lemma lem2429583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2429584 (y : int) (x : int) : (term76 x y) = (term77 y x).
Proof. exact (MK_COMB (@lem2429583) (@lem2429555 y x)). Qed.
Lemma lem2429585 (x : int) (y : int) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem2429584 y x) (@lem2429582 x y)). Qed.
Lemma lem2429586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2429587 (x : int) (y : int) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem2429586) (@lem2429531 x y)). Qed.
Lemma lem2429588 (x : int) (y : int) : (term13 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem2429587 x y) (@lem2429585 x y)). Qed.
Lemma lem2429589 (x : int) (y : int) : (term12 x y) = (term82 x y).
Proof. exact (TRANS (@lem2429479 x y) (@lem2429588 x y)). Qed.
Lemma lem2429593 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2429629 (x : int) (y : int) : (term84 x y) = (term82 x y).
Proof. exact (@lem2429593 (term82 x y)). Qed.
Lemma lem2429630 (y : int) (x : int) : (term19 x y) = (term85 y x).
Proof. exact (@lem1988287 (term17 x y) (real_of_int x)). Qed.
Lemma lem2429649 (y : int) (x : int) : (term86 y x) = (term87 y x).
Proof. exact (@lem1982792 (term17 x y) (real_of_int x)). Qed.
Lemma lem2429650 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2429651 (y : int) (x : int) : (term88 y x) = (term89 y x).
Proof. exact (MK_COMB (@lem2429650) (@lem2429649 y x)). Qed.
Lemma lem2429652 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2429653 (y : int) (x : int) : (term85 y x) = (term90 y x).
Proof. exact (MK_COMB (@lem2429651 y x) (@lem2429652)). Qed.
Lemma lem2429654 (y : int) (x : int) : (term19 x y) = (term90 y x).
Proof. exact (TRANS (@lem2429630 y x) (@lem2429653 y x)). Qed.
Lemma lem2429655 (x : int) (y : int) : (term55 x y) = (term91 x y).
Proof. exact (@lem1988287 term54 (term50 x y)). Qed.
Lemma lem2429656 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2429662 (y : int) : (term45 y) = (term92 y).
Proof. exact (@lem1982792 (real_of_int y) term42). Qed.
Lemma lem2429664 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2429665 : term42 = term94.
Proof. exact (@lem2429664 term43). Qed.
Lemma lem2429667 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2429668 : term97 = term98.
Proof. exact (@lem2429667 term43). Qed.
Lemma lem2429669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2429670 : term99 = term100.
Proof. exact (MK_COMB (@lem2429669) (@lem2429668)). Qed.
Lemma lem2429671 : term101 = term102.
Proof. exact (MK_COMB (@lem2429670) (@lem2429665)). Qed.
Lemma lem2429672 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2429674 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2429675 : term106 = term107.
Proof. exact (@lem2429674 term43 term43). Qed.
Lemma lem2429676 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429677 : term109 = term43.
Proof. exact (EQ_MP (@lem2429676) (@lem940073)). Qed.
Lemma lem2429678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429679 : term107 = term42.
Proof. exact (MK_COMB (@lem2429678) (@lem2429677)). Qed.
Lemma lem2429680 : term106 = term42.
Proof. exact (TRANS (@lem2429675) (@lem2429679)). Qed.
Lemma lem2429682 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2429683 : term101 = term112.
Proof. exact (@lem2429682 term43 term43). Qed.
Lemma lem2429684 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429685 : term109 = term43.
Proof. exact (EQ_MP (@lem2429684) (@lem940073)). Qed.
Lemma lem2429686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429687 : term107 = term42.
Proof. exact (MK_COMB (@lem2429686) (@lem2429685)). Qed.
Lemma lem2429688 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2429689 : term112 = term97.
Proof. exact (MK_COMB (@lem2429688) (@lem2429687)). Qed.
Lemma lem2429690 : term101 = term97.
Proof. exact (TRANS (@lem2429683) (@lem2429689)). Qed.
Lemma lem2429691 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2429692 : term113 = term114.
Proof. exact (MK_COMB (@lem2429691) (@lem2429690)). Qed.
Lemma lem2429693 : term103 = term98.
Proof. exact (MK_COMB (@lem2429692) (@lem2429680)). Qed.
Lemma lem2429694 : term102 = term98.
Proof. exact (TRANS (@lem2429672) (@lem2429693)). Qed.
Lemma lem2429695 : term101 = term98.
Proof. exact (TRANS (@lem2429671) (@lem2429694)). Qed.
Lemma lem2429697 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2429698 : term98 = term97.
Proof. exact (@lem2429697 term97). Qed.
Lemma lem2429699 : term101 = term97.
Proof. exact (TRANS (@lem2429695) (@lem2429698)). Qed.
Lemma lem2429700 (y : int) : (term116 y) = (term116 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem2429703 (y : int) : (term92 y) = (term117 y).
Proof. exact (MK_COMB (@lem2429700 y) (@lem2429699)). Qed.
Lemma lem2429705 (y : int) : (term45 y) = (term117 y).
Proof. exact (TRANS (@lem2429662 y) (@lem2429703 y)). Qed.
Lemma lem2429708 (x : int) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem2429709 (x : int) (y : int) : (term47 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem2429708 x) (@lem2429705 y)). Qed.
Lemma lem2429710 (y : int) (x : int) : (term118 x y) = (term119 y x).
Proof. exact (@lem1982781 (real_of_int y) (real_of_int x) term97). Qed.
Lemma lem2429711 (x : int) : (term120 x) = (term121 x).
Proof. exact (@lem1982747 term97 (real_of_int x)). Qed.
Lemma lem2429714 (x : int) (y : int) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem2429715 (y : int) (x : int) : (term119 y x) = (term87 y x).
Proof. exact (MK_COMB (@lem2429714 x y) (@lem2429711 x)). Qed.
Lemma lem2429716 (y : int) (x : int) : (term118 x y) = (term87 y x).
Proof. exact (TRANS (@lem2429710 y x) (@lem2429715 y x)). Qed.
Lemma lem2429717 (y : int) (x : int) : (term47 x y) = (term87 y x).
Proof. exact (TRANS (@lem2429709 x y) (@lem2429716 y x)). Qed.
Lemma lem2429718 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2429719 (y : int) (x : int) : (term49 x y) = (term122 y x).
Proof. exact (MK_COMB (@lem2429718) (@lem2429717 y x)). Qed.
Lemma lem2429720 (y : int) (x : int) : (term50 x y) = (term123 y x).
Proof. exact (MK_COMB (@lem2429719 y x) (@lem2429656)). Qed.
Lemma lem2429725 (y : int) (x : int) : (term123 y x) = (term124 y x).
Proof. exact (@lem1982755 (term17 x y) (term121 x) term42). Qed.
Lemma lem2429726 (y : int) (x : int) : (term50 x y) = (term124 y x).
Proof. exact (TRANS (@lem2429720 y x) (@lem2429725 y x)). Qed.
Lemma lem2429729 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem2429730 (y : int) (x : int) : (term126 x y) = (term127 y x).
Proof. exact (MK_COMB (@lem2429729) (@lem2429726 y x)). Qed.
Lemma lem2429731 (y : int) (x : int) : (term127 y x) = (term128 y x).
Proof. exact (@lem1982792 term54 (term124 y x)). Qed.
Lemma lem2429732 (y : int) (x : int) : (term129 y x) = (term130 y x).
Proof. exact (@lem1982781 (term17 x y) term97 (term131 x)). Qed.
Lemma lem2429733 (x : int) : (term132 x) = (term133 x).
Proof. exact (@lem1982781 (term121 x) term97 term42). Qed.
Lemma lem2429735 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2429736 : term42 = term94.
Proof. exact (@lem2429735 term43). Qed.
Lemma lem2429738 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2429739 : term97 = term98.
Proof. exact (@lem2429738 term43). Qed.
Lemma lem2429740 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2429741 : term99 = term100.
Proof. exact (MK_COMB (@lem2429740) (@lem2429739)). Qed.
Lemma lem2429742 : term101 = term102.
Proof. exact (MK_COMB (@lem2429741) (@lem2429736)). Qed.
Lemma lem2429743 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2429745 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2429746 : term106 = term107.
Proof. exact (@lem2429745 term43 term43). Qed.
Lemma lem2429747 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429748 : term109 = term43.
Proof. exact (EQ_MP (@lem2429747) (@lem940073)). Qed.
Lemma lem2429749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429750 : term107 = term42.
Proof. exact (MK_COMB (@lem2429749) (@lem2429748)). Qed.
Lemma lem2429751 : term106 = term42.
Proof. exact (TRANS (@lem2429746) (@lem2429750)). Qed.
Lemma lem2429753 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2429754 : term101 = term112.
Proof. exact (@lem2429753 term43 term43). Qed.
Lemma lem2429755 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429756 : term109 = term43.
Proof. exact (EQ_MP (@lem2429755) (@lem940073)). Qed.
Lemma lem2429757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429758 : term107 = term42.
Proof. exact (MK_COMB (@lem2429757) (@lem2429756)). Qed.
Lemma lem2429759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2429760 : term112 = term97.
Proof. exact (MK_COMB (@lem2429759) (@lem2429758)). Qed.
Lemma lem2429761 : term101 = term97.
Proof. exact (TRANS (@lem2429754) (@lem2429760)). Qed.
Lemma lem2429762 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2429763 : term113 = term114.
Proof. exact (MK_COMB (@lem2429762) (@lem2429761)). Qed.
Lemma lem2429764 : term103 = term98.
Proof. exact (MK_COMB (@lem2429763) (@lem2429751)). Qed.
Lemma lem2429765 : term102 = term98.
Proof. exact (TRANS (@lem2429743) (@lem2429764)). Qed.
Lemma lem2429766 : term101 = term98.
Proof. exact (TRANS (@lem2429742) (@lem2429765)). Qed.
Lemma lem2429768 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2429769 : term98 = term97.
Proof. exact (@lem2429768 term97). Qed.
Lemma lem2429770 : term101 = term97.
Proof. exact (TRANS (@lem2429766) (@lem2429769)). Qed.
Lemma lem2429771 (x : int) : (term134 x) = (term135 x).
Proof. exact (@lem1982749 term97 term97 (real_of_int x)). Qed.
Lemma lem2429773 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2429774 : term97 = term98.
Proof. exact (@lem2429773 term43). Qed.
Lemma lem2429776 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2429777 : term97 = term98.
Proof. exact (@lem2429776 term43). Qed.
Lemma lem2429778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2429779 : term99 = term100.
Proof. exact (MK_COMB (@lem2429778) (@lem2429777)). Qed.
Lemma lem2429780 : term136 = term137.
Proof. exact (MK_COMB (@lem2429779) (@lem2429774)). Qed.
Lemma lem2429781 : term137 = term138.
Proof. exact (@lem1981613 term97 term97 term42 term42). Qed.
Lemma lem2429783 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2429784 : term106 = term107.
Proof. exact (@lem2429783 term43 term43). Qed.
Lemma lem2429785 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429786 : term109 = term43.
Proof. exact (EQ_MP (@lem2429785) (@lem940073)). Qed.
Lemma lem2429787 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429788 : term107 = term42.
Proof. exact (MK_COMB (@lem2429787) (@lem2429786)). Qed.
Lemma lem2429789 : term106 = term42.
Proof. exact (TRANS (@lem2429784) (@lem2429788)). Qed.
Lemma lem2429791 (m : nat) (n : nat) : (term139 m n) = (term105 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2429792 : term136 = term107.
Proof. exact (@lem2429791 term43 term43). Qed.
Lemma lem2429793 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429794 : term109 = term43.
Proof. exact (EQ_MP (@lem2429793) (@lem940073)). Qed.
Lemma lem2429795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429796 : term107 = term42.
Proof. exact (MK_COMB (@lem2429795) (@lem2429794)). Qed.
Lemma lem2429797 : term136 = term42.
Proof. exact (TRANS (@lem2429792) (@lem2429796)). Qed.
Lemma lem2429798 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2429799 : term140 = term141.
Proof. exact (MK_COMB (@lem2429798) (@lem2429797)). Qed.
Lemma lem2429800 : term138 = term94.
Proof. exact (MK_COMB (@lem2429799) (@lem2429789)). Qed.
Lemma lem2429801 : term137 = term94.
Proof. exact (TRANS (@lem2429781) (@lem2429800)). Qed.
Lemma lem2429802 : term136 = term94.
Proof. exact (TRANS (@lem2429780) (@lem2429801)). Qed.
Lemma lem2429804 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2429805 : term94 = term42.
Proof. exact (@lem2429804 term42). Qed.
Lemma lem2429806 : term136 = term42.
Proof. exact (TRANS (@lem2429802) (@lem2429805)). Qed.
Lemma lem2429807 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2429808 : term142 = term143.
Proof. exact (MK_COMB (@lem2429807) (@lem2429806)). Qed.
Lemma lem2429809 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2429810 (x : int) : (term135 x) = (term144 x).
Proof. exact (MK_COMB (@lem2429808) (@lem2429809 x)). Qed.
Lemma lem2429811 (x : int) : (term134 x) = (term144 x).
Proof. exact (TRANS (@lem2429771 x) (@lem2429810 x)). Qed.
Lemma lem2429812 (x : int) : (term144 x) = (real_of_int x).
Proof. exact (@lem1982709 (real_of_int x)). Qed.
Lemma lem2429813 (x : int) : (term134 x) = (real_of_int x).
Proof. exact (TRANS (@lem2429811 x) (@lem2429812 x)). Qed.
Lemma lem2429814 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2429815 (x : int) : (term145 x) = (term116 x).
Proof. exact (MK_COMB (@lem2429814) (@lem2429813 x)). Qed.
Lemma lem2429816 (x : int) : (term133 x) = (term117 x).
Proof. exact (MK_COMB (@lem2429815 x) (@lem2429770)). Qed.
Lemma lem2429817 (x : int) : (term132 x) = (term117 x).
Proof. exact (TRANS (@lem2429733 x) (@lem2429816 x)). Qed.
Lemma lem2429820 (x : int) (y : int) : (term146 x y) = (term146 x y).
Proof. exact (eq_refl (term146 x y)). Qed.
Lemma lem2429821 (y : int) (x : int) : (term130 y x) = (term147 y x).
Proof. exact (MK_COMB (@lem2429820 x y) (@lem2429817 x)). Qed.
Lemma lem2429822 (y : int) (x : int) : (term129 y x) = (term147 y x).
Proof. exact (TRANS (@lem2429732 y x) (@lem2429821 y x)). Qed.
Lemma lem2429823 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem2429824 (y : int) (x : int) : (term128 y x) = (term149 y x).
Proof. exact (MK_COMB (@lem2429823) (@lem2429822 y x)). Qed.
Lemma lem2429825 (y : int) (x : int) : (term149 y x) = (term147 y x).
Proof. exact (@lem1982721 (term147 y x)). Qed.
Lemma lem2429826 (y : int) (x : int) : (term128 y x) = (term147 y x).
Proof. exact (TRANS (@lem2429824 y x) (@lem2429825 y x)). Qed.
Lemma lem2429827 (y : int) (x : int) : (term127 y x) = (term147 y x).
Proof. exact (TRANS (@lem2429731 y x) (@lem2429826 y x)). Qed.
Lemma lem2429828 (y : int) (x : int) : (term126 x y) = (term147 y x).
Proof. exact (TRANS (@lem2429730 y x) (@lem2429827 y x)). Qed.
Lemma lem2429829 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2429830 (y : int) (x : int) : (term150 x y) = (term151 y x).
Proof. exact (MK_COMB (@lem2429829) (@lem2429828 y x)). Qed.
Lemma lem2429831 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2429832 (y : int) (x : int) : (term91 x y) = (term152 y x).
Proof. exact (MK_COMB (@lem2429830 y x) (@lem2429831)). Qed.
Lemma lem2429833 (y : int) (x : int) : (term55 x y) = (term152 y x).
Proof. exact (TRANS (@lem2429655 x y) (@lem2429832 y x)). Qed.
Lemma lem2429834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2429835 (y : int) (x : int) : (term57 x y) = (term153 y x).
Proof. exact (MK_COMB (@lem2429834) (@lem2429654 y x)). Qed.
Lemma lem2429836 (y : int) (x : int) : (term59 x y) = (term154 y x).
Proof. exact (MK_COMB (@lem2429835 y x) (@lem2429833 y x)). Qed.
Lemma lem2429837 (x : int) (y : int) : (term71 y x) = (term155 x y).
Proof. exact (@lem1988287 (real_of_int x) (term68 x y)). Qed.
Lemma lem2429855 (x : int) (y : int) : (term156 x y) = (term157 x y).
Proof. exact (@lem1982792 (real_of_int x) (term68 x y)). Qed.
Lemma lem2429856 (x : int) (y : int) : (term158 x y) = (term159 x y).
Proof. exact (@lem1982781 (term17 x y) term97 term42). Qed.
Lemma lem2429858 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2429859 : term42 = term94.
Proof. exact (@lem2429858 term43). Qed.
Lemma lem2429861 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2429862 : term97 = term98.
Proof. exact (@lem2429861 term43). Qed.
Lemma lem2429863 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2429864 : term99 = term100.
Proof. exact (MK_COMB (@lem2429863) (@lem2429862)). Qed.
Lemma lem2429865 : term101 = term102.
Proof. exact (MK_COMB (@lem2429864) (@lem2429859)). Qed.
Lemma lem2429866 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2429868 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2429869 : term106 = term107.
Proof. exact (@lem2429868 term43 term43). Qed.
Lemma lem2429870 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429871 : term109 = term43.
Proof. exact (EQ_MP (@lem2429870) (@lem940073)). Qed.
Lemma lem2429872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429873 : term107 = term42.
Proof. exact (MK_COMB (@lem2429872) (@lem2429871)). Qed.
Lemma lem2429874 : term106 = term42.
Proof. exact (TRANS (@lem2429869) (@lem2429873)). Qed.
Lemma lem2429876 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2429877 : term101 = term112.
Proof. exact (@lem2429876 term43 term43). Qed.
Lemma lem2429878 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429879 : term109 = term43.
Proof. exact (EQ_MP (@lem2429878) (@lem940073)). Qed.
Lemma lem2429880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429881 : term107 = term42.
Proof. exact (MK_COMB (@lem2429880) (@lem2429879)). Qed.
Lemma lem2429882 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2429883 : term112 = term97.
Proof. exact (MK_COMB (@lem2429882) (@lem2429881)). Qed.
Lemma lem2429884 : term101 = term97.
Proof. exact (TRANS (@lem2429877) (@lem2429883)). Qed.
Lemma lem2429885 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2429886 : term113 = term114.
Proof. exact (MK_COMB (@lem2429885) (@lem2429884)). Qed.
Lemma lem2429887 : term103 = term98.
Proof. exact (MK_COMB (@lem2429886) (@lem2429874)). Qed.
Lemma lem2429888 : term102 = term98.
Proof. exact (TRANS (@lem2429866) (@lem2429887)). Qed.
Lemma lem2429889 : term101 = term98.
Proof. exact (TRANS (@lem2429865) (@lem2429888)). Qed.
Lemma lem2429891 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2429892 : term98 = term97.
Proof. exact (@lem2429891 term97). Qed.
Lemma lem2429893 : term101 = term97.
Proof. exact (TRANS (@lem2429889) (@lem2429892)). Qed.
Lemma lem2429896 (x : int) (y : int) : (term146 x y) = (term146 x y).
Proof. exact (eq_refl (term146 x y)). Qed.
Lemma lem2429897 (x : int) (y : int) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem2429896 x y) (@lem2429893)). Qed.
Lemma lem2429898 (x : int) (y : int) : (term158 x y) = (term160 x y).
Proof. exact (TRANS (@lem2429856 x y) (@lem2429897 x y)). Qed.
Lemma lem2429899 (x : int) : (term116 x) = (term116 x).
Proof. exact (eq_refl (term116 x)). Qed.
Lemma lem2429900 (x : int) (y : int) : (term157 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem2429899 x) (@lem2429898 x y)). Qed.
Lemma lem2429905 (y : int) (x : int) : (term161 x y) = (term147 y x).
Proof. exact (@lem1982757 (term162 x y) (real_of_int x) term97). Qed.
Lemma lem2429906 (y : int) (x : int) : (term157 x y) = (term147 y x).
Proof. exact (TRANS (@lem2429900 x y) (@lem2429905 y x)). Qed.
Lemma lem2429908 (y : int) (x : int) : (term156 x y) = (term147 y x).
Proof. exact (TRANS (@lem2429855 x y) (@lem2429906 y x)). Qed.
Lemma lem2429909 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2429910 (y : int) (x : int) : (term163 x y) = (term151 y x).
Proof. exact (MK_COMB (@lem2429909) (@lem2429908 y x)). Qed.
Lemma lem2429911 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2429912 (y : int) (x : int) : (term155 x y) = (term152 y x).
Proof. exact (MK_COMB (@lem2429910 y x) (@lem2429911)). Qed.
Lemma lem2429913 (y : int) (x : int) : (term71 y x) = (term152 y x).
Proof. exact (TRANS (@lem2429837 x y) (@lem2429912 y x)). Qed.
Lemma lem2429914 (x : int) (y : int) : (term75 x y) = (term164 x y).
Proof. exact (@lem1988287 (term47 x y) term54). Qed.
Lemma lem2429915 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2429921 (y : int) : (term45 y) = (term92 y).
Proof. exact (@lem1982792 (real_of_int y) term42). Qed.
Lemma lem2429923 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2429924 : term42 = term94.
Proof. exact (@lem2429923 term43). Qed.
Lemma lem2429926 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2429927 : term97 = term98.
Proof. exact (@lem2429926 term43). Qed.
Lemma lem2429928 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2429929 : term99 = term100.
Proof. exact (MK_COMB (@lem2429928) (@lem2429927)). Qed.
Lemma lem2429930 : term101 = term102.
Proof. exact (MK_COMB (@lem2429929) (@lem2429924)). Qed.
Lemma lem2429931 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2429933 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2429934 : term106 = term107.
Proof. exact (@lem2429933 term43 term43). Qed.
Lemma lem2429935 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429936 : term109 = term43.
Proof. exact (EQ_MP (@lem2429935) (@lem940073)). Qed.
Lemma lem2429937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429938 : term107 = term42.
Proof. exact (MK_COMB (@lem2429937) (@lem2429936)). Qed.
Lemma lem2429939 : term106 = term42.
Proof. exact (TRANS (@lem2429934) (@lem2429938)). Qed.
Lemma lem2429941 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2429942 : term101 = term112.
Proof. exact (@lem2429941 term43 term43). Qed.
Lemma lem2429943 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429944 : term109 = term43.
Proof. exact (EQ_MP (@lem2429943) (@lem940073)). Qed.
Lemma lem2429945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429946 : term107 = term42.
Proof. exact (MK_COMB (@lem2429945) (@lem2429944)). Qed.
Lemma lem2429947 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2429948 : term112 = term97.
Proof. exact (MK_COMB (@lem2429947) (@lem2429946)). Qed.
Lemma lem2429949 : term101 = term97.
Proof. exact (TRANS (@lem2429942) (@lem2429948)). Qed.
Lemma lem2429950 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2429951 : term113 = term114.
Proof. exact (MK_COMB (@lem2429950) (@lem2429949)). Qed.
Lemma lem2429952 : term103 = term98.
Proof. exact (MK_COMB (@lem2429951) (@lem2429939)). Qed.
Lemma lem2429953 : term102 = term98.
Proof. exact (TRANS (@lem2429931) (@lem2429952)). Qed.
Lemma lem2429954 : term101 = term98.
Proof. exact (TRANS (@lem2429930) (@lem2429953)). Qed.
Lemma lem2429956 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2429957 : term98 = term97.
Proof. exact (@lem2429956 term97). Qed.
Lemma lem2429958 : term101 = term97.
Proof. exact (TRANS (@lem2429954) (@lem2429957)). Qed.
Lemma lem2429959 (y : int) : (term116 y) = (term116 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem2429962 (y : int) : (term92 y) = (term117 y).
Proof. exact (MK_COMB (@lem2429959 y) (@lem2429958)). Qed.
Lemma lem2429964 (y : int) : (term45 y) = (term117 y).
Proof. exact (TRANS (@lem2429921 y) (@lem2429962 y)). Qed.
Lemma lem2429967 (x : int) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem2429968 (x : int) (y : int) : (term47 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem2429967 x) (@lem2429964 y)). Qed.
Lemma lem2429969 (y : int) (x : int) : (term118 x y) = (term119 y x).
Proof. exact (@lem1982781 (real_of_int y) (real_of_int x) term97). Qed.
Lemma lem2429970 (x : int) : (term120 x) = (term121 x).
Proof. exact (@lem1982747 term97 (real_of_int x)). Qed.
Lemma lem2429973 (x : int) (y : int) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem2429974 (y : int) (x : int) : (term119 y x) = (term87 y x).
Proof. exact (MK_COMB (@lem2429973 x y) (@lem2429970 x)). Qed.
Lemma lem2429975 (y : int) (x : int) : (term118 x y) = (term87 y x).
Proof. exact (TRANS (@lem2429969 y x) (@lem2429974 y x)). Qed.
Lemma lem2429976 (y : int) (x : int) : (term47 x y) = (term87 y x).
Proof. exact (TRANS (@lem2429968 x y) (@lem2429975 y x)). Qed.
Lemma lem2429977 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2429978 (y : int) (x : int) : (term165 x y) = (term166 y x).
Proof. exact (MK_COMB (@lem2429977) (@lem2429976 y x)). Qed.
Lemma lem2429979 (y : int) (x : int) : (term167 x y) = (term168 y x).
Proof. exact (MK_COMB (@lem2429978 y x) (@lem2429915)). Qed.
Lemma lem2429980 (y : int) (x : int) : (term168 y x) = (term169 y x).
Proof. exact (@lem1982792 (term87 y x) term54). Qed.
Lemma lem2429982 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2429983 : term54 = term170.
Proof. exact (@lem2429982 (NUMERAL 0)). Qed.
Lemma lem2429985 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2429986 : term97 = term98.
Proof. exact (@lem2429985 term43). Qed.
Lemma lem2429987 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2429988 : term99 = term100.
Proof. exact (MK_COMB (@lem2429987) (@lem2429986)). Qed.
Lemma lem2429989 : term171 = term172.
Proof. exact (MK_COMB (@lem2429988) (@lem2429983)). Qed.
Lemma lem2429990 : term172 = term173.
Proof. exact (@lem1981613 term97 term54 term42 term42). Qed.
Lemma lem2429992 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2429993 : term106 = term107.
Proof. exact (@lem2429992 term43 term43). Qed.
Lemma lem2429994 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2429995 : term109 = term43.
Proof. exact (EQ_MP (@lem2429994) (@lem940073)). Qed.
Lemma lem2429996 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2429997 : term107 = term42.
Proof. exact (MK_COMB (@lem2429996) (@lem2429995)). Qed.
Lemma lem2429998 : term106 = term42.
Proof. exact (TRANS (@lem2429993) (@lem2429997)). Qed.
Lemma lem2430000 (x : nat) : (term174 x) = term54.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2430001 : term171 = term54.
Proof. exact (@lem2430000 term43). Qed.
Lemma lem2430002 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2430003 : term175 = term176.
Proof. exact (MK_COMB (@lem2430002) (@lem2430001)). Qed.
Lemma lem2430004 : term173 = term170.
Proof. exact (MK_COMB (@lem2430003) (@lem2429998)). Qed.
Lemma lem2430005 : term172 = term170.
Proof. exact (TRANS (@lem2429990) (@lem2430004)). Qed.
Lemma lem2430006 : term171 = term170.
Proof. exact (TRANS (@lem2429989) (@lem2430005)). Qed.
Lemma lem2430008 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2430009 : term170 = term54.
Proof. exact (@lem2430008 term54). Qed.
Lemma lem2430010 : term171 = term54.
Proof. exact (TRANS (@lem2430006) (@lem2430009)). Qed.
Lemma lem2430011 (y : int) (x : int) : (term122 y x) = (term122 y x).
Proof. exact (eq_refl (term122 y x)). Qed.
Lemma lem2430012 (y : int) (x : int) : (term169 y x) = (term177 y x).
Proof. exact (MK_COMB (@lem2430011 y x) (@lem2430010)). Qed.
Lemma lem2430013 (y : int) (x : int) : (term177 y x) = (term87 y x).
Proof. exact (@lem1982723 (term87 y x)). Qed.
Lemma lem2430014 (y : int) (x : int) : (term169 y x) = (term87 y x).
Proof. exact (TRANS (@lem2430012 y x) (@lem2430013 y x)). Qed.
Lemma lem2430015 (y : int) (x : int) : (term168 y x) = (term87 y x).
Proof. exact (TRANS (@lem2429980 y x) (@lem2430014 y x)). Qed.
Lemma lem2430016 (y : int) (x : int) : (term167 x y) = (term87 y x).
Proof. exact (TRANS (@lem2429979 y x) (@lem2430015 y x)). Qed.
Lemma lem2430017 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2430018 (y : int) (x : int) : (term178 x y) = (term89 y x).
Proof. exact (MK_COMB (@lem2430017) (@lem2430016 y x)). Qed.
Lemma lem2430019 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2430020 (y : int) (x : int) : (term164 x y) = (term90 y x).
Proof. exact (MK_COMB (@lem2430018 y x) (@lem2430019)). Qed.
Lemma lem2430021 (y : int) (x : int) : (term75 x y) = (term90 y x).
Proof. exact (TRANS (@lem2429914 x y) (@lem2430020 y x)). Qed.
Lemma lem2430022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2430023 (y : int) (x : int) : (term77 y x) = (term179 y x).
Proof. exact (MK_COMB (@lem2430022) (@lem2429913 y x)). Qed.
Lemma lem2430024 (y : int) (x : int) : (term79 x y) = (term180 y x).
Proof. exact (MK_COMB (@lem2430023 y x) (@lem2430021 y x)). Qed.
Lemma lem2430025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2430026 (y : int) (x : int) : (term81 x y) = (term181 y x).
Proof. exact (MK_COMB (@lem2430025) (@lem2429836 y x)). Qed.
Lemma lem2430027 (y : int) (x : int) : (term82 x y) = (term182 y x).
Proof. exact (MK_COMB (@lem2430026 y x) (@lem2430024 y x)). Qed.
Lemma lem2430052 (y : int) (x : int) : (term84 x y) = (term182 y x).
Proof. exact (TRANS (@lem2429629 x y) (@lem2430027 y x)). Qed.
Lemma lem2430062 (y : int) (x : int) (h1 : term182 y x) : term182 y x.
Proof. exact (h1). Qed.
Lemma lem2430063 (y : int) (x : int) (h1 : term154 y x) : term154 y x.
Proof. exact (h1). Qed.
Lemma lem2430064 (y : int) (x : int) (h1 : term154 y x) : term152 y x.
Proof. exact (proj2 (@lem2430063 y x h1)). Qed.
Lemma lem2430065 (y : int) (x : int) (h1 : term154 y x) : term90 y x.
Proof. exact (proj1 (@lem2430063 y x h1)). Qed.
Lemma lem2430067 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2430068 : term183 = term184.
Proof. exact (@lem2430067 term54 term42). Qed.
Lemma lem2430070 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430071 : term42 = term94.
Proof. exact (@lem2430070 term43). Qed.
Lemma lem2430073 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430074 : term54 = term170.
Proof. exact (@lem2430073 (NUMERAL 0)). Qed.
Lemma lem2430075 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2430076 : term185 = term186.
Proof. exact (MK_COMB (@lem2430075) (@lem2430074)). Qed.
Lemma lem2430077 : term184 = term187.
Proof. exact (MK_COMB (@lem2430076) (@lem2430071)). Qed.
Lemma lem2430078 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2430080 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430081 : term184 = term190.
Proof. exact (@lem2430080 (NUMERAL 0) term43). Qed.
Lemma lem2430082 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430083 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430084 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430083 h1) (fun h1 : term190 = True => @lem2430082)). Qed.
Lemma lem2430085 : term190 = True.
Proof. exact (EQ_MP (@lem2430084) (@lem2430082)). Qed.
Lemma lem2430086 : term184 = True.
Proof. exact (TRANS (@lem2430081) (@lem2430085)). Qed.
Lemma lem2430087 : True = term184.
Proof. exact (SYM (@lem2430086)). Qed.
Lemma lem2430088 : term184.
Proof. exact (EQ_MP (@lem2430087) (@lem0)). Qed.
Lemma lem2430089 : term192.
Proof. exact (@lem2430078 (@lem2430088)). Qed.
Lemma lem2430091 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430092 : term184 = term190.
Proof. exact (@lem2430091 (NUMERAL 0) term43). Qed.
Lemma lem2430093 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430094 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430095 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430094 h1) (fun h1 : term190 = True => @lem2430093)). Qed.
Lemma lem2430096 : term190 = True.
Proof. exact (EQ_MP (@lem2430095) (@lem2430093)). Qed.
Lemma lem2430097 : term184 = True.
Proof. exact (TRANS (@lem2430092) (@lem2430096)). Qed.
Lemma lem2430098 : True = term184.
Proof. exact (SYM (@lem2430097)). Qed.
Lemma lem2430099 : term184.
Proof. exact (EQ_MP (@lem2430098) (@lem0)). Qed.
Lemma lem2430100 : term187 = term193.
Proof. exact (@lem2430089 (@lem2430099)). Qed.
Lemma lem2430102 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430103 : term106 = term107.
Proof. exact (@lem2430102 term43 term43). Qed.
Lemma lem2430104 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430105 : term109 = term43.
Proof. exact (EQ_MP (@lem2430104) (@lem940073)). Qed.
Lemma lem2430106 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430107 : term107 = term42.
Proof. exact (MK_COMB (@lem2430106) (@lem2430105)). Qed.
Lemma lem2430108 : term106 = term42.
Proof. exact (TRANS (@lem2430103) (@lem2430107)). Qed.
Lemma lem2430110 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430111 : term195 = term54.
Proof. exact (@lem2430110 term43). Qed.
Lemma lem2430112 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2430113 : term196 = term185.
Proof. exact (MK_COMB (@lem2430112) (@lem2430111)). Qed.
Lemma lem2430114 : term193 = term184.
Proof. exact (MK_COMB (@lem2430113) (@lem2430108)). Qed.
Lemma lem2430116 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430117 : term184 = term190.
Proof. exact (@lem2430116 (NUMERAL 0) term43). Qed.
Lemma lem2430118 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430119 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430120 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430119 h1) (fun h1 : term190 = True => @lem2430118)). Qed.
Lemma lem2430121 : term190 = True.
Proof. exact (EQ_MP (@lem2430120) (@lem2430118)). Qed.
Lemma lem2430122 : term184 = True.
Proof. exact (TRANS (@lem2430117) (@lem2430121)). Qed.
Lemma lem2430123 : term193 = True.
Proof. exact (TRANS (@lem2430114) (@lem2430122)). Qed.
Lemma lem2430124 : term187 = True.
Proof. exact (TRANS (@lem2430100) (@lem2430123)). Qed.
Lemma lem2430125 : term184 = True.
Proof. exact (TRANS (@lem2430077) (@lem2430124)). Qed.
Lemma lem2430126 : term183 = True.
Proof. exact (TRANS (@lem2430068) (@lem2430125)). Qed.
Lemma lem2430127 : True = term183.
Proof. exact (SYM (@lem2430126)). Qed.
Lemma lem2430128 : term183.
Proof. exact (EQ_MP (@lem2430127) (@lem0)). Qed.
Lemma lem2430129 (y : int) (x : int) (h1 : term154 y x) : term197 y x.
Proof. exact (conj (@lem2430128) (@lem2430065 y x h1)). Qed.
Lemma lem2430131 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2430132 (y : int) (x : int) : term199 y x.
Proof. exact (@lem2430131 term42 (term87 y x)). Qed.
Lemma lem2430133 (y : int) (x : int) (h1 : term154 y x) : term200 y x.
Proof. exact (@lem2430132 y x (@lem2430129 y x h1)). Qed.
Lemma lem2430134 (y : int) (x : int) : (term201 y x) = (term87 y x).
Proof. exact (@lem1982733 (term87 y x)). Qed.
Lemma lem2430135 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2430136 (y : int) (x : int) : (term202 y x) = (term89 y x).
Proof. exact (MK_COMB (@lem2430135) (@lem2430134 y x)). Qed.
Lemma lem2430137 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2430138 (y : int) (x : int) : (term200 y x) = (term90 y x).
Proof. exact (MK_COMB (@lem2430136 y x) (@lem2430137)). Qed.
Lemma lem2430139 (y : int) (x : int) (h1 : term154 y x) : term90 y x.
Proof. exact (EQ_MP (@lem2430138 y x) (@lem2430133 y x h1)). Qed.
Lemma lem2430141 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2430142 : term183 = term184.
Proof. exact (@lem2430141 term54 term42). Qed.
Lemma lem2430144 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430145 : term42 = term94.
Proof. exact (@lem2430144 term43). Qed.
Lemma lem2430147 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430148 : term54 = term170.
Proof. exact (@lem2430147 (NUMERAL 0)). Qed.
Lemma lem2430149 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2430150 : term185 = term186.
Proof. exact (MK_COMB (@lem2430149) (@lem2430148)). Qed.
Lemma lem2430151 : term184 = term187.
Proof. exact (MK_COMB (@lem2430150) (@lem2430145)). Qed.
Lemma lem2430152 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2430154 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430155 : term184 = term190.
Proof. exact (@lem2430154 (NUMERAL 0) term43). Qed.
Lemma lem2430156 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430157 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430158 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430157 h1) (fun h1 : term190 = True => @lem2430156)). Qed.
Lemma lem2430159 : term190 = True.
Proof. exact (EQ_MP (@lem2430158) (@lem2430156)). Qed.
Lemma lem2430160 : term184 = True.
Proof. exact (TRANS (@lem2430155) (@lem2430159)). Qed.
Lemma lem2430161 : True = term184.
Proof. exact (SYM (@lem2430160)). Qed.
Lemma lem2430162 : term184.
Proof. exact (EQ_MP (@lem2430161) (@lem0)). Qed.
Lemma lem2430163 : term192.
Proof. exact (@lem2430152 (@lem2430162)). Qed.
Lemma lem2430165 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430166 : term184 = term190.
Proof. exact (@lem2430165 (NUMERAL 0) term43). Qed.
Lemma lem2430167 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430168 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430169 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430168 h1) (fun h1 : term190 = True => @lem2430167)). Qed.
Lemma lem2430170 : term190 = True.
Proof. exact (EQ_MP (@lem2430169) (@lem2430167)). Qed.
Lemma lem2430171 : term184 = True.
Proof. exact (TRANS (@lem2430166) (@lem2430170)). Qed.
Lemma lem2430172 : True = term184.
Proof. exact (SYM (@lem2430171)). Qed.
Lemma lem2430173 : term184.
Proof. exact (EQ_MP (@lem2430172) (@lem0)). Qed.
Lemma lem2430174 : term187 = term193.
Proof. exact (@lem2430163 (@lem2430173)). Qed.
Lemma lem2430176 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430177 : term106 = term107.
Proof. exact (@lem2430176 term43 term43). Qed.
Lemma lem2430178 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430179 : term109 = term43.
Proof. exact (EQ_MP (@lem2430178) (@lem940073)). Qed.
Lemma lem2430180 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430181 : term107 = term42.
Proof. exact (MK_COMB (@lem2430180) (@lem2430179)). Qed.
Lemma lem2430182 : term106 = term42.
Proof. exact (TRANS (@lem2430177) (@lem2430181)). Qed.
Lemma lem2430184 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430185 : term195 = term54.
Proof. exact (@lem2430184 term43). Qed.
Lemma lem2430186 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2430187 : term196 = term185.
Proof. exact (MK_COMB (@lem2430186) (@lem2430185)). Qed.
Lemma lem2430188 : term193 = term184.
Proof. exact (MK_COMB (@lem2430187) (@lem2430182)). Qed.
Lemma lem2430190 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430191 : term184 = term190.
Proof. exact (@lem2430190 (NUMERAL 0) term43). Qed.
Lemma lem2430192 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430193 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430194 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430193 h1) (fun h1 : term190 = True => @lem2430192)). Qed.
Lemma lem2430195 : term190 = True.
Proof. exact (EQ_MP (@lem2430194) (@lem2430192)). Qed.
Lemma lem2430196 : term184 = True.
Proof. exact (TRANS (@lem2430191) (@lem2430195)). Qed.
Lemma lem2430197 : term193 = True.
Proof. exact (TRANS (@lem2430188) (@lem2430196)). Qed.
Lemma lem2430198 : term187 = True.
Proof. exact (TRANS (@lem2430174) (@lem2430197)). Qed.
Lemma lem2430199 : term184 = True.
Proof. exact (TRANS (@lem2430151) (@lem2430198)). Qed.
Lemma lem2430200 : term183 = True.
Proof. exact (TRANS (@lem2430142) (@lem2430199)). Qed.
Lemma lem2430201 : True = term183.
Proof. exact (SYM (@lem2430200)). Qed.
Lemma lem2430202 : term183.
Proof. exact (EQ_MP (@lem2430201) (@lem0)). Qed.
Lemma lem2430203 (y : int) (x : int) (h1 : term154 y x) : term203 y x.
Proof. exact (conj (@lem2430202) (@lem2430064 y x h1)). Qed.
Lemma lem2430205 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2430206 (y : int) (x : int) : term204 y x.
Proof. exact (@lem2430205 term42 (term147 y x)). Qed.
Lemma lem2430207 (y : int) (x : int) (h1 : term154 y x) : term205 y x.
Proof. exact (@lem2430206 y x (@lem2430203 y x h1)). Qed.
Lemma lem2430208 (y : int) (x : int) : (term206 y x) = (term147 y x).
Proof. exact (@lem1982733 (term147 y x)). Qed.
Lemma lem2430209 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2430210 (y : int) (x : int) : (term207 y x) = (term151 y x).
Proof. exact (MK_COMB (@lem2430209) (@lem2430208 y x)). Qed.
Lemma lem2430211 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2430212 (y : int) (x : int) : (term205 y x) = (term152 y x).
Proof. exact (MK_COMB (@lem2430210 y x) (@lem2430211)). Qed.
Lemma lem2430213 (y : int) (x : int) (h1 : term154 y x) : term152 y x.
Proof. exact (EQ_MP (@lem2430212 y x) (@lem2430207 y x h1)). Qed.
Lemma lem2430214 (y : int) (x : int) (h1 : term154 y x) : term180 y x.
Proof. exact (conj (@lem2430213 y x h1) (@lem2430139 y x h1)). Qed.
Lemma lem2430216 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2430217 (y : int) (x : int) : term209 y x.
Proof. exact (@lem2430216 (term147 y x) (term87 y x)). Qed.
Lemma lem2430218 (y : int) (x : int) (h1 : term154 y x) : term210 y x.
Proof. exact (@lem2430217 y x (@lem2430214 y x h1)). Qed.
Lemma lem2430219 (y : int) (x : int) : (term211 y x) = (term212 y x).
Proof. exact (@lem1982753 (term162 x y) (term17 x y) (term117 x) (term121 x)). Qed.
Lemma lem2430220 (x : int) (y : int) : (term213 x y) = (term214 x y).
Proof. exact (@lem1982713 term97 (term17 x y)). Qed.
Lemma lem2430222 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430223 : term42 = term94.
Proof. exact (@lem2430222 term43). Qed.
Lemma lem2430225 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2430226 : term97 = term98.
Proof. exact (@lem2430225 term43). Qed.
Lemma lem2430227 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430228 : term215 = term216.
Proof. exact (MK_COMB (@lem2430227) (@lem2430226)). Qed.
Lemma lem2430229 : term217 = term218.
Proof. exact (MK_COMB (@lem2430228) (@lem2430223)). Qed.
Lemma lem2430230 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2430232 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430233 : term184 = term190.
Proof. exact (@lem2430232 (NUMERAL 0) term43). Qed.
Lemma lem2430234 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430235 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430236 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430235 h1) (fun h1 : term190 = True => @lem2430234)). Qed.
Lemma lem2430237 : term190 = True.
Proof. exact (EQ_MP (@lem2430236) (@lem2430234)). Qed.
Lemma lem2430238 : term184 = True.
Proof. exact (TRANS (@lem2430233) (@lem2430237)). Qed.
Lemma lem2430239 : True = term184.
Proof. exact (SYM (@lem2430238)). Qed.
Lemma lem2430240 : term184.
Proof. exact (EQ_MP (@lem2430239) (@lem0)). Qed.
Lemma lem2430241 : term220.
Proof. exact (@lem2430230 (@lem2430240)). Qed.
Lemma lem2430243 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430244 : term184 = term190.
Proof. exact (@lem2430243 (NUMERAL 0) term43). Qed.
Lemma lem2430245 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430246 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430247 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430246 h1) (fun h1 : term190 = True => @lem2430245)). Qed.
Lemma lem2430248 : term190 = True.
Proof. exact (EQ_MP (@lem2430247) (@lem2430245)). Qed.
Lemma lem2430249 : term184 = True.
Proof. exact (TRANS (@lem2430244) (@lem2430248)). Qed.
Lemma lem2430250 : True = term184.
Proof. exact (SYM (@lem2430249)). Qed.
Lemma lem2430251 : term184.
Proof. exact (EQ_MP (@lem2430250) (@lem0)). Qed.
Lemma lem2430252 : term221.
Proof. exact (@lem2430241 (@lem2430251)). Qed.
Lemma lem2430254 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430255 : term184 = term190.
Proof. exact (@lem2430254 (NUMERAL 0) term43). Qed.
Lemma lem2430256 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430257 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430258 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430257 h1) (fun h1 : term190 = True => @lem2430256)). Qed.
Lemma lem2430259 : term190 = True.
Proof. exact (EQ_MP (@lem2430258) (@lem2430256)). Qed.
Lemma lem2430260 : term184 = True.
Proof. exact (TRANS (@lem2430255) (@lem2430259)). Qed.
Lemma lem2430261 : True = term184.
Proof. exact (SYM (@lem2430260)). Qed.
Lemma lem2430262 : term184.
Proof. exact (EQ_MP (@lem2430261) (@lem0)). Qed.
Lemma lem2430263 : term222.
Proof. exact (@lem2430252 (@lem2430262)). Qed.
Lemma lem2430265 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430266 : term106 = term107.
Proof. exact (@lem2430265 term43 term43). Qed.
Lemma lem2430267 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430268 : term109 = term43.
Proof. exact (EQ_MP (@lem2430267) (@lem940073)). Qed.
Lemma lem2430269 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430270 : term107 = term42.
Proof. exact (MK_COMB (@lem2430269) (@lem2430268)). Qed.
Lemma lem2430271 : term106 = term42.
Proof. exact (TRANS (@lem2430266) (@lem2430270)). Qed.
Lemma lem2430273 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2430274 : term101 = term112.
Proof. exact (@lem2430273 term43 term43). Qed.
Lemma lem2430275 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430276 : term109 = term43.
Proof. exact (EQ_MP (@lem2430275) (@lem940073)). Qed.
Lemma lem2430277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430278 : term107 = term42.
Proof. exact (MK_COMB (@lem2430277) (@lem2430276)). Qed.
Lemma lem2430279 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2430280 : term112 = term97.
Proof. exact (MK_COMB (@lem2430279) (@lem2430278)). Qed.
Lemma lem2430281 : term101 = term97.
Proof. exact (TRANS (@lem2430274) (@lem2430280)). Qed.
Lemma lem2430282 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430283 : term223 = term215.
Proof. exact (MK_COMB (@lem2430282) (@lem2430281)). Qed.
Lemma lem2430284 : term224 = term217.
Proof. exact (MK_COMB (@lem2430283) (@lem2430271)). Qed.
Lemma lem2430286 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2430287 : term217 = term54.
Proof. exact (@lem2430286 term43). Qed.
Lemma lem2430288 : term224 = term54.
Proof. exact (TRANS (@lem2430284) (@lem2430287)). Qed.
Lemma lem2430289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2430290 : term226 = term227.
Proof. exact (MK_COMB (@lem2430289) (@lem2430288)). Qed.
Lemma lem2430291 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2430292 : term228 = term195.
Proof. exact (MK_COMB (@lem2430290) (@lem2430291)). Qed.
Lemma lem2430294 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430295 : term195 = term54.
Proof. exact (@lem2430294 term43). Qed.
Lemma lem2430296 : term228 = term54.
Proof. exact (TRANS (@lem2430292) (@lem2430295)). Qed.
Lemma lem2430298 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430299 : term106 = term107.
Proof. exact (@lem2430298 term43 term43). Qed.
Lemma lem2430300 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430301 : term109 = term43.
Proof. exact (EQ_MP (@lem2430300) (@lem940073)). Qed.
Lemma lem2430302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430303 : term107 = term42.
Proof. exact (MK_COMB (@lem2430302) (@lem2430301)). Qed.
Lemma lem2430304 : term106 = term42.
Proof. exact (TRANS (@lem2430299) (@lem2430303)). Qed.
Lemma lem2430305 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2430306 : term229 = term195.
Proof. exact (MK_COMB (@lem2430305) (@lem2430304)). Qed.
Lemma lem2430308 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430309 : term195 = term54.
Proof. exact (@lem2430308 term43). Qed.
Lemma lem2430310 : term229 = term54.
Proof. exact (TRANS (@lem2430306) (@lem2430309)). Qed.
Lemma lem2430311 : term54 = term229.
Proof. exact (SYM (@lem2430310)). Qed.
Lemma lem2430312 : term228 = term229.
Proof. exact (TRANS (@lem2430296) (@lem2430311)). Qed.
Lemma lem2430313 : term218 = term170.
Proof. exact (@lem2430263 (@lem2430312)). Qed.
Lemma lem2430314 : term217 = term170.
Proof. exact (TRANS (@lem2430229) (@lem2430313)). Qed.
Lemma lem2430316 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2430317 : term170 = term54.
Proof. exact (@lem2430316 term54). Qed.
Lemma lem2430318 : term217 = term54.
Proof. exact (TRANS (@lem2430314) (@lem2430317)). Qed.
Lemma lem2430319 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2430320 : term230 = term227.
Proof. exact (MK_COMB (@lem2430319) (@lem2430318)). Qed.
Lemma lem2430321 (x : int) (y : int) : (term17 x y) = (term17 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem2430322 (x : int) (y : int) : (term214 x y) = (term231 x y).
Proof. exact (MK_COMB (@lem2430320) (@lem2430321 x y)). Qed.
Lemma lem2430323 (x : int) (y : int) : (term213 x y) = (term231 x y).
Proof. exact (TRANS (@lem2430220 x y) (@lem2430322 x y)). Qed.
Lemma lem2430324 (x : int) (y : int) : (term231 x y) = term54.
Proof. exact (@lem1982719 (term17 x y)). Qed.
Lemma lem2430325 (x : int) (y : int) : (term213 x y) = term54.
Proof. exact (TRANS (@lem2430323 x y) (@lem2430324 x y)). Qed.
Lemma lem2430326 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430327 (x : int) (y : int) : (term232 x y) = term148.
Proof. exact (MK_COMB (@lem2430326) (@lem2430325 x y)). Qed.
Lemma lem2430328 (x : int) : (term233 x) = (term234 x).
Proof. exact (@lem1982759 (real_of_int x) (term121 x) term97). Qed.
Lemma lem2430329 (x : int) : (term235 x) = (term236 x).
Proof. exact (@lem1982715 term97 (real_of_int x)). Qed.
Lemma lem2430331 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430332 : term42 = term94.
Proof. exact (@lem2430331 term43). Qed.
Lemma lem2430334 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2430335 : term97 = term98.
Proof. exact (@lem2430334 term43). Qed.
Lemma lem2430336 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430337 : term215 = term216.
Proof. exact (MK_COMB (@lem2430336) (@lem2430335)). Qed.
Lemma lem2430338 : term217 = term218.
Proof. exact (MK_COMB (@lem2430337) (@lem2430332)). Qed.
Lemma lem2430339 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2430341 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430342 : term184 = term190.
Proof. exact (@lem2430341 (NUMERAL 0) term43). Qed.
Lemma lem2430343 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430344 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430345 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430344 h1) (fun h1 : term190 = True => @lem2430343)). Qed.
Lemma lem2430346 : term190 = True.
Proof. exact (EQ_MP (@lem2430345) (@lem2430343)). Qed.
Lemma lem2430347 : term184 = True.
Proof. exact (TRANS (@lem2430342) (@lem2430346)). Qed.
Lemma lem2430348 : True = term184.
Proof. exact (SYM (@lem2430347)). Qed.
Lemma lem2430349 : term184.
Proof. exact (EQ_MP (@lem2430348) (@lem0)). Qed.
Lemma lem2430350 : term220.
Proof. exact (@lem2430339 (@lem2430349)). Qed.
Lemma lem2430352 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430353 : term184 = term190.
Proof. exact (@lem2430352 (NUMERAL 0) term43). Qed.
Lemma lem2430354 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430355 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430356 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430355 h1) (fun h1 : term190 = True => @lem2430354)). Qed.
Lemma lem2430357 : term190 = True.
Proof. exact (EQ_MP (@lem2430356) (@lem2430354)). Qed.
Lemma lem2430358 : term184 = True.
Proof. exact (TRANS (@lem2430353) (@lem2430357)). Qed.
Lemma lem2430359 : True = term184.
Proof. exact (SYM (@lem2430358)). Qed.
Lemma lem2430360 : term184.
Proof. exact (EQ_MP (@lem2430359) (@lem0)). Qed.
Lemma lem2430361 : term221.
Proof. exact (@lem2430350 (@lem2430360)). Qed.
Lemma lem2430363 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430364 : term184 = term190.
Proof. exact (@lem2430363 (NUMERAL 0) term43). Qed.
Lemma lem2430365 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430366 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430367 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430366 h1) (fun h1 : term190 = True => @lem2430365)). Qed.
Lemma lem2430368 : term190 = True.
Proof. exact (EQ_MP (@lem2430367) (@lem2430365)). Qed.
Lemma lem2430369 : term184 = True.
Proof. exact (TRANS (@lem2430364) (@lem2430368)). Qed.
Lemma lem2430370 : True = term184.
Proof. exact (SYM (@lem2430369)). Qed.
Lemma lem2430371 : term184.
Proof. exact (EQ_MP (@lem2430370) (@lem0)). Qed.
Lemma lem2430372 : term222.
Proof. exact (@lem2430361 (@lem2430371)). Qed.
Lemma lem2430374 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430375 : term106 = term107.
Proof. exact (@lem2430374 term43 term43). Qed.
Lemma lem2430376 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430377 : term109 = term43.
Proof. exact (EQ_MP (@lem2430376) (@lem940073)). Qed.
Lemma lem2430378 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430379 : term107 = term42.
Proof. exact (MK_COMB (@lem2430378) (@lem2430377)). Qed.
Lemma lem2430380 : term106 = term42.
Proof. exact (TRANS (@lem2430375) (@lem2430379)). Qed.
Lemma lem2430382 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2430383 : term101 = term112.
Proof. exact (@lem2430382 term43 term43). Qed.
Lemma lem2430384 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430385 : term109 = term43.
Proof. exact (EQ_MP (@lem2430384) (@lem940073)). Qed.
Lemma lem2430386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430387 : term107 = term42.
Proof. exact (MK_COMB (@lem2430386) (@lem2430385)). Qed.
Lemma lem2430388 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2430389 : term112 = term97.
Proof. exact (MK_COMB (@lem2430388) (@lem2430387)). Qed.
Lemma lem2430390 : term101 = term97.
Proof. exact (TRANS (@lem2430383) (@lem2430389)). Qed.
Lemma lem2430391 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430392 : term223 = term215.
Proof. exact (MK_COMB (@lem2430391) (@lem2430390)). Qed.
Lemma lem2430393 : term224 = term217.
Proof. exact (MK_COMB (@lem2430392) (@lem2430380)). Qed.
Lemma lem2430395 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2430396 : term217 = term54.
Proof. exact (@lem2430395 term43). Qed.
Lemma lem2430397 : term224 = term54.
Proof. exact (TRANS (@lem2430393) (@lem2430396)). Qed.
Lemma lem2430398 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2430399 : term226 = term227.
Proof. exact (MK_COMB (@lem2430398) (@lem2430397)). Qed.
Lemma lem2430400 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2430401 : term228 = term195.
Proof. exact (MK_COMB (@lem2430399) (@lem2430400)). Qed.
Lemma lem2430403 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430404 : term195 = term54.
Proof. exact (@lem2430403 term43). Qed.
Lemma lem2430405 : term228 = term54.
Proof. exact (TRANS (@lem2430401) (@lem2430404)). Qed.
Lemma lem2430407 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430408 : term106 = term107.
Proof. exact (@lem2430407 term43 term43). Qed.
Lemma lem2430409 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430410 : term109 = term43.
Proof. exact (EQ_MP (@lem2430409) (@lem940073)). Qed.
Lemma lem2430411 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430412 : term107 = term42.
Proof. exact (MK_COMB (@lem2430411) (@lem2430410)). Qed.
Lemma lem2430413 : term106 = term42.
Proof. exact (TRANS (@lem2430408) (@lem2430412)). Qed.
Lemma lem2430414 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2430415 : term229 = term195.
Proof. exact (MK_COMB (@lem2430414) (@lem2430413)). Qed.
Lemma lem2430417 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430418 : term195 = term54.
Proof. exact (@lem2430417 term43). Qed.
Lemma lem2430419 : term229 = term54.
Proof. exact (TRANS (@lem2430415) (@lem2430418)). Qed.
Lemma lem2430420 : term54 = term229.
Proof. exact (SYM (@lem2430419)). Qed.
Lemma lem2430421 : term228 = term229.
Proof. exact (TRANS (@lem2430405) (@lem2430420)). Qed.
Lemma lem2430422 : term218 = term170.
Proof. exact (@lem2430372 (@lem2430421)). Qed.
Lemma lem2430423 : term217 = term170.
Proof. exact (TRANS (@lem2430338) (@lem2430422)). Qed.
Lemma lem2430425 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2430426 : term170 = term54.
Proof. exact (@lem2430425 term54). Qed.
Lemma lem2430427 : term217 = term54.
Proof. exact (TRANS (@lem2430423) (@lem2430426)). Qed.
Lemma lem2430428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2430429 : term230 = term227.
Proof. exact (MK_COMB (@lem2430428) (@lem2430427)). Qed.
Lemma lem2430430 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2430431 (x : int) : (term236 x) = (term237 x).
Proof. exact (MK_COMB (@lem2430429) (@lem2430430 x)). Qed.
Lemma lem2430432 (x : int) : (term235 x) = (term237 x).
Proof. exact (TRANS (@lem2430329 x) (@lem2430431 x)). Qed.
Lemma lem2430433 (x : int) : (term237 x) = term54.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2430434 (x : int) : (term235 x) = term54.
Proof. exact (TRANS (@lem2430432 x) (@lem2430433 x)). Qed.
Lemma lem2430435 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430436 (x : int) : (term238 x) = term148.
Proof. exact (MK_COMB (@lem2430435) (@lem2430434 x)). Qed.
Lemma lem2430437 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem2430438 (x : int) : (term234 x) = term239.
Proof. exact (MK_COMB (@lem2430436 x) (@lem2430437)). Qed.
Lemma lem2430439 (x : int) : (term233 x) = term239.
Proof. exact (TRANS (@lem2430328 x) (@lem2430438 x)). Qed.
Lemma lem2430440 : term239 = term97.
Proof. exact (@lem1982721 term97). Qed.
Lemma lem2430441 (x : int) : (term233 x) = term97.
Proof. exact (TRANS (@lem2430439 x) (@lem2430440)). Qed.
Lemma lem2430442 (y : int) (x : int) : (term212 y x) = term239.
Proof. exact (MK_COMB (@lem2430327 x y) (@lem2430441 x)). Qed.
Lemma lem2430443 (y : int) (x : int) : (term211 y x) = term239.
Proof. exact (TRANS (@lem2430219 y x) (@lem2430442 y x)). Qed.
Lemma lem2430444 : term239 = term97.
Proof. exact (@lem1982721 term97). Qed.
Lemma lem2430445 (y : int) (x : int) : (term211 y x) = term97.
Proof. exact (TRANS (@lem2430443 y x) (@lem2430444)). Qed.
Lemma lem2430446 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2430447 (y : int) (x : int) : (term240 y x) = term241.
Proof. exact (MK_COMB (@lem2430446) (@lem2430445 y x)). Qed.
Lemma lem2430448 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2430449 (y : int) (x : int) : (term210 y x) = term242.
Proof. exact (MK_COMB (@lem2430447 y x) (@lem2430448)). Qed.
Lemma lem2430450 (y : int) (x : int) (h1 : term154 y x) : term242.
Proof. exact (EQ_MP (@lem2430449 y x) (@lem2430218 y x h1)). Qed.
Lemma lem2430452 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2430453 : term242 = term243.
Proof. exact (@lem2430452 term54 term97). Qed.
Lemma lem2430455 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2430456 : term97 = term98.
Proof. exact (@lem2430455 term43). Qed.
Lemma lem2430458 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430459 : term54 = term170.
Proof. exact (@lem2430458 (NUMERAL 0)). Qed.
Lemma lem2430460 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2430461 : term74 = term244.
Proof. exact (MK_COMB (@lem2430460) (@lem2430459)). Qed.
Lemma lem2430462 : term243 = term245.
Proof. exact (MK_COMB (@lem2430461) (@lem2430456)). Qed.
Lemma lem2430463 : term246.
Proof. exact (@lem1980026 term54 term42 term97 term42). Qed.
Lemma lem2430465 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430466 : term184 = term190.
Proof. exact (@lem2430465 (NUMERAL 0) term43). Qed.
Lemma lem2430467 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430468 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430469 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430468 h1) (fun h1 : term190 = True => @lem2430467)). Qed.
Lemma lem2430470 : term190 = True.
Proof. exact (EQ_MP (@lem2430469) (@lem2430467)). Qed.
Lemma lem2430471 : term184 = True.
Proof. exact (TRANS (@lem2430466) (@lem2430470)). Qed.
Lemma lem2430472 : True = term184.
Proof. exact (SYM (@lem2430471)). Qed.
Lemma lem2430473 : term184.
Proof. exact (EQ_MP (@lem2430472) (@lem0)). Qed.
Lemma lem2430474 : term247.
Proof. exact (@lem2430463 (@lem2430473)). Qed.
Lemma lem2430476 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430477 : term184 = term190.
Proof. exact (@lem2430476 (NUMERAL 0) term43). Qed.
Lemma lem2430478 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430479 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430480 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430479 h1) (fun h1 : term190 = True => @lem2430478)). Qed.
Lemma lem2430481 : term190 = True.
Proof. exact (EQ_MP (@lem2430480) (@lem2430478)). Qed.
Lemma lem2430482 : term184 = True.
Proof. exact (TRANS (@lem2430477) (@lem2430481)). Qed.
Lemma lem2430483 : True = term184.
Proof. exact (SYM (@lem2430482)). Qed.
Lemma lem2430484 : term184.
Proof. exact (EQ_MP (@lem2430483) (@lem0)). Qed.
Lemma lem2430485 : term245 = term248.
Proof. exact (@lem2430474 (@lem2430484)). Qed.
Lemma lem2430487 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2430488 : term101 = term112.
Proof. exact (@lem2430487 term43 term43). Qed.
Lemma lem2430489 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430490 : term109 = term43.
Proof. exact (EQ_MP (@lem2430489) (@lem940073)). Qed.
Lemma lem2430491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430492 : term107 = term42.
Proof. exact (MK_COMB (@lem2430491) (@lem2430490)). Qed.
Lemma lem2430493 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2430494 : term112 = term97.
Proof. exact (MK_COMB (@lem2430493) (@lem2430492)). Qed.
Lemma lem2430495 : term101 = term97.
Proof. exact (TRANS (@lem2430488) (@lem2430494)). Qed.
Lemma lem2430497 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430498 : term195 = term54.
Proof. exact (@lem2430497 term43). Qed.
Lemma lem2430499 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2430500 : term249 = term74.
Proof. exact (MK_COMB (@lem2430499) (@lem2430498)). Qed.
Lemma lem2430501 : term248 = term243.
Proof. exact (MK_COMB (@lem2430500) (@lem2430495)). Qed.
Lemma lem2430503 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2430504 : term243 = term252.
Proof. exact (@lem2430503 (NUMERAL 0) term43). Qed.
Lemma lem2430505 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430506 (h1 : term191 = (BIT1 0)) : (term43 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2430507 : (term191 = (BIT1 0)) = ((term43 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430506 h1) (fun h1 : (term43 = (NUMERAL 0)) = False => @lem2430505)). Qed.
Lemma lem2430508 : (term43 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2430507) (@lem2430505)). Qed.
Lemma lem2430509 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2430510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2430511 : term253 = (and True).
Proof. exact (MK_COMB (@lem2430510) (@lem2430509)). Qed.
Lemma lem2430512 : term252 = (True /\ False).
Proof. exact (MK_COMB (@lem2430511) (@lem2430508)). Qed.
Lemma lem2430514 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2430515 : term252 = False.
Proof. exact (TRANS (@lem2430512) (@lem2430514)). Qed.
Lemma lem2430516 : term243 = False.
Proof. exact (TRANS (@lem2430504) (@lem2430515)). Qed.
Lemma lem2430517 : term248 = False.
Proof. exact (TRANS (@lem2430501) (@lem2430516)). Qed.
Lemma lem2430518 : term245 = False.
Proof. exact (TRANS (@lem2430485) (@lem2430517)). Qed.
Lemma lem2430519 : term243 = False.
Proof. exact (TRANS (@lem2430462) (@lem2430518)). Qed.
Lemma lem2430520 : term242 = False.
Proof. exact (TRANS (@lem2430453) (@lem2430519)). Qed.
Lemma lem2430521 (y : int) (x : int) (h1 : term154 y x) : False.
Proof. exact (EQ_MP (@lem2430520) (@lem2430450 y x h1)). Qed.
Lemma lem2430522 (y : int) (x : int) (h1 : term180 y x) : term180 y x.
Proof. exact (h1). Qed.
Lemma lem2430523 (y : int) (x : int) (h1 : term180 y x) : term90 y x.
Proof. exact (proj2 (@lem2430522 y x h1)). Qed.
Lemma lem2430524 (y : int) (x : int) (h1 : term180 y x) : term152 y x.
Proof. exact (proj1 (@lem2430522 y x h1)). Qed.
Lemma lem2430526 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2430527 : term183 = term184.
Proof. exact (@lem2430526 term54 term42). Qed.
Lemma lem2430529 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430530 : term42 = term94.
Proof. exact (@lem2430529 term43). Qed.
Lemma lem2430532 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430533 : term54 = term170.
Proof. exact (@lem2430532 (NUMERAL 0)). Qed.
Lemma lem2430534 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2430535 : term185 = term186.
Proof. exact (MK_COMB (@lem2430534) (@lem2430533)). Qed.
Lemma lem2430536 : term184 = term187.
Proof. exact (MK_COMB (@lem2430535) (@lem2430530)). Qed.
Lemma lem2430537 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2430539 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430540 : term184 = term190.
Proof. exact (@lem2430539 (NUMERAL 0) term43). Qed.
Lemma lem2430541 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430542 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430543 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430542 h1) (fun h1 : term190 = True => @lem2430541)). Qed.
Lemma lem2430544 : term190 = True.
Proof. exact (EQ_MP (@lem2430543) (@lem2430541)). Qed.
Lemma lem2430545 : term184 = True.
Proof. exact (TRANS (@lem2430540) (@lem2430544)). Qed.
Lemma lem2430546 : True = term184.
Proof. exact (SYM (@lem2430545)). Qed.
Lemma lem2430547 : term184.
Proof. exact (EQ_MP (@lem2430546) (@lem0)). Qed.
Lemma lem2430548 : term192.
Proof. exact (@lem2430537 (@lem2430547)). Qed.
Lemma lem2430550 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430551 : term184 = term190.
Proof. exact (@lem2430550 (NUMERAL 0) term43). Qed.
Lemma lem2430552 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430553 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430554 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430553 h1) (fun h1 : term190 = True => @lem2430552)). Qed.
Lemma lem2430555 : term190 = True.
Proof. exact (EQ_MP (@lem2430554) (@lem2430552)). Qed.
Lemma lem2430556 : term184 = True.
Proof. exact (TRANS (@lem2430551) (@lem2430555)). Qed.
Lemma lem2430557 : True = term184.
Proof. exact (SYM (@lem2430556)). Qed.
Lemma lem2430558 : term184.
Proof. exact (EQ_MP (@lem2430557) (@lem0)). Qed.
Lemma lem2430559 : term187 = term193.
Proof. exact (@lem2430548 (@lem2430558)). Qed.
Lemma lem2430561 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430562 : term106 = term107.
Proof. exact (@lem2430561 term43 term43). Qed.
Lemma lem2430563 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430564 : term109 = term43.
Proof. exact (EQ_MP (@lem2430563) (@lem940073)). Qed.
Lemma lem2430565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430566 : term107 = term42.
Proof. exact (MK_COMB (@lem2430565) (@lem2430564)). Qed.
Lemma lem2430567 : term106 = term42.
Proof. exact (TRANS (@lem2430562) (@lem2430566)). Qed.
Lemma lem2430569 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430570 : term195 = term54.
Proof. exact (@lem2430569 term43). Qed.
Lemma lem2430571 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2430572 : term196 = term185.
Proof. exact (MK_COMB (@lem2430571) (@lem2430570)). Qed.
Lemma lem2430573 : term193 = term184.
Proof. exact (MK_COMB (@lem2430572) (@lem2430567)). Qed.
Lemma lem2430575 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430576 : term184 = term190.
Proof. exact (@lem2430575 (NUMERAL 0) term43). Qed.
Lemma lem2430577 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430578 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430579 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430578 h1) (fun h1 : term190 = True => @lem2430577)). Qed.
Lemma lem2430580 : term190 = True.
Proof. exact (EQ_MP (@lem2430579) (@lem2430577)). Qed.
Lemma lem2430581 : term184 = True.
Proof. exact (TRANS (@lem2430576) (@lem2430580)). Qed.
Lemma lem2430582 : term193 = True.
Proof. exact (TRANS (@lem2430573) (@lem2430581)). Qed.
Lemma lem2430583 : term187 = True.
Proof. exact (TRANS (@lem2430559) (@lem2430582)). Qed.
Lemma lem2430584 : term184 = True.
Proof. exact (TRANS (@lem2430536) (@lem2430583)). Qed.
Lemma lem2430585 : term183 = True.
Proof. exact (TRANS (@lem2430527) (@lem2430584)). Qed.
Lemma lem2430586 : True = term183.
Proof. exact (SYM (@lem2430585)). Qed.
Lemma lem2430587 : term183.
Proof. exact (EQ_MP (@lem2430586) (@lem0)). Qed.
Lemma lem2430588 (y : int) (x : int) (h1 : term180 y x) : term197 y x.
Proof. exact (conj (@lem2430587) (@lem2430523 y x h1)). Qed.
Lemma lem2430590 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2430591 (y : int) (x : int) : term199 y x.
Proof. exact (@lem2430590 term42 (term87 y x)). Qed.
Lemma lem2430592 (y : int) (x : int) (h1 : term180 y x) : term200 y x.
Proof. exact (@lem2430591 y x (@lem2430588 y x h1)). Qed.
Lemma lem2430593 (y : int) (x : int) : (term201 y x) = (term87 y x).
Proof. exact (@lem1982733 (term87 y x)). Qed.
Lemma lem2430594 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2430595 (y : int) (x : int) : (term202 y x) = (term89 y x).
Proof. exact (MK_COMB (@lem2430594) (@lem2430593 y x)). Qed.
Lemma lem2430596 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2430597 (y : int) (x : int) : (term200 y x) = (term90 y x).
Proof. exact (MK_COMB (@lem2430595 y x) (@lem2430596)). Qed.
Lemma lem2430598 (y : int) (x : int) (h1 : term180 y x) : term90 y x.
Proof. exact (EQ_MP (@lem2430597 y x) (@lem2430592 y x h1)). Qed.
Lemma lem2430600 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2430601 : term183 = term184.
Proof. exact (@lem2430600 term54 term42). Qed.
Lemma lem2430603 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430604 : term42 = term94.
Proof. exact (@lem2430603 term43). Qed.
Lemma lem2430606 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430607 : term54 = term170.
Proof. exact (@lem2430606 (NUMERAL 0)). Qed.
Lemma lem2430608 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2430609 : term185 = term186.
Proof. exact (MK_COMB (@lem2430608) (@lem2430607)). Qed.
Lemma lem2430610 : term184 = term187.
Proof. exact (MK_COMB (@lem2430609) (@lem2430604)). Qed.
Lemma lem2430611 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2430613 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430614 : term184 = term190.
Proof. exact (@lem2430613 (NUMERAL 0) term43). Qed.
Lemma lem2430615 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430616 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430617 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430616 h1) (fun h1 : term190 = True => @lem2430615)). Qed.
Lemma lem2430618 : term190 = True.
Proof. exact (EQ_MP (@lem2430617) (@lem2430615)). Qed.
Lemma lem2430619 : term184 = True.
Proof. exact (TRANS (@lem2430614) (@lem2430618)). Qed.
Lemma lem2430620 : True = term184.
Proof. exact (SYM (@lem2430619)). Qed.
Lemma lem2430621 : term184.
Proof. exact (EQ_MP (@lem2430620) (@lem0)). Qed.
Lemma lem2430622 : term192.
Proof. exact (@lem2430611 (@lem2430621)). Qed.
Lemma lem2430624 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430625 : term184 = term190.
Proof. exact (@lem2430624 (NUMERAL 0) term43). Qed.
Lemma lem2430626 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430627 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430628 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430627 h1) (fun h1 : term190 = True => @lem2430626)). Qed.
Lemma lem2430629 : term190 = True.
Proof. exact (EQ_MP (@lem2430628) (@lem2430626)). Qed.
Lemma lem2430630 : term184 = True.
Proof. exact (TRANS (@lem2430625) (@lem2430629)). Qed.
Lemma lem2430631 : True = term184.
Proof. exact (SYM (@lem2430630)). Qed.
Lemma lem2430632 : term184.
Proof. exact (EQ_MP (@lem2430631) (@lem0)). Qed.
Lemma lem2430633 : term187 = term193.
Proof. exact (@lem2430622 (@lem2430632)). Qed.
Lemma lem2430635 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430636 : term106 = term107.
Proof. exact (@lem2430635 term43 term43). Qed.
Lemma lem2430637 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430638 : term109 = term43.
Proof. exact (EQ_MP (@lem2430637) (@lem940073)). Qed.
Lemma lem2430639 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430640 : term107 = term42.
Proof. exact (MK_COMB (@lem2430639) (@lem2430638)). Qed.
Lemma lem2430641 : term106 = term42.
Proof. exact (TRANS (@lem2430636) (@lem2430640)). Qed.
Lemma lem2430643 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430644 : term195 = term54.
Proof. exact (@lem2430643 term43). Qed.
Lemma lem2430645 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2430646 : term196 = term185.
Proof. exact (MK_COMB (@lem2430645) (@lem2430644)). Qed.
Lemma lem2430647 : term193 = term184.
Proof. exact (MK_COMB (@lem2430646) (@lem2430641)). Qed.
Lemma lem2430649 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430650 : term184 = term190.
Proof. exact (@lem2430649 (NUMERAL 0) term43). Qed.
Lemma lem2430651 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430652 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430653 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430652 h1) (fun h1 : term190 = True => @lem2430651)). Qed.
Lemma lem2430654 : term190 = True.
Proof. exact (EQ_MP (@lem2430653) (@lem2430651)). Qed.
Lemma lem2430655 : term184 = True.
Proof. exact (TRANS (@lem2430650) (@lem2430654)). Qed.
Lemma lem2430656 : term193 = True.
Proof. exact (TRANS (@lem2430647) (@lem2430655)). Qed.
Lemma lem2430657 : term187 = True.
Proof. exact (TRANS (@lem2430633) (@lem2430656)). Qed.
Lemma lem2430658 : term184 = True.
Proof. exact (TRANS (@lem2430610) (@lem2430657)). Qed.
Lemma lem2430659 : term183 = True.
Proof. exact (TRANS (@lem2430601) (@lem2430658)). Qed.
Lemma lem2430660 : True = term183.
Proof. exact (SYM (@lem2430659)). Qed.
Lemma lem2430661 : term183.
Proof. exact (EQ_MP (@lem2430660) (@lem0)). Qed.
Lemma lem2430662 (y : int) (x : int) (h1 : term180 y x) : term203 y x.
Proof. exact (conj (@lem2430661) (@lem2430524 y x h1)). Qed.
Lemma lem2430664 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2430665 (y : int) (x : int) : term204 y x.
Proof. exact (@lem2430664 term42 (term147 y x)). Qed.
Lemma lem2430666 (y : int) (x : int) (h1 : term180 y x) : term205 y x.
Proof. exact (@lem2430665 y x (@lem2430662 y x h1)). Qed.
Lemma lem2430667 (y : int) (x : int) : (term206 y x) = (term147 y x).
Proof. exact (@lem1982733 (term147 y x)). Qed.
Lemma lem2430668 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2430669 (y : int) (x : int) : (term207 y x) = (term151 y x).
Proof. exact (MK_COMB (@lem2430668) (@lem2430667 y x)). Qed.
Lemma lem2430670 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2430671 (y : int) (x : int) : (term205 y x) = (term152 y x).
Proof. exact (MK_COMB (@lem2430669 y x) (@lem2430670)). Qed.
Lemma lem2430672 (y : int) (x : int) (h1 : term180 y x) : term152 y x.
Proof. exact (EQ_MP (@lem2430671 y x) (@lem2430666 y x h1)). Qed.
Lemma lem2430673 (y : int) (x : int) (h1 : term180 y x) : term180 y x.
Proof. exact (conj (@lem2430672 y x h1) (@lem2430598 y x h1)). Qed.
Lemma lem2430675 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2430676 (y : int) (x : int) : term209 y x.
Proof. exact (@lem2430675 (term147 y x) (term87 y x)). Qed.
Lemma lem2430677 (y : int) (x : int) (h1 : term180 y x) : term210 y x.
Proof. exact (@lem2430676 y x (@lem2430673 y x h1)). Qed.
Lemma lem2430678 (y : int) (x : int) : (term211 y x) = (term212 y x).
Proof. exact (@lem1982753 (term162 x y) (term17 x y) (term117 x) (term121 x)). Qed.
Lemma lem2430679 (x : int) (y : int) : (term213 x y) = (term214 x y).
Proof. exact (@lem1982713 term97 (term17 x y)). Qed.
Lemma lem2430681 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430682 : term42 = term94.
Proof. exact (@lem2430681 term43). Qed.
Lemma lem2430684 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2430685 : term97 = term98.
Proof. exact (@lem2430684 term43). Qed.
Lemma lem2430686 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430687 : term215 = term216.
Proof. exact (MK_COMB (@lem2430686) (@lem2430685)). Qed.
Lemma lem2430688 : term217 = term218.
Proof. exact (MK_COMB (@lem2430687) (@lem2430682)). Qed.
Lemma lem2430689 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2430691 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430692 : term184 = term190.
Proof. exact (@lem2430691 (NUMERAL 0) term43). Qed.
Lemma lem2430693 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430694 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430695 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430694 h1) (fun h1 : term190 = True => @lem2430693)). Qed.
Lemma lem2430696 : term190 = True.
Proof. exact (EQ_MP (@lem2430695) (@lem2430693)). Qed.
Lemma lem2430697 : term184 = True.
Proof. exact (TRANS (@lem2430692) (@lem2430696)). Qed.
Lemma lem2430698 : True = term184.
Proof. exact (SYM (@lem2430697)). Qed.
Lemma lem2430699 : term184.
Proof. exact (EQ_MP (@lem2430698) (@lem0)). Qed.
Lemma lem2430700 : term220.
Proof. exact (@lem2430689 (@lem2430699)). Qed.
Lemma lem2430702 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430703 : term184 = term190.
Proof. exact (@lem2430702 (NUMERAL 0) term43). Qed.
Lemma lem2430704 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430705 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430706 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430705 h1) (fun h1 : term190 = True => @lem2430704)). Qed.
Lemma lem2430707 : term190 = True.
Proof. exact (EQ_MP (@lem2430706) (@lem2430704)). Qed.
Lemma lem2430708 : term184 = True.
Proof. exact (TRANS (@lem2430703) (@lem2430707)). Qed.
Lemma lem2430709 : True = term184.
Proof. exact (SYM (@lem2430708)). Qed.
Lemma lem2430710 : term184.
Proof. exact (EQ_MP (@lem2430709) (@lem0)). Qed.
Lemma lem2430711 : term221.
Proof. exact (@lem2430700 (@lem2430710)). Qed.
Lemma lem2430713 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430714 : term184 = term190.
Proof. exact (@lem2430713 (NUMERAL 0) term43). Qed.
Lemma lem2430715 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430716 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430717 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430716 h1) (fun h1 : term190 = True => @lem2430715)). Qed.
Lemma lem2430718 : term190 = True.
Proof. exact (EQ_MP (@lem2430717) (@lem2430715)). Qed.
Lemma lem2430719 : term184 = True.
Proof. exact (TRANS (@lem2430714) (@lem2430718)). Qed.
Lemma lem2430720 : True = term184.
Proof. exact (SYM (@lem2430719)). Qed.
Lemma lem2430721 : term184.
Proof. exact (EQ_MP (@lem2430720) (@lem0)). Qed.
Lemma lem2430722 : term222.
Proof. exact (@lem2430711 (@lem2430721)). Qed.
Lemma lem2430724 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430725 : term106 = term107.
Proof. exact (@lem2430724 term43 term43). Qed.
Lemma lem2430726 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430727 : term109 = term43.
Proof. exact (EQ_MP (@lem2430726) (@lem940073)). Qed.
Lemma lem2430728 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430729 : term107 = term42.
Proof. exact (MK_COMB (@lem2430728) (@lem2430727)). Qed.
Lemma lem2430730 : term106 = term42.
Proof. exact (TRANS (@lem2430725) (@lem2430729)). Qed.
Lemma lem2430732 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2430733 : term101 = term112.
Proof. exact (@lem2430732 term43 term43). Qed.
Lemma lem2430734 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430735 : term109 = term43.
Proof. exact (EQ_MP (@lem2430734) (@lem940073)). Qed.
Lemma lem2430736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430737 : term107 = term42.
Proof. exact (MK_COMB (@lem2430736) (@lem2430735)). Qed.
Lemma lem2430738 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2430739 : term112 = term97.
Proof. exact (MK_COMB (@lem2430738) (@lem2430737)). Qed.
Lemma lem2430740 : term101 = term97.
Proof. exact (TRANS (@lem2430733) (@lem2430739)). Qed.
Lemma lem2430741 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430742 : term223 = term215.
Proof. exact (MK_COMB (@lem2430741) (@lem2430740)). Qed.
Lemma lem2430743 : term224 = term217.
Proof. exact (MK_COMB (@lem2430742) (@lem2430730)). Qed.
Lemma lem2430745 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2430746 : term217 = term54.
Proof. exact (@lem2430745 term43). Qed.
Lemma lem2430747 : term224 = term54.
Proof. exact (TRANS (@lem2430743) (@lem2430746)). Qed.
Lemma lem2430748 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2430749 : term226 = term227.
Proof. exact (MK_COMB (@lem2430748) (@lem2430747)). Qed.
Lemma lem2430750 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2430751 : term228 = term195.
Proof. exact (MK_COMB (@lem2430749) (@lem2430750)). Qed.
Lemma lem2430753 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430754 : term195 = term54.
Proof. exact (@lem2430753 term43). Qed.
Lemma lem2430755 : term228 = term54.
Proof. exact (TRANS (@lem2430751) (@lem2430754)). Qed.
Lemma lem2430757 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430758 : term106 = term107.
Proof. exact (@lem2430757 term43 term43). Qed.
Lemma lem2430759 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430760 : term109 = term43.
Proof. exact (EQ_MP (@lem2430759) (@lem940073)). Qed.
Lemma lem2430761 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430762 : term107 = term42.
Proof. exact (MK_COMB (@lem2430761) (@lem2430760)). Qed.
Lemma lem2430763 : term106 = term42.
Proof. exact (TRANS (@lem2430758) (@lem2430762)). Qed.
Lemma lem2430764 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2430765 : term229 = term195.
Proof. exact (MK_COMB (@lem2430764) (@lem2430763)). Qed.
Lemma lem2430767 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430768 : term195 = term54.
Proof. exact (@lem2430767 term43). Qed.
Lemma lem2430769 : term229 = term54.
Proof. exact (TRANS (@lem2430765) (@lem2430768)). Qed.
Lemma lem2430770 : term54 = term229.
Proof. exact (SYM (@lem2430769)). Qed.
Lemma lem2430771 : term228 = term229.
Proof. exact (TRANS (@lem2430755) (@lem2430770)). Qed.
Lemma lem2430772 : term218 = term170.
Proof. exact (@lem2430722 (@lem2430771)). Qed.
Lemma lem2430773 : term217 = term170.
Proof. exact (TRANS (@lem2430688) (@lem2430772)). Qed.
Lemma lem2430775 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2430776 : term170 = term54.
Proof. exact (@lem2430775 term54). Qed.
Lemma lem2430777 : term217 = term54.
Proof. exact (TRANS (@lem2430773) (@lem2430776)). Qed.
Lemma lem2430778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2430779 : term230 = term227.
Proof. exact (MK_COMB (@lem2430778) (@lem2430777)). Qed.
Lemma lem2430780 (x : int) (y : int) : (term17 x y) = (term17 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem2430781 (x : int) (y : int) : (term214 x y) = (term231 x y).
Proof. exact (MK_COMB (@lem2430779) (@lem2430780 x y)). Qed.
Lemma lem2430782 (x : int) (y : int) : (term213 x y) = (term231 x y).
Proof. exact (TRANS (@lem2430679 x y) (@lem2430781 x y)). Qed.
Lemma lem2430783 (x : int) (y : int) : (term231 x y) = term54.
Proof. exact (@lem1982719 (term17 x y)). Qed.
Lemma lem2430784 (x : int) (y : int) : (term213 x y) = term54.
Proof. exact (TRANS (@lem2430782 x y) (@lem2430783 x y)). Qed.
Lemma lem2430785 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430786 (x : int) (y : int) : (term232 x y) = term148.
Proof. exact (MK_COMB (@lem2430785) (@lem2430784 x y)). Qed.
Lemma lem2430787 (x : int) : (term233 x) = (term234 x).
Proof. exact (@lem1982759 (real_of_int x) (term121 x) term97). Qed.
Lemma lem2430788 (x : int) : (term235 x) = (term236 x).
Proof. exact (@lem1982715 term97 (real_of_int x)). Qed.
Lemma lem2430790 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430791 : term42 = term94.
Proof. exact (@lem2430790 term43). Qed.
Lemma lem2430793 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2430794 : term97 = term98.
Proof. exact (@lem2430793 term43). Qed.
Lemma lem2430795 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430796 : term215 = term216.
Proof. exact (MK_COMB (@lem2430795) (@lem2430794)). Qed.
Lemma lem2430797 : term217 = term218.
Proof. exact (MK_COMB (@lem2430796) (@lem2430791)). Qed.
Lemma lem2430798 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2430800 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430801 : term184 = term190.
Proof. exact (@lem2430800 (NUMERAL 0) term43). Qed.
Lemma lem2430802 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430803 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430804 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430803 h1) (fun h1 : term190 = True => @lem2430802)). Qed.
Lemma lem2430805 : term190 = True.
Proof. exact (EQ_MP (@lem2430804) (@lem2430802)). Qed.
Lemma lem2430806 : term184 = True.
Proof. exact (TRANS (@lem2430801) (@lem2430805)). Qed.
Lemma lem2430807 : True = term184.
Proof. exact (SYM (@lem2430806)). Qed.
Lemma lem2430808 : term184.
Proof. exact (EQ_MP (@lem2430807) (@lem0)). Qed.
Lemma lem2430809 : term220.
Proof. exact (@lem2430798 (@lem2430808)). Qed.
Lemma lem2430811 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430812 : term184 = term190.
Proof. exact (@lem2430811 (NUMERAL 0) term43). Qed.
Lemma lem2430813 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430814 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430815 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430814 h1) (fun h1 : term190 = True => @lem2430813)). Qed.
Lemma lem2430816 : term190 = True.
Proof. exact (EQ_MP (@lem2430815) (@lem2430813)). Qed.
Lemma lem2430817 : term184 = True.
Proof. exact (TRANS (@lem2430812) (@lem2430816)). Qed.
Lemma lem2430818 : True = term184.
Proof. exact (SYM (@lem2430817)). Qed.
Lemma lem2430819 : term184.
Proof. exact (EQ_MP (@lem2430818) (@lem0)). Qed.
Lemma lem2430820 : term221.
Proof. exact (@lem2430809 (@lem2430819)). Qed.
Lemma lem2430822 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430823 : term184 = term190.
Proof. exact (@lem2430822 (NUMERAL 0) term43). Qed.
Lemma lem2430824 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430825 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430826 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430825 h1) (fun h1 : term190 = True => @lem2430824)). Qed.
Lemma lem2430827 : term190 = True.
Proof. exact (EQ_MP (@lem2430826) (@lem2430824)). Qed.
Lemma lem2430828 : term184 = True.
Proof. exact (TRANS (@lem2430823) (@lem2430827)). Qed.
Lemma lem2430829 : True = term184.
Proof. exact (SYM (@lem2430828)). Qed.
Lemma lem2430830 : term184.
Proof. exact (EQ_MP (@lem2430829) (@lem0)). Qed.
Lemma lem2430831 : term222.
Proof. exact (@lem2430820 (@lem2430830)). Qed.
Lemma lem2430833 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430834 : term106 = term107.
Proof. exact (@lem2430833 term43 term43). Qed.
Lemma lem2430835 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430836 : term109 = term43.
Proof. exact (EQ_MP (@lem2430835) (@lem940073)). Qed.
Lemma lem2430837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430838 : term107 = term42.
Proof. exact (MK_COMB (@lem2430837) (@lem2430836)). Qed.
Lemma lem2430839 : term106 = term42.
Proof. exact (TRANS (@lem2430834) (@lem2430838)). Qed.
Lemma lem2430841 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2430842 : term101 = term112.
Proof. exact (@lem2430841 term43 term43). Qed.
Lemma lem2430843 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430844 : term109 = term43.
Proof. exact (EQ_MP (@lem2430843) (@lem940073)). Qed.
Lemma lem2430845 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430846 : term107 = term42.
Proof. exact (MK_COMB (@lem2430845) (@lem2430844)). Qed.
Lemma lem2430847 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2430848 : term112 = term97.
Proof. exact (MK_COMB (@lem2430847) (@lem2430846)). Qed.
Lemma lem2430849 : term101 = term97.
Proof. exact (TRANS (@lem2430842) (@lem2430848)). Qed.
Lemma lem2430850 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430851 : term223 = term215.
Proof. exact (MK_COMB (@lem2430850) (@lem2430849)). Qed.
Lemma lem2430852 : term224 = term217.
Proof. exact (MK_COMB (@lem2430851) (@lem2430839)). Qed.
Lemma lem2430854 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2430855 : term217 = term54.
Proof. exact (@lem2430854 term43). Qed.
Lemma lem2430856 : term224 = term54.
Proof. exact (TRANS (@lem2430852) (@lem2430855)). Qed.
Lemma lem2430857 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2430858 : term226 = term227.
Proof. exact (MK_COMB (@lem2430857) (@lem2430856)). Qed.
Lemma lem2430859 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2430860 : term228 = term195.
Proof. exact (MK_COMB (@lem2430858) (@lem2430859)). Qed.
Lemma lem2430862 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430863 : term195 = term54.
Proof. exact (@lem2430862 term43). Qed.
Lemma lem2430864 : term228 = term54.
Proof. exact (TRANS (@lem2430860) (@lem2430863)). Qed.
Lemma lem2430866 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2430867 : term106 = term107.
Proof. exact (@lem2430866 term43 term43). Qed.
Lemma lem2430868 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430869 : term109 = term43.
Proof. exact (EQ_MP (@lem2430868) (@lem940073)). Qed.
Lemma lem2430870 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430871 : term107 = term42.
Proof. exact (MK_COMB (@lem2430870) (@lem2430869)). Qed.
Lemma lem2430872 : term106 = term42.
Proof. exact (TRANS (@lem2430867) (@lem2430871)). Qed.
Lemma lem2430873 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2430874 : term229 = term195.
Proof. exact (MK_COMB (@lem2430873) (@lem2430872)). Qed.
Lemma lem2430876 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430877 : term195 = term54.
Proof. exact (@lem2430876 term43). Qed.
Lemma lem2430878 : term229 = term54.
Proof. exact (TRANS (@lem2430874) (@lem2430877)). Qed.
Lemma lem2430879 : term54 = term229.
Proof. exact (SYM (@lem2430878)). Qed.
Lemma lem2430880 : term228 = term229.
Proof. exact (TRANS (@lem2430864) (@lem2430879)). Qed.
Lemma lem2430881 : term218 = term170.
Proof. exact (@lem2430831 (@lem2430880)). Qed.
Lemma lem2430882 : term217 = term170.
Proof. exact (TRANS (@lem2430797) (@lem2430881)). Qed.
Lemma lem2430884 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2430885 : term170 = term54.
Proof. exact (@lem2430884 term54). Qed.
Lemma lem2430886 : term217 = term54.
Proof. exact (TRANS (@lem2430882) (@lem2430885)). Qed.
Lemma lem2430887 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2430888 : term230 = term227.
Proof. exact (MK_COMB (@lem2430887) (@lem2430886)). Qed.
Lemma lem2430889 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2430890 (x : int) : (term236 x) = (term237 x).
Proof. exact (MK_COMB (@lem2430888) (@lem2430889 x)). Qed.
Lemma lem2430891 (x : int) : (term235 x) = (term237 x).
Proof. exact (TRANS (@lem2430788 x) (@lem2430890 x)). Qed.
Lemma lem2430892 (x : int) : (term237 x) = term54.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2430893 (x : int) : (term235 x) = term54.
Proof. exact (TRANS (@lem2430891 x) (@lem2430892 x)). Qed.
Lemma lem2430894 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2430895 (x : int) : (term238 x) = term148.
Proof. exact (MK_COMB (@lem2430894) (@lem2430893 x)). Qed.
Lemma lem2430896 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem2430897 (x : int) : (term234 x) = term239.
Proof. exact (MK_COMB (@lem2430895 x) (@lem2430896)). Qed.
Lemma lem2430898 (x : int) : (term233 x) = term239.
Proof. exact (TRANS (@lem2430787 x) (@lem2430897 x)). Qed.
Lemma lem2430899 : term239 = term97.
Proof. exact (@lem1982721 term97). Qed.
Lemma lem2430900 (x : int) : (term233 x) = term97.
Proof. exact (TRANS (@lem2430898 x) (@lem2430899)). Qed.
Lemma lem2430901 (y : int) (x : int) : (term212 y x) = term239.
Proof. exact (MK_COMB (@lem2430786 x y) (@lem2430900 x)). Qed.
Lemma lem2430902 (y : int) (x : int) : (term211 y x) = term239.
Proof. exact (TRANS (@lem2430678 y x) (@lem2430901 y x)). Qed.
Lemma lem2430903 : term239 = term97.
Proof. exact (@lem1982721 term97). Qed.
Lemma lem2430904 (y : int) (x : int) : (term211 y x) = term97.
Proof. exact (TRANS (@lem2430902 y x) (@lem2430903)). Qed.
Lemma lem2430905 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2430906 (y : int) (x : int) : (term240 y x) = term241.
Proof. exact (MK_COMB (@lem2430905) (@lem2430904 y x)). Qed.
Lemma lem2430907 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2430908 (y : int) (x : int) : (term210 y x) = term242.
Proof. exact (MK_COMB (@lem2430906 y x) (@lem2430907)). Qed.
Lemma lem2430909 (y : int) (x : int) (h1 : term180 y x) : term242.
Proof. exact (EQ_MP (@lem2430908 y x) (@lem2430677 y x h1)). Qed.
Lemma lem2430911 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2430912 : term242 = term243.
Proof. exact (@lem2430911 term54 term97). Qed.
Lemma lem2430914 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2430915 : term97 = term98.
Proof. exact (@lem2430914 term43). Qed.
Lemma lem2430917 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2430918 : term54 = term170.
Proof. exact (@lem2430917 (NUMERAL 0)). Qed.
Lemma lem2430919 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2430920 : term74 = term244.
Proof. exact (MK_COMB (@lem2430919) (@lem2430918)). Qed.
Lemma lem2430921 : term243 = term245.
Proof. exact (MK_COMB (@lem2430920) (@lem2430915)). Qed.
Lemma lem2430922 : term246.
Proof. exact (@lem1980026 term54 term42 term97 term42). Qed.
Lemma lem2430924 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430925 : term184 = term190.
Proof. exact (@lem2430924 (NUMERAL 0) term43). Qed.
Lemma lem2430926 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430927 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430928 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430927 h1) (fun h1 : term190 = True => @lem2430926)). Qed.
Lemma lem2430929 : term190 = True.
Proof. exact (EQ_MP (@lem2430928) (@lem2430926)). Qed.
Lemma lem2430930 : term184 = True.
Proof. exact (TRANS (@lem2430925) (@lem2430929)). Qed.
Lemma lem2430931 : True = term184.
Proof. exact (SYM (@lem2430930)). Qed.
Lemma lem2430932 : term184.
Proof. exact (EQ_MP (@lem2430931) (@lem0)). Qed.
Lemma lem2430933 : term247.
Proof. exact (@lem2430922 (@lem2430932)). Qed.
Lemma lem2430935 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2430936 : term184 = term190.
Proof. exact (@lem2430935 (NUMERAL 0) term43). Qed.
Lemma lem2430937 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430938 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2430939 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430938 h1) (fun h1 : term190 = True => @lem2430937)). Qed.
Lemma lem2430940 : term190 = True.
Proof. exact (EQ_MP (@lem2430939) (@lem2430937)). Qed.
Lemma lem2430941 : term184 = True.
Proof. exact (TRANS (@lem2430936) (@lem2430940)). Qed.
Lemma lem2430942 : True = term184.
Proof. exact (SYM (@lem2430941)). Qed.
Lemma lem2430943 : term184.
Proof. exact (EQ_MP (@lem2430942) (@lem0)). Qed.
Lemma lem2430944 : term245 = term248.
Proof. exact (@lem2430933 (@lem2430943)). Qed.
Lemma lem2430946 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2430947 : term101 = term112.
Proof. exact (@lem2430946 term43 term43). Qed.
Lemma lem2430948 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2430949 : term109 = term43.
Proof. exact (EQ_MP (@lem2430948) (@lem940073)). Qed.
Lemma lem2430950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2430951 : term107 = term42.
Proof. exact (MK_COMB (@lem2430950) (@lem2430949)). Qed.
Lemma lem2430952 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2430953 : term112 = term97.
Proof. exact (MK_COMB (@lem2430952) (@lem2430951)). Qed.
Lemma lem2430954 : term101 = term97.
Proof. exact (TRANS (@lem2430947) (@lem2430953)). Qed.
Lemma lem2430956 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2430957 : term195 = term54.
Proof. exact (@lem2430956 term43). Qed.
Lemma lem2430958 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2430959 : term249 = term74.
Proof. exact (MK_COMB (@lem2430958) (@lem2430957)). Qed.
Lemma lem2430960 : term248 = term243.
Proof. exact (MK_COMB (@lem2430959) (@lem2430954)). Qed.
Lemma lem2430962 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2430963 : term243 = term252.
Proof. exact (@lem2430962 (NUMERAL 0) term43). Qed.
Lemma lem2430964 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2430965 (h1 : term191 = (BIT1 0)) : (term43 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2430966 : (term191 = (BIT1 0)) = ((term43 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2430965 h1) (fun h1 : (term43 = (NUMERAL 0)) = False => @lem2430964)). Qed.
Lemma lem2430967 : (term43 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2430966) (@lem2430964)). Qed.
Lemma lem2430968 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2430969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2430970 : term253 = (and True).
Proof. exact (MK_COMB (@lem2430969) (@lem2430968)). Qed.
Lemma lem2430971 : term252 = (True /\ False).
Proof. exact (MK_COMB (@lem2430970) (@lem2430967)). Qed.
Lemma lem2430973 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2430974 : term252 = False.
Proof. exact (TRANS (@lem2430971) (@lem2430973)). Qed.
Lemma lem2430975 : term243 = False.
Proof. exact (TRANS (@lem2430963) (@lem2430974)). Qed.
Lemma lem2430976 : term248 = False.
Proof. exact (TRANS (@lem2430960) (@lem2430975)). Qed.
Lemma lem2430977 : term245 = False.
Proof. exact (TRANS (@lem2430944) (@lem2430976)). Qed.
Lemma lem2430978 : term243 = False.
Proof. exact (TRANS (@lem2430921) (@lem2430977)). Qed.
Lemma lem2430979 : term242 = False.
Proof. exact (TRANS (@lem2430912) (@lem2430978)). Qed.
Lemma lem2430980 (y : int) (x : int) (h1 : term180 y x) : False.
Proof. exact (EQ_MP (@lem2430979) (@lem2430909 y x h1)). Qed.
Lemma lem2430981 (y : int) (x : int) (h1 : term182 y x) : False.
Proof. exact (or_elim (@lem2430062 y x h1) (fun h0 : term154 y x => @lem2430521 y x h0) (fun h0 : term180 y x => @lem2430980 y x h0)). Qed.
Lemma lem2430983 (y : int) (x : int) (h1 : term182 y x) : term182 y x.
Proof. exact (h1). Qed.
Lemma lem2430984 (y : int) (x : int) (h1 : term182 y x) : (term182 y x) = False.
Proof. exact (prop_ext (fun h2 : term182 y x => @lem2430981 y x h1) (fun h2 : False => @lem2430983 y x h1)). Qed.
Lemma lem2430985 (y : int) (x : int) (h1 : term182 y x) : False.
Proof. exact (EQ_MP (@lem2430984 y x h1) (@lem2430983 y x h1)). Qed.
Lemma lem2430986 (x : int) (y : int) (h1 : term84 x y) : term84 x y.
Proof. exact (h1). Qed.
Lemma lem2430987 (x : int) (y : int) (h1 : term84 x y) : term182 y x.
Proof. exact (EQ_MP (@lem2430052 y x) (@lem2430986 x y h1)). Qed.
Lemma lem2430988 (x : int) (y : int) (h1 : term84 x y) : (term182 y x) = False.
Proof. exact (prop_ext (fun h2 : term182 y x => @lem2430985 y x h2) (fun h2 : False => @lem2430987 x y h1)). Qed.
Lemma lem2430989 (x : int) (y : int) (h1 : term84 x y) : False.
Proof. exact (EQ_MP (@lem2430988 x y h1) (@lem2430987 x y h1)). Qed.
Lemma lem2430990 (x : int) (y : int) : term254 x y.
Proof. exact (fun h0 : term84 x y => @lem2430989 x y h0). Qed.
Lemma lem2430991 (x : int) (y : int) : term255 x y.
Proof. exact (@lem1386578 (term256 x y)). Qed.
Lemma lem2430994 (x : int) (y : int) : term256 x y.
Proof. exact (@lem2430991 x y (@lem2430990 x y)). Qed.
Lemma lem2430995 (x : int) (y : int) : (term82 x y) = (term12 x y).
Proof. exact (SYM (@lem2429589 x y)). Qed.
Lemma lem2430996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2430997 (x : int) (y : int) : (term256 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2430996) (@lem2430995 x y)). Qed.
Lemma lem2430998 (x : int) (y : int) : term9 x y.
Proof. exact (EQ_MP (@lem2430997 x y) (@lem2430994 x y)). Qed.
Lemma lem2431012 (p : Prop) : term257 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem2431013 (p : Prop) : (term257 p) = (term258 p).
Proof. exact (eq_refl (term257 p)). Qed.
Lemma lem2431014 (p : Prop) : term258 p.
Proof. exact (EQ_MP (@lem2431013 p) (@lem2431012 p)). Qed.
Lemma lem2431015 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem2431016 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem2431029 (q : Prop) (r : Prop) : (term259 q r) = (term259 q r).
Proof. exact (eq_refl (term259 q r)). Qed.
Lemma lem2431030 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term260 q r p) = (term261 q r).
Proof. exact (MK_COMB (@lem2431029 q r) (@lem2431015 p h1)). Qed.
Lemma lem2431031 (q : Prop) (r : Prop) : (term261 q r) = ((term262 q r) = (term263 q r)).
Proof. exact (eq_refl (term261 q r)). Qed.
Lemma lem2431032 (q : Prop) (r : Prop) (p : Prop) : (term264 q r p) = (term264 q r p).
Proof. exact (eq_refl (term264 q r p)). Qed.
Lemma lem2431033 (p : Prop) (q : Prop) (r : Prop) : ((term260 q r p) = (term261 q r)) = ((term260 q r p) = ((term262 q r) = (term263 q r))).
Proof. exact (MK_COMB (@lem2431032 q r p) (@lem2431031 q r)). Qed.
Lemma lem2431034 (q : Prop) (r : Prop) (p : Prop) : (term260 q r p) = ((term265 p q r) = (term266 q r p)).
Proof. exact (eq_refl (term260 q r p)). Qed.
Lemma lem2431035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431036 (q : Prop) (r : Prop) (p : Prop) : (term264 q r p) = (term267 q r p).
Proof. exact (MK_COMB (@lem2431035) (@lem2431034 q r p)). Qed.
Lemma lem2431037 (q : Prop) (r : Prop) : ((term262 q r) = (term263 q r)) = ((term262 q r) = (term263 q r)).
Proof. exact (eq_refl ((term262 q r) = (term263 q r))). Qed.
Lemma lem2431038 (p : Prop) (q : Prop) (r : Prop) : ((term260 q r p) = ((term262 q r) = (term263 q r))) = (((term265 p q r) = (term266 q r p)) = ((term262 q r) = (term263 q r))).
Proof. exact (MK_COMB (@lem2431036 q r p) (@lem2431037 q r)). Qed.
Lemma lem2431039 (p : Prop) (q : Prop) (r : Prop) : ((term260 q r p) = (term261 q r)) = (((term265 p q r) = (term266 q r p)) = ((term262 q r) = (term263 q r))).
Proof. exact (TRANS (@lem2431033 p q r) (@lem2431038 p q r)). Qed.
Lemma lem2431040 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term265 p q r) = (term266 q r p)) = ((term262 q r) = (term263 q r)).
Proof. exact (EQ_MP (@lem2431039 p q r) (@lem2431030 q r p h1)). Qed.
Lemma lem2431041 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term262 q r) = (term263 q r)) = ((term265 p q r) = (term266 q r p)).
Proof. exact (SYM (@lem2431040 q r p h1)). Qed.
Lemma lem2431042 (q : Prop) (r : Prop) : (term259 q r) = (term259 q r).
Proof. exact (eq_refl (term259 q r)). Qed.
Lemma lem2431043 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term260 q r p) = (term268 q r).
Proof. exact (MK_COMB (@lem2431042 q r) (@lem2431016 p h1)). Qed.
Lemma lem2431044 (q : Prop) (r : Prop) : (term268 q r) = ((term269 q r) = (term270 q r)).
Proof. exact (eq_refl (term268 q r)). Qed.
Lemma lem2431045 (q : Prop) (r : Prop) (p : Prop) : (term264 q r p) = (term264 q r p).
Proof. exact (eq_refl (term264 q r p)). Qed.
Lemma lem2431046 (p : Prop) (q : Prop) (r : Prop) : ((term260 q r p) = (term268 q r)) = ((term260 q r p) = ((term269 q r) = (term270 q r))).
Proof. exact (MK_COMB (@lem2431045 q r p) (@lem2431044 q r)). Qed.
Lemma lem2431047 (q : Prop) (r : Prop) (p : Prop) : (term260 q r p) = ((term265 p q r) = (term266 q r p)).
Proof. exact (eq_refl (term260 q r p)). Qed.
Lemma lem2431048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431049 (q : Prop) (r : Prop) (p : Prop) : (term264 q r p) = (term267 q r p).
Proof. exact (MK_COMB (@lem2431048) (@lem2431047 q r p)). Qed.
Lemma lem2431050 (q : Prop) (r : Prop) : ((term269 q r) = (term270 q r)) = ((term269 q r) = (term270 q r)).
Proof. exact (eq_refl ((term269 q r) = (term270 q r))). Qed.
Lemma lem2431051 (p : Prop) (q : Prop) (r : Prop) : ((term260 q r p) = ((term269 q r) = (term270 q r))) = (((term265 p q r) = (term266 q r p)) = ((term269 q r) = (term270 q r))).
Proof. exact (MK_COMB (@lem2431049 q r p) (@lem2431050 q r)). Qed.
Lemma lem2431052 (p : Prop) (q : Prop) (r : Prop) : ((term260 q r p) = (term268 q r)) = (((term265 p q r) = (term266 q r p)) = ((term269 q r) = (term270 q r))).
Proof. exact (TRANS (@lem2431046 p q r) (@lem2431051 p q r)). Qed.
Lemma lem2431053 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term265 p q r) = (term266 q r p)) = ((term269 q r) = (term270 q r)).
Proof. exact (EQ_MP (@lem2431052 p q r) (@lem2431043 q r p h1)). Qed.
Lemma lem2431054 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term269 q r) = (term270 q r)) = ((term265 p q r) = (term266 q r p)).
Proof. exact (SYM (@lem2431053 q r p h1)). Qed.
Lemma lem2431058 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2431059 (q : Prop) (r : Prop) : (term262 q r) = True.
Proof. exact (@lem2431058 (q \/ r)). Qed.
Lemma lem2431060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431061 (q : Prop) (r : Prop) : (term271 q r) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2431060) (@lem2431059 q r)). Qed.
Lemma lem2431063 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem2431064 (q : Prop) (r : Prop) : (term263 q r) = True.
Proof. exact (@lem2431063 (term272 q r)). Qed.
Lemma lem2431065 (q : Prop) (r : Prop) : ((term262 q r) = (term263 q r)) = (True = True).
Proof. exact (MK_COMB (@lem2431061 q r) (@lem2431064 q r)). Qed.
Lemma lem2431067 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2431068 : (True = True) = True.
Proof. exact (@lem2431067 True). Qed.
Lemma lem2431069 (q : Prop) (r : Prop) : ((term262 q r) = (term263 q r)) = True.
Proof. exact (TRANS (@lem2431065 q r) (@lem2431068)). Qed.
Lemma lem2431070 (q : Prop) (r : Prop) : True = ((term262 q r) = (term263 q r)).
Proof. exact (SYM (@lem2431069 q r)). Qed.
Lemma lem2431071 (q : Prop) (r : Prop) : (term262 q r) = (term263 q r).
Proof. exact (EQ_MP (@lem2431070 q r) (@lem0)). Qed.
Lemma lem2431075 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem2431076 (q : Prop) (r : Prop) : (term269 q r) = (q \/ r).
Proof. exact (@lem2431075 (q \/ r)). Qed.
Lemma lem2431079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431080 (q : Prop) (r : Prop) : (term273 q r) = (term274 q r).
Proof. exact (MK_COMB (@lem2431079) (@lem2431076 q r)). Qed.
Lemma lem2431082 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem2431083 (q : Prop) (r : Prop) : (term270 q r) = (term275 q r).
Proof. exact (@lem2431082 (term272 q r)). Qed.
Lemma lem2431086 (q : Prop) (r : Prop) : ((term269 q r) = (term270 q r)) = ((q \/ r) = (term275 q r)).
Proof. exact (MK_COMB (@lem2431080 q r) (@lem2431083 q r)). Qed.
Lemma lem2431089 (q : Prop) (r : Prop) : ((q \/ r) = (term275 q r)) = ((term269 q r) = (term270 q r)).
Proof. exact (SYM (@lem2431086 q r)). Qed.
Lemma lem2431090 (q : Prop) : term257 q.
Proof. exact (@lem9851 q). Qed.
Lemma lem2431091 (q : Prop) : (term257 q) = (term258 q).
Proof. exact (eq_refl (term257 q)). Qed.
Lemma lem2431092 (q : Prop) : term258 q.
Proof. exact (EQ_MP (@lem2431091 q) (@lem2431090 q)). Qed.
Lemma lem2431093 (q : Prop) (h1 : q = True) : q = True.
Proof. exact (h1). Qed.
Lemma lem2431094 (q : Prop) (h1 : q = False) : q = False.
Proof. exact (h1). Qed.
Lemma lem2431103 (r : Prop) : (term276 r) = (term276 r).
Proof. exact (eq_refl (term276 r)). Qed.
Lemma lem2431104 (r : Prop) (q : Prop) (h1 : q = True) : (term277 r q) = (term278 r).
Proof. exact (MK_COMB (@lem2431103 r) (@lem2431093 q h1)). Qed.
Lemma lem2431105 (r : Prop) : (term278 r) = ((True \/ r) = (term279 r)).
Proof. exact (eq_refl (term278 r)). Qed.
Lemma lem2431106 (r : Prop) (q : Prop) : (term280 r q) = (term280 r q).
Proof. exact (eq_refl (term280 r q)). Qed.
Lemma lem2431107 (q : Prop) (r : Prop) : ((term277 r q) = (term278 r)) = ((term277 r q) = ((True \/ r) = (term279 r))).
Proof. exact (MK_COMB (@lem2431106 r q) (@lem2431105 r)). Qed.
Lemma lem2431108 (q : Prop) (r : Prop) : (term277 r q) = ((q \/ r) = (term275 q r)).
Proof. exact (eq_refl (term277 r q)). Qed.
Lemma lem2431109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431110 (q : Prop) (r : Prop) : (term280 r q) = (term281 q r).
Proof. exact (MK_COMB (@lem2431109) (@lem2431108 q r)). Qed.
Lemma lem2431111 (r : Prop) : ((True \/ r) = (term279 r)) = ((True \/ r) = (term279 r)).
Proof. exact (eq_refl ((True \/ r) = (term279 r))). Qed.
Lemma lem2431112 (q : Prop) (r : Prop) : ((term277 r q) = ((True \/ r) = (term279 r))) = (((q \/ r) = (term275 q r)) = ((True \/ r) = (term279 r))).
Proof. exact (MK_COMB (@lem2431110 q r) (@lem2431111 r)). Qed.
Lemma lem2431113 (q : Prop) (r : Prop) : ((term277 r q) = (term278 r)) = (((q \/ r) = (term275 q r)) = ((True \/ r) = (term279 r))).
Proof. exact (TRANS (@lem2431107 q r) (@lem2431112 q r)). Qed.
Lemma lem2431114 (r : Prop) (q : Prop) (h1 : q = True) : ((q \/ r) = (term275 q r)) = ((True \/ r) = (term279 r)).
Proof. exact (EQ_MP (@lem2431113 q r) (@lem2431104 r q h1)). Qed.
Lemma lem2431115 (r : Prop) (q : Prop) (h1 : q = True) : ((True \/ r) = (term279 r)) = ((q \/ r) = (term275 q r)).
Proof. exact (SYM (@lem2431114 r q h1)). Qed.
Lemma lem2431116 (r : Prop) : (term276 r) = (term276 r).
Proof. exact (eq_refl (term276 r)). Qed.
Lemma lem2431117 (r : Prop) (q : Prop) (h1 : q = False) : (term277 r q) = (term282 r).
Proof. exact (MK_COMB (@lem2431116 r) (@lem2431094 q h1)). Qed.
Lemma lem2431118 (r : Prop) : (term282 r) = ((False \/ r) = (term283 r)).
Proof. exact (eq_refl (term282 r)). Qed.
Lemma lem2431119 (r : Prop) (q : Prop) : (term280 r q) = (term280 r q).
Proof. exact (eq_refl (term280 r q)). Qed.
Lemma lem2431120 (q : Prop) (r : Prop) : ((term277 r q) = (term282 r)) = ((term277 r q) = ((False \/ r) = (term283 r))).
Proof. exact (MK_COMB (@lem2431119 r q) (@lem2431118 r)). Qed.
Lemma lem2431121 (q : Prop) (r : Prop) : (term277 r q) = ((q \/ r) = (term275 q r)).
Proof. exact (eq_refl (term277 r q)). Qed.
Lemma lem2431122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431123 (q : Prop) (r : Prop) : (term280 r q) = (term281 q r).
Proof. exact (MK_COMB (@lem2431122) (@lem2431121 q r)). Qed.
Lemma lem2431124 (r : Prop) : ((False \/ r) = (term283 r)) = ((False \/ r) = (term283 r)).
Proof. exact (eq_refl ((False \/ r) = (term283 r))). Qed.
Lemma lem2431125 (q : Prop) (r : Prop) : ((term277 r q) = ((False \/ r) = (term283 r))) = (((q \/ r) = (term275 q r)) = ((False \/ r) = (term283 r))).
Proof. exact (MK_COMB (@lem2431123 q r) (@lem2431124 r)). Qed.
Lemma lem2431126 (q : Prop) (r : Prop) : ((term277 r q) = (term282 r)) = (((q \/ r) = (term275 q r)) = ((False \/ r) = (term283 r))).
Proof. exact (TRANS (@lem2431120 q r) (@lem2431125 q r)). Qed.
Lemma lem2431127 (r : Prop) (q : Prop) (h1 : q = False) : ((q \/ r) = (term275 q r)) = ((False \/ r) = (term283 r)).
Proof. exact (EQ_MP (@lem2431126 q r) (@lem2431117 r q h1)). Qed.
Lemma lem2431128 (r : Prop) (q : Prop) (h1 : q = False) : ((False \/ r) = (term283 r)) = ((q \/ r) = (term275 q r)).
Proof. exact (SYM (@lem2431127 r q h1)). Qed.
Lemma lem2431132 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2431133 (r : Prop) : (True \/ r) = True.
Proof. exact (@lem2431132 r). Qed.
Lemma lem2431134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431135 (r : Prop) : (term284 r) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2431134) (@lem2431133 r)). Qed.
Lemma lem2431139 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem2431140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2431141 : term285 = (and False).
Proof. exact (MK_COMB (@lem2431140) (@lem2431139)). Qed.
Lemma lem2431142 (r : Prop) : (~ r) = (~ r).
Proof. exact (eq_refl (~ r)). Qed.
Lemma lem2431143 (r : Prop) : (term286 r) = (term287 r).
Proof. exact (MK_COMB (@lem2431141) (@lem2431142 r)). Qed.
Lemma lem2431145 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem2431146 (r : Prop) : (term287 r) = False.
Proof. exact (@lem2431145 (~ r)). Qed.
Lemma lem2431147 (r : Prop) : (term286 r) = False.
Proof. exact (TRANS (@lem2431143 r) (@lem2431146 r)). Qed.
Lemma lem2431148 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2431149 (r : Prop) : (term279 r) = (~ False).
Proof. exact (MK_COMB (@lem2431148) (@lem2431147 r)). Qed.
Lemma lem2431151 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2431152 (r : Prop) : (term279 r) = True.
Proof. exact (TRANS (@lem2431149 r) (@lem2431151)). Qed.
Lemma lem2431153 (r : Prop) : ((True \/ r) = (term279 r)) = (True = True).
Proof. exact (MK_COMB (@lem2431135 r) (@lem2431152 r)). Qed.
Lemma lem2431155 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2431156 : (True = True) = True.
Proof. exact (@lem2431155 True). Qed.
Lemma lem2431157 (r : Prop) : ((True \/ r) = (term279 r)) = True.
Proof. exact (TRANS (@lem2431153 r) (@lem2431156)). Qed.
Lemma lem2431158 (r : Prop) : True = ((True \/ r) = (term279 r)).
Proof. exact (SYM (@lem2431157 r)). Qed.
Lemma lem2431159 (r : Prop) : (True \/ r) = (term279 r).
Proof. exact (EQ_MP (@lem2431158 r) (@lem0)). Qed.
Lemma lem2431163 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem2431164 (r : Prop) : (False \/ r) = r.
Proof. exact (@lem2431163 r). Qed.
Lemma lem2431165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431166 (r : Prop) : (term288 r) = (@eq Prop r).
Proof. exact (MK_COMB (@lem2431165) (@lem2431164 r)). Qed.
Lemma lem2431170 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2431171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2431172 : term289 = (and True).
Proof. exact (MK_COMB (@lem2431171) (@lem2431170)). Qed.
Lemma lem2431173 (r : Prop) : (~ r) = (~ r).
Proof. exact (eq_refl (~ r)). Qed.
Lemma lem2431174 (r : Prop) : (term290 r) = (term291 r).
Proof. exact (MK_COMB (@lem2431172) (@lem2431173 r)). Qed.
Lemma lem2431176 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2431177 (r : Prop) : (term291 r) = (~ r).
Proof. exact (@lem2431176 (~ r)). Qed.
Lemma lem2431178 (r : Prop) : (term290 r) = (~ r).
Proof. exact (TRANS (@lem2431174 r) (@lem2431177 r)). Qed.
Lemma lem2431179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2431180 (r : Prop) : (term283 r) = (term83 r).
Proof. exact (MK_COMB (@lem2431179) (@lem2431178 r)). Qed.
Lemma lem2431182 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem2431183 (r : Prop) : (term83 r) = r.
Proof. exact (@lem2431182 r). Qed.
Lemma lem2431184 (r : Prop) : (term283 r) = r.
Proof. exact (TRANS (@lem2431180 r) (@lem2431183 r)). Qed.
Lemma lem2431185 (r : Prop) : ((False \/ r) = (term283 r)) = (r = r).
Proof. exact (MK_COMB (@lem2431166 r) (@lem2431184 r)). Qed.
Lemma lem2431187 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2431188 (x : Prop) : (x = x) = True.
Proof. exact (@lem2431187 Prop x). Qed.
Lemma lem2431189 (r : Prop) : (r = r) = True.
Proof. exact (@lem2431188 r). Qed.
Lemma lem2431190 (r : Prop) : ((False \/ r) = (term283 r)) = True.
Proof. exact (TRANS (@lem2431185 r) (@lem2431189 r)). Qed.
Lemma lem2431191 (r : Prop) : True = ((False \/ r) = (term283 r)).
Proof. exact (SYM (@lem2431190 r)). Qed.
Lemma lem2431192 (r : Prop) : (False \/ r) = (term283 r).
Proof. exact (EQ_MP (@lem2431191 r) (@lem0)). Qed.
Lemma lem2431193 (r : Prop) (q : Prop) (h1 : q = False) : (q \/ r) = (term275 q r).
Proof. exact (EQ_MP (@lem2431128 r q h1) (@lem2431192 r)). Qed.
Lemma lem2431194 (r : Prop) (q : Prop) (h1 : q = True) : (q \/ r) = (term275 q r).
Proof. exact (EQ_MP (@lem2431115 r q h1) (@lem2431159 r)). Qed.
Lemma lem2431196 (q : Prop) (r : Prop) : (q \/ r) = (term275 q r).
Proof. exact (or_elim (@lem2431092 q) (fun h0 : q = True => @lem2431194 r q h0) (fun h0 : q = False => @lem2431193 r q h0)). Qed.
Lemma lem2431197 (q : Prop) (r : Prop) : (term269 q r) = (term270 q r).
Proof. exact (EQ_MP (@lem2431089 q r) (@lem2431196 q r)). Qed.
Lemma lem2431198 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term265 p q r) = (term266 q r p).
Proof. exact (EQ_MP (@lem2431054 q r p h1) (@lem2431197 q r)). Qed.
Lemma lem2431199 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term265 p q r) = (term266 q r p).
Proof. exact (EQ_MP (@lem2431041 q r p h1) (@lem2431071 q r)). Qed.
Lemma lem2431203 (x : int) : term292 x.
Proof. exact (@lem2301483 x). Qed.
Lemma lem2431204 (x : int) : (term292 x) = (term293 x).
Proof. exact (eq_refl (term292 x)). Qed.
Lemma lem2431205 (x : int) : term293 x.
Proof. exact (EQ_MP (@lem2431204 x) (@lem2431203 x)). Qed.
Lemma lem2431206 (x : int) (y : int) : term294 x y.
Proof. exact (@lem2431205 x y). Qed.
Lemma lem2431207 (x : int) (y : int) : (term294 x y) = (((int_mul x y) = term25) = (term295 x y)).
Proof. exact (eq_refl (term294 x y)). Qed.
Lemma lem2431209 (x : int) : term296 x.
Proof. exact (@lem2300430 x). Qed.
Lemma lem2431210 (x : int) : (term296 x) = (term297 x).
Proof. exact (eq_refl (term296 x)). Qed.
Lemma lem2431211 (x : int) : term297 x.
Proof. exact (EQ_MP (@lem2431210 x) (@lem2431209 x)). Qed.
Lemma lem2431212 (x : int) (y : int) : term298 x y.
Proof. exact (@lem2431211 x y). Qed.
Lemma lem2431213 (x : int) (y : int) : (term298 x y) = ((term299 x y) = (term300 x y)).
Proof. exact (eq_refl (term298 x y)). Qed.
Lemma lem2431215 {A : Type'} (P : A -> Prop) : term301 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem2431216 {A : Type'} (P : A -> Prop) : (term301 A P) = (term302 A P).
Proof. exact (eq_refl (term301 A P)). Qed.
Lemma lem2431217 {A : Type'} (P : A -> Prop) : term302 A P.
Proof. exact (EQ_MP (@lem2431216 A P) (@lem2431215 A P)). Qed.
Lemma lem2431218 {A : Type'} (P : A -> Prop) (Q : Prop) : term303 A P Q.
Proof. exact (@lem2431217 A P Q). Qed.
Lemma lem2431219 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = ((term304 A P Q) = (term305 A P Q)).
Proof. exact (eq_refl (term303 A P Q)). Qed.
Lemma lem2431221 (b : int) : term306 b.
Proof. exact (@lem2429416 b). Qed.
Lemma lem2431222 (b : int) : (term306 b) = (term307 b).
Proof. exact (eq_refl (term306 b)). Qed.
Lemma lem2431223 (b : int) : term307 b.
Proof. exact (EQ_MP (@lem2431222 b) (@lem2431221 b)). Qed.
Lemma lem2431224 (b : int) (a : int) : term308 b a.
Proof. exact (@lem2431223 b a). Qed.
Lemma lem2431225 (b : int) (a : int) : (term308 b a) = ((int_divides a b) = (term309 b a)).
Proof. exact (eq_refl (term308 b a)). Qed.
Lemma lem2431238 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term310 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2431239 (p : Prop) (q : Prop) (p' : Prop) : term311 p q p'.
Proof. exact (fun q' : Prop => @lem2431238 p q p' q'). Qed.
Lemma lem2431240 (p : Prop) (q : Prop) : term312 p q.
Proof. exact (fun p' : Prop => @lem2431239 p q p'). Qed.
Lemma lem2431241 (x : int) (y : int) : term313 x y.
Proof. exact (@lem2431240 (int_divides x y) (term314 x y)). Qed.
Lemma lem2431242 (x : int) (y : int) (p' : Prop) : term315 x y p'.
Proof. exact (@lem2431241 x y p'). Qed.
Lemma lem2431243 (x : int) (y : int) (p' : Prop) : (term315 x y p') = (term316 x y p').
Proof. exact (eq_refl (term315 x y p')). Qed.
Lemma lem2431244 (x : int) (y : int) (p' : Prop) : term316 x y p'.
Proof. exact (EQ_MP (@lem2431243 x y p') (@lem2431242 x y p')). Qed.
Lemma lem2431245 (x : int) (y : int) (p' : Prop) (q' : Prop) : term317 x y p' q'.
Proof. exact (@lem2431244 x y p' q'). Qed.
Lemma lem2431246 (x : int) (y : int) (p' : Prop) (q' : Prop) : (term317 x y p' q') = (term318 x y p' q').
Proof. exact (eq_refl (term317 x y p' q')). Qed.
Lemma lem2431247 (x : int) (y : int) (p' : Prop) (q' : Prop) : term318 x y p' q'.
Proof. exact (EQ_MP (@lem2431246 x y p' q') (@lem2431245 x y p' q')). Qed.
Lemma lem2431249 (b : int) (a : int) : (int_divides a b) = (term309 b a).
Proof. exact (EQ_MP (@lem2431225 b a) (@lem2431224 b a)). Qed.
Lemma lem2431250 (y : int) (x : int) : (int_divides x y) = (term309 y x).
Proof. exact (@lem2431249 y x). Qed.
Lemma lem2431257 (y : int) (x : int) (q' : Prop) : term319 y x q'.
Proof. exact (@lem2431247 x y (term309 y x) q'). Qed.
Lemma lem2431258 (y : int) (x : int) (q' : Prop) : term320 y x q'.
Proof. exact (@lem2431257 y x q' (@lem2431250 y x)). Qed.
Lemma lem2431266 (x : int) (y : int) : (term314 x y) = (term314 x y).
Proof. exact (eq_refl (term314 x y)). Qed.
Lemma lem2431267 (x : int) (y : int) : term321 x y.
Proof. exact (fun h0 : term309 y x => @lem2431266 x y). Qed.
Lemma lem2431268 (x : int) (y : int) : term322 x y.
Proof. exact (@lem2431258 y x (term314 x y)). Qed.
Lemma lem2431269 (x : int) (y : int) : (term323 x y) = (term324 x y).
Proof. exact (@lem2431268 x y (@lem2431267 x y)). Qed.
Lemma lem2431271 {A : Type'} (P : A -> Prop) (Q : Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (EQ_MP (@lem2431219 A P Q) (@lem2431218 A P Q)). Qed.
Lemma lem2431272 (P : int -> Prop) (Q : Prop) : (term325 P Q) = (term326 P Q).
Proof. exact (@lem2431271 int P Q). Qed.
Lemma lem2431273 (x : int) (y : int) : (term327 x y) = (term328 x y).
Proof. exact (@lem2431272 (term329 y x) (term314 x y)). Qed.
Lemma lem2431274 (y : int) (x : int) (x' : int) : (term330 y x x') = (y = (int_mul x x')).
Proof. exact (eq_refl (term330 y x x')). Qed.
Lemma lem2431275 (y : int) (x : int) : (term331 y x) = (term329 y x).
Proof. exact (fun_ext (fun x' : int => @lem2431274 y x x')). Qed.
Lemma lem2431276 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2431277 (y : int) (x : int) : (term332 y x) = (term309 y x).
Proof. exact (MK_COMB (@lem2431276) (@lem2431275 y x)). Qed.
Lemma lem2431278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2431279 (y : int) (x : int) : (term333 y x) = (term334 y x).
Proof. exact (MK_COMB (@lem2431278) (@lem2431277 y x)). Qed.
Lemma lem2431280 (x : int) (y : int) : (term314 x y) = (term314 x y).
Proof. exact (eq_refl (term314 x y)). Qed.
Lemma lem2431281 (x : int) (y : int) : (term327 x y) = (term324 x y).
Proof. exact (MK_COMB (@lem2431279 y x) (@lem2431280 x y)). Qed.
Lemma lem2431282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2431283 (x : int) (y : int) : (term335 x y) = (term336 x y).
Proof. exact (MK_COMB (@lem2431282) (@lem2431281 x y)). Qed.
Lemma lem2431284 (y : int) (x : int) (x' : int) : (term330 y x x') = (y = (int_mul x x')).
Proof. exact (eq_refl (term330 y x x')). Qed.
Lemma lem2431285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2431286 (y : int) (x : int) (x' : int) : (term337 y x x') = (term338 y x x').
Proof. exact (MK_COMB (@lem2431285) (@lem2431284 y x x')). Qed.
Lemma lem2431287 (x : int) (y : int) : (term314 x y) = (term314 x y).
Proof. exact (eq_refl (term314 x y)). Qed.
Lemma lem2431288 (x' : int) (x : int) (y : int) : (term339 x' x y) = (term340 x' x y).
Proof. exact (MK_COMB (@lem2431286 y x x') (@lem2431287 x y)). Qed.
Lemma lem2431289 (x : int) (y : int) : (term341 x y) = (term342 x y).
Proof. exact (fun_ext (fun x' : int => @lem2431288 x' x y)). Qed.
Lemma lem2431290 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431291 (x : int) (y : int) : (term328 x y) = (term343 x y).
Proof. exact (MK_COMB (@lem2431290) (@lem2431289 x y)). Qed.
Lemma lem2431292 (x : int) (y : int) : ((term327 x y) = (term328 x y)) = ((term324 x y) = (term343 x y)).
Proof. exact (MK_COMB (@lem2431283 x y) (@lem2431291 x y)). Qed.
Lemma lem2431293 (x : int) (y : int) : (term324 x y) = (term343 x y).
Proof. exact (EQ_MP (@lem2431292 x y) (@lem2431273 x y)). Qed.
Lemma lem2431303 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term310 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2431304 (p : Prop) (q : Prop) (p' : Prop) : term311 p q p'.
Proof. exact (fun q' : Prop => @lem2431303 p q p' q'). Qed.
Lemma lem2431305 (p : Prop) (q : Prop) : term312 p q.
Proof. exact (fun p' : Prop => @lem2431304 p q p'). Qed.
Lemma lem2431306 (x' : int) (x : int) (y : int) : term344 x' x y.
Proof. exact (@lem2431305 (y = (int_mul x x')) (term314 x y)). Qed.
Lemma lem2431307 (x' : int) (x : int) (y : int) (p' : Prop) : term345 x' x y p'.
Proof. exact (@lem2431306 x' x y p'). Qed.
Lemma lem2431308 (x' : int) (x : int) (y : int) (p' : Prop) : (term345 x' x y p') = (term346 x' x y p').
Proof. exact (eq_refl (term345 x' x y p')). Qed.
Lemma lem2431309 (x' : int) (x : int) (y : int) (p' : Prop) : term346 x' x y p'.
Proof. exact (EQ_MP (@lem2431308 x' x y p') (@lem2431307 x' x y p')). Qed.
Lemma lem2431310 (x' : int) (x : int) (y : int) (p' : Prop) (q' : Prop) : term347 x' x y p' q'.
Proof. exact (@lem2431309 x' x y p' q'). Qed.
Lemma lem2431311 (x' : int) (x : int) (y : int) (p' : Prop) (q' : Prop) : (term347 x' x y p' q') = (term348 x' x y p' q').
Proof. exact (eq_refl (term347 x' x y p' q')). Qed.
Lemma lem2431312 (x' : int) (x : int) (y : int) (p' : Prop) (q' : Prop) : term348 x' x y p' q'.
Proof. exact (EQ_MP (@lem2431311 x' x y p' q') (@lem2431310 x' x y p' q')). Qed.
Lemma lem2431315 (y : int) (x : int) (x' : int) : (y = (int_mul x x')) = (y = (int_mul x x')).
Proof. exact (eq_refl (y = (int_mul x x'))). Qed.
Lemma lem2431316 (y : int) (x : int) (x' : int) (q' : Prop) : term349 y x x' q'.
Proof. exact (@lem2431312 x' x y (y = (int_mul x x')) q'). Qed.
Lemma lem2431317 (y : int) (x : int) (x' : int) (q' : Prop) : term350 y x x' q'.
Proof. exact (@lem2431316 y x x' q' (@lem2431315 y x x')). Qed.
Lemma lem2431322 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : y = (int_mul x x').
Proof. exact (h1). Qed.
Lemma lem2431323 : int_abs = int_abs.
Proof. exact (eq_refl int_abs). Qed.
Lemma lem2431324 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (int_abs y) = (term299 x x').
Proof. exact (MK_COMB (@lem2431323) (@lem2431322 y x x' h1)). Qed.
Lemma lem2431326 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (EQ_MP (@lem2431213 x y) (@lem2431212 x y)). Qed.
Lemma lem2431327 (x : int) (x' : int) : (term299 x x') = (term300 x x').
Proof. exact (@lem2431326 x x'). Qed.
Lemma lem2431328 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (int_abs y) = (term300 x x').
Proof. exact (TRANS (@lem2431324 y x x' h1) (@lem2431327 x x')). Qed.
Lemma lem2431329 (x : int) : (term351 x) = (term351 x).
Proof. exact (eq_refl (term351 x)). Qed.
Lemma lem2431330 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (term352 x y) = (term353 x x').
Proof. exact (MK_COMB (@lem2431329 x) (@lem2431328 y x x' h1)). Qed.
Lemma lem2431331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2431332 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (term354 x y) = (term355 x x').
Proof. exact (MK_COMB (@lem2431331) (@lem2431330 y x x' h1)). Qed.
Lemma lem2431336 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : y = (int_mul x x').
Proof. exact (h1). Qed.
Lemma lem2431337 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2431338 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (@eq int y) = (term356 x x').
Proof. exact (MK_COMB (@lem2431337) (@lem2431336 y x x' h1)). Qed.
Lemma lem2431339 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem2431340 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (y = term25) = ((int_mul x x') = term25).
Proof. exact (MK_COMB (@lem2431338 y x x' h1) (@lem2431339)). Qed.
Lemma lem2431342 (x : int) (y : int) : ((int_mul x y) = term25) = (term295 x y).
Proof. exact (EQ_MP (@lem2431207 x y) (@lem2431206 x y)). Qed.
Lemma lem2431343 (x : int) (x' : int) : ((int_mul x x') = term25) = (term295 x x').
Proof. exact (@lem2431342 x x'). Qed.
Lemma lem2431350 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (y = term25) = (term295 x x').
Proof. exact (TRANS (@lem2431340 y x x' h1) (@lem2431343 x x')). Qed.
Lemma lem2431351 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (term314 x y) = (term357 x x').
Proof. exact (MK_COMB (@lem2431332 y x x' h1) (@lem2431350 y x x' h1)). Qed.
Lemma lem2431360 (y : int) (x : int) (x' : int) : term358 y x x'.
Proof. exact (fun h0 : y = (int_mul x x') => @lem2431351 y x x' h0). Qed.
Lemma lem2431361 (y : int) (x : int) (x' : int) : term359 y x x'.
Proof. exact (@lem2431317 y x x' (term357 x x')). Qed.
Lemma lem2431362 (y : int) (x : int) (x' : int) : (term340 x' x y) = (term360 y x x').
Proof. exact (@lem2431361 y x x' (@lem2431360 y x x')). Qed.
Lemma lem2431406 (y : int) (x : int) : (term342 x y) = (term361 y x).
Proof. exact (fun_ext (fun x' : int => @lem2431362 y x x')). Qed.
Lemma lem2431450 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431451 (y : int) (x : int) : (term343 x y) = (term362 y x).
Proof. exact (MK_COMB (@lem2431450) (@lem2431406 y x)). Qed.
Lemma lem2431499 (y : int) (x : int) : (term324 x y) = (term362 y x).
Proof. exact (TRANS (@lem2431293 x y) (@lem2431451 y x)). Qed.
Lemma lem2431500 (y : int) (x : int) : (term323 x y) = (term362 y x).
Proof. exact (TRANS (@lem2431269 x y) (@lem2431499 y x)). Qed.
Lemma lem2431501 (x : int) : (term363 x) = (term364 x).
Proof. exact (fun_ext (fun y : int => @lem2431500 y x)). Qed.
Lemma lem2431549 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431550 (x : int) : (term365 x) = (term366 x).
Proof. exact (MK_COMB (@lem2431549) (@lem2431501 x)). Qed.
Lemma lem2431602 : term367 = term368.
Proof. exact (fun_ext (fun x : int => @lem2431550 x)). Qed.
Lemma lem2431654 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431655 : term369 = term370.
Proof. exact (MK_COMB (@lem2431654) (@lem2431602)). Qed.
Lemma lem2431711 : term370 = term369.
Proof. exact (SYM (@lem2431655)). Qed.
Lemma lem2431731 (q : Prop) (r : Prop) (p : Prop) : (term265 p q r) = (term266 q r p).
Proof. exact (or_elim (@lem2431014 p) (fun h0 : p = True => @lem2431199 q r p h0) (fun h0 : p = False => @lem2431198 q r p h0)). Qed.
Lemma lem2431732 (x : int) (x' : int) : (term357 x x') = (term371 x x').
Proof. exact (@lem2431731 (x = term25) (x' = term25) (term353 x x')). Qed.
Lemma lem2431741 (y : int) (x : int) (x' : int) : (term338 y x x') = (term338 y x x').
Proof. exact (eq_refl (term338 y x x')). Qed.
Lemma lem2431742 (y : int) (x : int) (x' : int) : (term360 y x x') = (term372 y x x').
Proof. exact (MK_COMB (@lem2431741 y x x') (@lem2431732 x x')). Qed.
Lemma lem2431747 (y : int) (x : int) : (term361 y x) = (term373 y x).
Proof. exact (fun_ext (fun x' : int => @lem2431742 y x x')). Qed.
Lemma lem2431748 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431749 (y : int) (x : int) : (term362 y x) = (term374 y x).
Proof. exact (MK_COMB (@lem2431748) (@lem2431747 y x)). Qed.
Lemma lem2431754 (x : int) : (term364 x) = (term375 x).
Proof. exact (fun_ext (fun y : int => @lem2431749 y x)). Qed.
Lemma lem2431755 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431756 (x : int) : (term366 x) = (term376 x).
Proof. exact (MK_COMB (@lem2431755) (@lem2431754 x)). Qed.
Lemma lem2431761 : term368 = term377.
Proof. exact (fun_ext (fun x : int => @lem2431756 x)). Qed.
Lemma lem2431762 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431763 : term370 = term378.
Proof. exact (MK_COMB (@lem2431762) (@lem2431761)). Qed.
Lemma lem2431768 : term378 = term370.
Proof. exact (SYM (@lem2431763)). Qed.
Lemma lem2431796 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2429440 x y) (@lem2430998 x y)). Qed.
Lemma lem2431797 (x : int) (x' : int) : (term353 x x') = (term379 x x').
Proof. exact (@lem2431796 (int_abs x) (int_abs x')). Qed.
Lemma lem2431800 (x : int) (x' : int) : (term380 x x') = (term380 x x').
Proof. exact (eq_refl (term380 x x')). Qed.
Lemma lem2431801 (x : int) (x' : int) : (term371 x x') = (term381 x x').
Proof. exact (MK_COMB (@lem2431800 x x') (@lem2431797 x x')). Qed.
Lemma lem2431804 (y : int) (x : int) (x' : int) : (term338 y x x') = (term338 y x x').
Proof. exact (eq_refl (term338 y x x')). Qed.
Lemma lem2431805 (y : int) (x : int) (x' : int) : (term372 y x x') = (term382 y x x').
Proof. exact (MK_COMB (@lem2431804 y x x') (@lem2431801 x x')). Qed.
Lemma lem2431810 (y : int) (x : int) : (term373 y x) = (term383 y x).
Proof. exact (fun_ext (fun x' : int => @lem2431805 y x x')). Qed.
Lemma lem2431811 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431812 (y : int) (x : int) : (term374 y x) = (term384 y x).
Proof. exact (MK_COMB (@lem2431811) (@lem2431810 y x)). Qed.
Lemma lem2431817 (x : int) : (term375 x) = (term385 x).
Proof. exact (fun_ext (fun y : int => @lem2431812 y x)). Qed.
Lemma lem2431818 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431819 (x : int) : (term376 x) = (term386 x).
Proof. exact (MK_COMB (@lem2431818) (@lem2431817 x)). Qed.
Lemma lem2431824 : term377 = term387.
Proof. exact (fun_ext (fun x : int => @lem2431819 x)). Qed.
Lemma lem2431825 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2431826 : term378 = term388.
Proof. exact (MK_COMB (@lem2431825) (@lem2431824)). Qed.
Lemma lem2431831 : term388 = term378.
Proof. exact (SYM (@lem2431826)). Qed.
Lemma lem2431832 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : y = (int_mul x x').
Proof. exact (h1). Qed.
Lemma lem2431833 (x : int) (x' : int) (h1 : term389 x x') : term389 x x'.
Proof. exact (h1). Qed.
Lemma lem2431834 (x' : int) (h1 : term390 x') : term390 x'.
Proof. exact (h1). Qed.
Lemma lem2431835 (x : int) (h1 : term390 x) : term390 x.
Proof. exact (h1). Qed.
Lemma lem2431837 (x : int) (y : int) : term4 x y.
Proof. exact (EQ_MP (@lem2429438 x y) (@lem2429437 x y)). Qed.
Lemma lem2431838 (x : int) (x' : int) : term391 x x'.
Proof. exact (@lem2431837 (int_abs x) (term392 x')). Qed.
Lemma lem2431839 (y : int) (x : int) (x' : int) : (term393 y x x') = (term394 y x x').
Proof. exact (@lem2318604 (term394 y x x')). Qed.
Lemma lem2431862 (x : int) (x' : int) : (term395 x x') = (term396 x x').
Proof. exact (@lem17045 (term397 x) (term398 x')). Qed.
Lemma lem2431864 (x' : int) : (term399 x') = (term399 x').
Proof. exact (eq_refl (term399 x')). Qed.
Lemma lem2431865 (x : int) (x' : int) : (term400 x x') = (term401 x x').
Proof. exact (MK_COMB (@lem2431864 x') (@lem2431862 x x')). Qed.
Lemma lem2431866 (x : int) (x' : int) : (term402 x x') = (term400 x x').
Proof. exact (@lem17362 (term390 x') (term403 x x')). Qed.
Lemma lem2431867 (x : int) (x' : int) : (term402 x x') = (term401 x x').
Proof. exact (TRANS (@lem2431866 x x') (@lem2431865 x x')). Qed.
Lemma lem2431869 (x : int) : (term399 x) = (term399 x).
Proof. exact (eq_refl (term399 x)). Qed.
Lemma lem2431870 (x : int) (x' : int) : (term404 x x') = (term405 x x').
Proof. exact (MK_COMB (@lem2431869 x) (@lem2431867 x x')). Qed.
Lemma lem2431871 (x : int) (x' : int) : (term406 x x') = (term404 x x').
Proof. exact (@lem17362 (term390 x) (term407 x x')). Qed.
Lemma lem2431872 (x : int) (x' : int) : (term406 x x') = (term405 x x').
Proof. exact (TRANS (@lem2431871 x x') (@lem2431870 x x')). Qed.
Lemma lem2431874 (y : int) (x : int) (x' : int) : (term408 y x x') = (term408 y x x').
Proof. exact (eq_refl (term408 y x x')). Qed.
Lemma lem2431875 (y : int) (x : int) (x' : int) : (term409 y x x') = (term410 y x x').
Proof. exact (MK_COMB (@lem2431874 y x x') (@lem2431872 x x')). Qed.
Lemma lem2431876 (y : int) (x : int) (x' : int) : (term411 y x x') = (term409 y x x').
Proof. exact (@lem17362 (y = (int_mul x x')) (term412 x x')). Qed.
Lemma lem2431904 (y : int) (x : int) (x' : int) : (term411 y x x') = (term410 y x x').
Proof. exact (TRANS (@lem2431876 y x x') (@lem2431875 y x x')). Qed.
Lemma lem2431907 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2431908 (y : int) (x : int) (x' : int) : (y = (int_mul x x')) = ((real_of_int y) = (term16 x x')).
Proof. exact (@lem2431907 y (int_mul x x')). Qed.
Lemma lem2431912 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2431913 (x : int) (x' : int) : (term16 x x') = (term17 x x').
Proof. exact (@lem2431912 x x'). Qed.
Lemma lem2431914 (y : int) : (term413 y) = (term413 y).
Proof. exact (eq_refl (term413 y)). Qed.
Lemma lem2431915 (y : int) (x : int) (x' : int) : ((real_of_int y) = (term16 x x')) = ((real_of_int y) = (term17 x x')).
Proof. exact (MK_COMB (@lem2431914 y) (@lem2431913 x x')). Qed.
Lemma lem2431917 (y : int) (x : int) (x' : int) : (y = (int_mul x x')) = ((real_of_int y) = (term17 x x')).
Proof. exact (TRANS (@lem2431908 y x x') (@lem2431915 y x x')). Qed.
Lemma lem2431919 (y : int) (x : int) : (term414 x y) = (term415 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2431920 (x : int) : (term390 x) = (term416 x).
Proof. exact (@lem2431919 term25 x). Qed.
Lemma lem2431922 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2431923 (x : int) : (term417 x) = (term418 x).
Proof. exact (@lem2431922 (term419 x) term25). Qed.
Lemma lem2431925 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2431926 (x : int) : (term420 x) = (term421 x).
Proof. exact (@lem2431925 x term32). Qed.
Lemma lem2431928 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2431929 : term41 = term42.
Proof. exact (@lem2431928 term43). Qed.
Lemma lem2431930 (x : int) : (term116 x) = (term116 x).
Proof. exact (eq_refl (term116 x)). Qed.
Lemma lem2431931 (x : int) : (term421 x) = (term422 x).
Proof. exact (MK_COMB (@lem2431930 x) (@lem2431929)). Qed.
Lemma lem2431932 (x : int) : (term420 x) = (term422 x).
Proof. exact (TRANS (@lem2431926 x) (@lem2431931 x)). Qed.
Lemma lem2431933 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2431934 (x : int) : (term423 x) = (term424 x).
Proof. exact (MK_COMB (@lem2431933) (@lem2431932 x)). Qed.
Lemma lem2431936 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2431937 : term53 = term54.
Proof. exact (@lem2431936 (NUMERAL 0)). Qed.
Lemma lem2431938 (x : int) : (term418 x) = (term425 x).
Proof. exact (MK_COMB (@lem2431934 x) (@lem2431937)). Qed.
Lemma lem2431939 (x : int) : (term417 x) = (term425 x).
Proof. exact (TRANS (@lem2431923 x) (@lem2431938 x)). Qed.
Lemma lem2431940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2431941 (x : int) : (term426 x) = (term427 x).
Proof. exact (MK_COMB (@lem2431940) (@lem2431939 x)). Qed.
Lemma lem2431943 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2431944 (x : int) : (term428 x) = (term429 x).
Proof. exact (@lem2431943 term430 x). Qed.
Lemma lem2431946 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2431947 : term431 = term432.
Proof. exact (@lem2431946 term25 term32). Qed.
Lemma lem2431949 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2431950 : term53 = term54.
Proof. exact (@lem2431949 (NUMERAL 0)). Qed.
Lemma lem2431951 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2431952 : term433 = term148.
Proof. exact (MK_COMB (@lem2431951) (@lem2431950)). Qed.
Lemma lem2431954 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2431955 : term41 = term42.
Proof. exact (@lem2431954 term43). Qed.
Lemma lem2431956 : term432 = term434.
Proof. exact (MK_COMB (@lem2431952) (@lem2431955)). Qed.
Lemma lem2431957 : term431 = term434.
Proof. exact (TRANS (@lem2431947) (@lem2431956)). Qed.
Lemma lem2431958 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2431959 : term435 = term436.
Proof. exact (MK_COMB (@lem2431958) (@lem2431957)). Qed.
Lemma lem2431960 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2431961 (x : int) : (term429 x) = (term437 x).
Proof. exact (MK_COMB (@lem2431959) (@lem2431960 x)). Qed.
Lemma lem2431962 (x : int) : (term428 x) = (term437 x).
Proof. exact (TRANS (@lem2431944 x) (@lem2431961 x)). Qed.
Lemma lem2431963 (x : int) : (term416 x) = (term438 x).
Proof. exact (MK_COMB (@lem2431941 x) (@lem2431962 x)). Qed.
Lemma lem2431964 (x : int) : (term390 x) = (term438 x).
Proof. exact (TRANS (@lem2431920 x) (@lem2431963 x)). Qed.
Lemma lem2431966 (y : int) (x : int) : (term414 x y) = (term415 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2431967 (x' : int) : (term390 x') = (term416 x').
Proof. exact (@lem2431966 term25 x'). Qed.
Lemma lem2431969 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2431970 (x' : int) : (term417 x') = (term418 x').
Proof. exact (@lem2431969 (term419 x') term25). Qed.
Lemma lem2431972 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2431973 (x' : int) : (term420 x') = (term421 x').
Proof. exact (@lem2431972 x' term32). Qed.
Lemma lem2431975 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2431976 : term41 = term42.
Proof. exact (@lem2431975 term43). Qed.
Lemma lem2431977 (x' : int) : (term116 x') = (term116 x').
Proof. exact (eq_refl (term116 x')). Qed.
Lemma lem2431978 (x' : int) : (term421 x') = (term422 x').
Proof. exact (MK_COMB (@lem2431977 x') (@lem2431976)). Qed.
Lemma lem2431979 (x' : int) : (term420 x') = (term422 x').
Proof. exact (TRANS (@lem2431973 x') (@lem2431978 x')). Qed.
Lemma lem2431980 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2431981 (x' : int) : (term423 x') = (term424 x').
Proof. exact (MK_COMB (@lem2431980) (@lem2431979 x')). Qed.
Lemma lem2431983 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2431984 : term53 = term54.
Proof. exact (@lem2431983 (NUMERAL 0)). Qed.
Lemma lem2431985 (x' : int) : (term418 x') = (term425 x').
Proof. exact (MK_COMB (@lem2431981 x') (@lem2431984)). Qed.
Lemma lem2431986 (x' : int) : (term417 x') = (term425 x').
Proof. exact (TRANS (@lem2431970 x') (@lem2431985 x')). Qed.
Lemma lem2431987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2431988 (x' : int) : (term426 x') = (term427 x').
Proof. exact (MK_COMB (@lem2431987) (@lem2431986 x')). Qed.
Lemma lem2431990 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2431991 (x' : int) : (term428 x') = (term429 x').
Proof. exact (@lem2431990 term430 x'). Qed.
Lemma lem2431993 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2431994 : term431 = term432.
Proof. exact (@lem2431993 term25 term32). Qed.
Lemma lem2431996 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2431997 : term53 = term54.
Proof. exact (@lem2431996 (NUMERAL 0)). Qed.
Lemma lem2431998 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2431999 : term433 = term148.
Proof. exact (MK_COMB (@lem2431998) (@lem2431997)). Qed.
Lemma lem2432001 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2432002 : term41 = term42.
Proof. exact (@lem2432001 term43). Qed.
Lemma lem2432003 : term432 = term434.
Proof. exact (MK_COMB (@lem2431999) (@lem2432002)). Qed.
Lemma lem2432004 : term431 = term434.
Proof. exact (TRANS (@lem2431994) (@lem2432003)). Qed.
Lemma lem2432005 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2432006 : term435 = term436.
Proof. exact (MK_COMB (@lem2432005) (@lem2432004)). Qed.
Lemma lem2432007 (x' : int) : (real_of_int x') = (real_of_int x').
Proof. exact (eq_refl (real_of_int x')). Qed.
Lemma lem2432008 (x' : int) : (term429 x') = (term437 x').
Proof. exact (MK_COMB (@lem2432006) (@lem2432007 x')). Qed.
Lemma lem2432009 (x' : int) : (term428 x') = (term437 x').
Proof. exact (TRANS (@lem2431991 x') (@lem2432008 x')). Qed.
Lemma lem2432010 (x' : int) : (term416 x') = (term438 x').
Proof. exact (MK_COMB (@lem2431988 x') (@lem2432009 x')). Qed.
Lemma lem2432011 (x' : int) : (term390 x') = (term438 x').
Proof. exact (TRANS (@lem2431967 x') (@lem2432010 x')). Qed.
Lemma lem2432013 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2432014 (x : int) : (term439 x) = (term440 x).
Proof. exact (@lem2432013 (int_abs x) term25). Qed.
Lemma lem2432016 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2432017 (x : int) : (term440 x) = (term441 x).
Proof. exact (@lem2432016 (term442 x) term25). Qed.
Lemma lem2432019 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2432020 (x : int) : (term443 x) = (term444 x).
Proof. exact (@lem2432019 (int_abs x) term32). Qed.
Lemma lem2432022 (x : int) : (term445 x) = (term446 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2432023 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2432024 (x : int) : (term447 x) = (term448 x).
Proof. exact (MK_COMB (@lem2432023) (@lem2432022 x)). Qed.
Lemma lem2432026 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2432027 : term41 = term42.
Proof. exact (@lem2432026 term43). Qed.
Lemma lem2432028 (x : int) : (term444 x) = (term449 x).
Proof. exact (MK_COMB (@lem2432024 x) (@lem2432027)). Qed.
Lemma lem2432029 (x : int) : (term443 x) = (term449 x).
Proof. exact (TRANS (@lem2432020 x) (@lem2432028 x)). Qed.
Lemma lem2432030 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2432031 (x : int) : (term450 x) = (term451 x).
Proof. exact (MK_COMB (@lem2432030) (@lem2432029 x)). Qed.
Lemma lem2432033 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2432034 : term53 = term54.
Proof. exact (@lem2432033 (NUMERAL 0)). Qed.
Lemma lem2432035 (x : int) : (term441 x) = (term452 x).
Proof. exact (MK_COMB (@lem2432031 x) (@lem2432034)). Qed.
Lemma lem2432036 (x : int) : (term440 x) = (term452 x).
Proof. exact (TRANS (@lem2432017 x) (@lem2432035 x)). Qed.
Lemma lem2432037 (x : int) : (term439 x) = (term452 x).
Proof. exact (TRANS (@lem2432014 x) (@lem2432036 x)). Qed.
Lemma lem2432039 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2432040 (x' : int) : (term453 x') = (term454 x').
Proof. exact (@lem2432039 (term392 x') term25). Qed.
Lemma lem2432042 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2432043 (x' : int) : (term454 x') = (term455 x').
Proof. exact (@lem2432042 (term456 x') term25). Qed.
Lemma lem2432045 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2432046 (x' : int) : (term457 x') = (term458 x').
Proof. exact (@lem2432045 (term392 x') term32). Qed.
Lemma lem2432048 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2432049 (x' : int) : (term459 x') = (term460 x').
Proof. exact (@lem2432048 (int_abs x') term32). Qed.
Lemma lem2432051 (x : int) : (term445 x) = (term446 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2432052 (x' : int) : (term445 x') = (term446 x').
Proof. exact (@lem2432051 x'). Qed.
Lemma lem2432053 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2432054 (x' : int) : (term461 x') = (term462 x').
Proof. exact (MK_COMB (@lem2432053) (@lem2432052 x')). Qed.
Lemma lem2432056 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2432057 : term41 = term42.
Proof. exact (@lem2432056 term43). Qed.
Lemma lem2432058 (x' : int) : (term460 x') = (term463 x').
Proof. exact (MK_COMB (@lem2432054 x') (@lem2432057)). Qed.
Lemma lem2432059 (x' : int) : (term459 x') = (term463 x').
Proof. exact (TRANS (@lem2432049 x') (@lem2432058 x')). Qed.
Lemma lem2432060 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2432061 (x' : int) : (term464 x') = (term465 x').
Proof. exact (MK_COMB (@lem2432060) (@lem2432059 x')). Qed.
Lemma lem2432063 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2432064 : term41 = term42.
Proof. exact (@lem2432063 term43). Qed.
Lemma lem2432065 (x' : int) : (term458 x') = (term466 x').
Proof. exact (MK_COMB (@lem2432061 x') (@lem2432064)). Qed.
Lemma lem2432066 (x' : int) : (term457 x') = (term466 x').
Proof. exact (TRANS (@lem2432046 x') (@lem2432065 x')). Qed.
Lemma lem2432067 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2432068 (x' : int) : (term467 x') = (term468 x').
Proof. exact (MK_COMB (@lem2432067) (@lem2432066 x')). Qed.
Lemma lem2432070 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2432071 : term53 = term54.
Proof. exact (@lem2432070 (NUMERAL 0)). Qed.
Lemma lem2432072 (x' : int) : (term455 x') = (term469 x').
Proof. exact (MK_COMB (@lem2432068 x') (@lem2432071)). Qed.
Lemma lem2432073 (x' : int) : (term454 x') = (term469 x').
Proof. exact (TRANS (@lem2432043 x') (@lem2432072 x')). Qed.
Lemma lem2432074 (x' : int) : (term453 x') = (term469 x').
Proof. exact (TRANS (@lem2432040 x') (@lem2432073 x')). Qed.
Lemma lem2432075 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432076 (x : int) : (term470 x) = (term471 x).
Proof. exact (MK_COMB (@lem2432075) (@lem2432037 x)). Qed.
Lemma lem2432077 (x : int) (x' : int) : (term396 x x') = (term472 x x').
Proof. exact (MK_COMB (@lem2432076 x) (@lem2432074 x')). Qed.
Lemma lem2432078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432079 (x' : int) : (term399 x') = (term473 x').
Proof. exact (MK_COMB (@lem2432078) (@lem2432011 x')). Qed.
Lemma lem2432080 (x : int) (x' : int) : (term401 x x') = (term474 x x').
Proof. exact (MK_COMB (@lem2432079 x') (@lem2432077 x x')). Qed.
Lemma lem2432081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432082 (x : int) : (term399 x) = (term473 x).
Proof. exact (MK_COMB (@lem2432081) (@lem2431964 x)). Qed.
Lemma lem2432083 (x : int) (x' : int) : (term405 x x') = (term475 x x').
Proof. exact (MK_COMB (@lem2432082 x) (@lem2432080 x x')). Qed.
Lemma lem2432084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432085 (y : int) (x : int) (x' : int) : (term408 y x x') = (term476 y x x').
Proof. exact (MK_COMB (@lem2432084) (@lem2431917 y x x')). Qed.
Lemma lem2432086 (y : int) (x : int) (x' : int) : (term410 y x x') = (term477 y x x').
Proof. exact (MK_COMB (@lem2432085 y x x') (@lem2432083 x x')). Qed.
Lemma lem2432087 (y : int) (x : int) (x' : int) : (term411 y x x') = (term477 y x x').
Proof. exact (TRANS (@lem2431904 y x x') (@lem2432086 y x x')). Qed.
Lemma lem2432091 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2432157 (y : int) (x : int) (x' : int) : (term478 y x x') = (term477 y x x').
Proof. exact (@lem2432091 (term477 y x x')). Qed.
Lemma lem2432158 (y : int) (x : int) (x' : int) : ((real_of_int y) = (term17 x x')) = ((term479 y x x') = term54).
Proof. exact (@lem1988293 (real_of_int y) (term17 x x')). Qed.
Lemma lem2432170 (y : int) (x : int) (x' : int) : (term479 y x x') = (term480 y x x').
Proof. exact (@lem1982792 (real_of_int y) (term17 x x')). Qed.
Lemma lem2432175 (x : int) (x' : int) (y : int) : (term480 y x x') = (term481 x x' y).
Proof. exact (@lem1982761 (term162 x x') (real_of_int y)). Qed.
Lemma lem2432177 (x : int) (x' : int) (y : int) : (term479 y x x') = (term481 x x' y).
Proof. exact (TRANS (@lem2432170 y x x') (@lem2432175 x x' y)). Qed.
Lemma lem2432178 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2432179 (x : int) (x' : int) (y : int) : (term482 y x x') = (term483 x x' y).
Proof. exact (MK_COMB (@lem2432178) (@lem2432177 x x' y)). Qed.
Lemma lem2432180 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432181 (x : int) (x' : int) (y : int) : ((term479 y x x') = term54) = ((term481 x x' y) = term54).
Proof. exact (MK_COMB (@lem2432179 x x' y) (@lem2432180)). Qed.
Lemma lem2432182 (x : int) (x' : int) (y : int) : ((real_of_int y) = (term17 x x')) = ((term481 x x' y) = term54).
Proof. exact (TRANS (@lem2432158 y x x') (@lem2432181 x x' y)). Qed.
Lemma lem2432183 (x : int) : (term425 x) = (term484 x).
Proof. exact (@lem1988287 term54 (term422 x)). Qed.
Lemma lem2432195 (x : int) : (term485 x) = (term486 x).
Proof. exact (@lem1982792 term54 (term422 x)). Qed.
Lemma lem2432196 (x : int) : (term487 x) = (term488 x).
Proof. exact (@lem1982781 (real_of_int x) term97 term42). Qed.
Lemma lem2432198 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2432199 : term42 = term94.
Proof. exact (@lem2432198 term43). Qed.
Lemma lem2432201 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2432202 : term97 = term98.
Proof. exact (@lem2432201 term43). Qed.
Lemma lem2432203 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2432204 : term99 = term100.
Proof. exact (MK_COMB (@lem2432203) (@lem2432202)). Qed.
Lemma lem2432205 : term101 = term102.
Proof. exact (MK_COMB (@lem2432204) (@lem2432199)). Qed.
Lemma lem2432206 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2432208 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2432209 : term106 = term107.
Proof. exact (@lem2432208 term43 term43). Qed.
Lemma lem2432210 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432211 : term109 = term43.
Proof. exact (EQ_MP (@lem2432210) (@lem940073)). Qed.
Lemma lem2432212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432213 : term107 = term42.
Proof. exact (MK_COMB (@lem2432212) (@lem2432211)). Qed.
Lemma lem2432214 : term106 = term42.
Proof. exact (TRANS (@lem2432209) (@lem2432213)). Qed.
Lemma lem2432216 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2432217 : term101 = term112.
Proof. exact (@lem2432216 term43 term43). Qed.
Lemma lem2432218 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432219 : term109 = term43.
Proof. exact (EQ_MP (@lem2432218) (@lem940073)). Qed.
Lemma lem2432220 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432221 : term107 = term42.
Proof. exact (MK_COMB (@lem2432220) (@lem2432219)). Qed.
Lemma lem2432222 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2432223 : term112 = term97.
Proof. exact (MK_COMB (@lem2432222) (@lem2432221)). Qed.
Lemma lem2432224 : term101 = term97.
Proof. exact (TRANS (@lem2432217) (@lem2432223)). Qed.
Lemma lem2432225 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2432226 : term113 = term114.
Proof. exact (MK_COMB (@lem2432225) (@lem2432224)). Qed.
Lemma lem2432227 : term103 = term98.
Proof. exact (MK_COMB (@lem2432226) (@lem2432214)). Qed.
Lemma lem2432228 : term102 = term98.
Proof. exact (TRANS (@lem2432206) (@lem2432227)). Qed.
Lemma lem2432229 : term101 = term98.
Proof. exact (TRANS (@lem2432205) (@lem2432228)). Qed.
Lemma lem2432231 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2432232 : term98 = term97.
Proof. exact (@lem2432231 term97). Qed.
Lemma lem2432233 : term101 = term97.
Proof. exact (TRANS (@lem2432229) (@lem2432232)). Qed.
Lemma lem2432236 (x : int) : (term489 x) = (term489 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem2432237 (x : int) : (term488 x) = (term490 x).
Proof. exact (MK_COMB (@lem2432236 x) (@lem2432233)). Qed.
Lemma lem2432238 (x : int) : (term487 x) = (term490 x).
Proof. exact (TRANS (@lem2432196 x) (@lem2432237 x)). Qed.
Lemma lem2432239 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem2432240 (x : int) : (term486 x) = (term491 x).
Proof. exact (MK_COMB (@lem2432239) (@lem2432238 x)). Qed.
Lemma lem2432241 (x : int) : (term491 x) = (term490 x).
Proof. exact (@lem1982721 (term490 x)). Qed.
Lemma lem2432242 (x : int) : (term486 x) = (term490 x).
Proof. exact (TRANS (@lem2432240 x) (@lem2432241 x)). Qed.
Lemma lem2432244 (x : int) : (term485 x) = (term490 x).
Proof. exact (TRANS (@lem2432195 x) (@lem2432242 x)). Qed.
Lemma lem2432245 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432246 (x : int) : (term492 x) = (term493 x).
Proof. exact (MK_COMB (@lem2432245) (@lem2432244 x)). Qed.
Lemma lem2432247 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432248 (x : int) : (term484 x) = (term494 x).
Proof. exact (MK_COMB (@lem2432246 x) (@lem2432247)). Qed.
Lemma lem2432249 (x : int) : (term425 x) = (term494 x).
Proof. exact (TRANS (@lem2432183 x) (@lem2432248 x)). Qed.
Lemma lem2432250 (x : int) : (term437 x) = (term495 x).
Proof. exact (@lem1988287 (real_of_int x) term434). Qed.
Lemma lem2432257 : term434 = term42.
Proof. exact (@lem1982721 term42). Qed.
Lemma lem2432260 (x : int) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem2432261 (x : int) : (term496 x) = (term45 x).
Proof. exact (MK_COMB (@lem2432260 x) (@lem2432257)). Qed.
Lemma lem2432262 (x : int) : (term45 x) = (term92 x).
Proof. exact (@lem1982792 (real_of_int x) term42). Qed.
Lemma lem2432264 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2432265 : term42 = term94.
Proof. exact (@lem2432264 term43). Qed.
Lemma lem2432267 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2432268 : term97 = term98.
Proof. exact (@lem2432267 term43). Qed.
Lemma lem2432269 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2432270 : term99 = term100.
Proof. exact (MK_COMB (@lem2432269) (@lem2432268)). Qed.
Lemma lem2432271 : term101 = term102.
Proof. exact (MK_COMB (@lem2432270) (@lem2432265)). Qed.
Lemma lem2432272 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2432274 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2432275 : term106 = term107.
Proof. exact (@lem2432274 term43 term43). Qed.
Lemma lem2432276 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432277 : term109 = term43.
Proof. exact (EQ_MP (@lem2432276) (@lem940073)). Qed.
Lemma lem2432278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432279 : term107 = term42.
Proof. exact (MK_COMB (@lem2432278) (@lem2432277)). Qed.
Lemma lem2432280 : term106 = term42.
Proof. exact (TRANS (@lem2432275) (@lem2432279)). Qed.
Lemma lem2432282 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2432283 : term101 = term112.
Proof. exact (@lem2432282 term43 term43). Qed.
Lemma lem2432284 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432285 : term109 = term43.
Proof. exact (EQ_MP (@lem2432284) (@lem940073)). Qed.
Lemma lem2432286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432287 : term107 = term42.
Proof. exact (MK_COMB (@lem2432286) (@lem2432285)). Qed.
Lemma lem2432288 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2432289 : term112 = term97.
Proof. exact (MK_COMB (@lem2432288) (@lem2432287)). Qed.
Lemma lem2432290 : term101 = term97.
Proof. exact (TRANS (@lem2432283) (@lem2432289)). Qed.
Lemma lem2432291 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2432292 : term113 = term114.
Proof. exact (MK_COMB (@lem2432291) (@lem2432290)). Qed.
Lemma lem2432293 : term103 = term98.
Proof. exact (MK_COMB (@lem2432292) (@lem2432280)). Qed.
Lemma lem2432294 : term102 = term98.
Proof. exact (TRANS (@lem2432272) (@lem2432293)). Qed.
Lemma lem2432295 : term101 = term98.
Proof. exact (TRANS (@lem2432271) (@lem2432294)). Qed.
Lemma lem2432297 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2432298 : term98 = term97.
Proof. exact (@lem2432297 term97). Qed.
Lemma lem2432299 : term101 = term97.
Proof. exact (TRANS (@lem2432295) (@lem2432298)). Qed.
Lemma lem2432300 (x : int) : (term116 x) = (term116 x).
Proof. exact (eq_refl (term116 x)). Qed.
Lemma lem2432303 (x : int) : (term92 x) = (term117 x).
Proof. exact (MK_COMB (@lem2432300 x) (@lem2432299)). Qed.
Lemma lem2432304 (x : int) : (term45 x) = (term117 x).
Proof. exact (TRANS (@lem2432262 x) (@lem2432303 x)). Qed.
Lemma lem2432305 (x : int) : (term496 x) = (term117 x).
Proof. exact (TRANS (@lem2432261 x) (@lem2432304 x)). Qed.
Lemma lem2432306 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432307 (x : int) : (term497 x) = (term498 x).
Proof. exact (MK_COMB (@lem2432306) (@lem2432305 x)). Qed.
Lemma lem2432308 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432309 (x : int) : (term495 x) = (term499 x).
Proof. exact (MK_COMB (@lem2432307 x) (@lem2432308)). Qed.
Lemma lem2432310 (x : int) : (term437 x) = (term499 x).
Proof. exact (TRANS (@lem2432250 x) (@lem2432309 x)). Qed.
Lemma lem2432311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432312 (x : int) : (term427 x) = (term500 x).
Proof. exact (MK_COMB (@lem2432311) (@lem2432249 x)). Qed.
Lemma lem2432313 (x : int) : (term438 x) = (term501 x).
Proof. exact (MK_COMB (@lem2432312 x) (@lem2432310 x)). Qed.
Lemma lem2432314 (x' : int) : (term425 x') = (term484 x').
Proof. exact (@lem1988287 term54 (term422 x')). Qed.
Lemma lem2432326 (x' : int) : (term485 x') = (term486 x').
Proof. exact (@lem1982792 term54 (term422 x')). Qed.
Lemma lem2432327 (x' : int) : (term487 x') = (term488 x').
Proof. exact (@lem1982781 (real_of_int x') term97 term42). Qed.
Lemma lem2432329 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2432330 : term42 = term94.
Proof. exact (@lem2432329 term43). Qed.
Lemma lem2432332 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2432333 : term97 = term98.
Proof. exact (@lem2432332 term43). Qed.
Lemma lem2432334 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2432335 : term99 = term100.
Proof. exact (MK_COMB (@lem2432334) (@lem2432333)). Qed.
Lemma lem2432336 : term101 = term102.
Proof. exact (MK_COMB (@lem2432335) (@lem2432330)). Qed.
Lemma lem2432337 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2432339 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2432340 : term106 = term107.
Proof. exact (@lem2432339 term43 term43). Qed.
Lemma lem2432341 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432342 : term109 = term43.
Proof. exact (EQ_MP (@lem2432341) (@lem940073)). Qed.
Lemma lem2432343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432344 : term107 = term42.
Proof. exact (MK_COMB (@lem2432343) (@lem2432342)). Qed.
Lemma lem2432345 : term106 = term42.
Proof. exact (TRANS (@lem2432340) (@lem2432344)). Qed.
Lemma lem2432347 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2432348 : term101 = term112.
Proof. exact (@lem2432347 term43 term43). Qed.
Lemma lem2432349 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432350 : term109 = term43.
Proof. exact (EQ_MP (@lem2432349) (@lem940073)). Qed.
Lemma lem2432351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432352 : term107 = term42.
Proof. exact (MK_COMB (@lem2432351) (@lem2432350)). Qed.
Lemma lem2432353 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2432354 : term112 = term97.
Proof. exact (MK_COMB (@lem2432353) (@lem2432352)). Qed.
Lemma lem2432355 : term101 = term97.
Proof. exact (TRANS (@lem2432348) (@lem2432354)). Qed.
Lemma lem2432356 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2432357 : term113 = term114.
Proof. exact (MK_COMB (@lem2432356) (@lem2432355)). Qed.
Lemma lem2432358 : term103 = term98.
Proof. exact (MK_COMB (@lem2432357) (@lem2432345)). Qed.
Lemma lem2432359 : term102 = term98.
Proof. exact (TRANS (@lem2432337) (@lem2432358)). Qed.
Lemma lem2432360 : term101 = term98.
Proof. exact (TRANS (@lem2432336) (@lem2432359)). Qed.
Lemma lem2432362 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2432363 : term98 = term97.
Proof. exact (@lem2432362 term97). Qed.
Lemma lem2432364 : term101 = term97.
Proof. exact (TRANS (@lem2432360) (@lem2432363)). Qed.
Lemma lem2432367 (x' : int) : (term489 x') = (term489 x').
Proof. exact (eq_refl (term489 x')). Qed.
Lemma lem2432368 (x' : int) : (term488 x') = (term490 x').
Proof. exact (MK_COMB (@lem2432367 x') (@lem2432364)). Qed.
Lemma lem2432369 (x' : int) : (term487 x') = (term490 x').
Proof. exact (TRANS (@lem2432327 x') (@lem2432368 x')). Qed.
Lemma lem2432370 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem2432371 (x' : int) : (term486 x') = (term491 x').
Proof. exact (MK_COMB (@lem2432370) (@lem2432369 x')). Qed.
Lemma lem2432372 (x' : int) : (term491 x') = (term490 x').
Proof. exact (@lem1982721 (term490 x')). Qed.
Lemma lem2432373 (x' : int) : (term486 x') = (term490 x').
Proof. exact (TRANS (@lem2432371 x') (@lem2432372 x')). Qed.
Lemma lem2432375 (x' : int) : (term485 x') = (term490 x').
Proof. exact (TRANS (@lem2432326 x') (@lem2432373 x')). Qed.
Lemma lem2432376 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432377 (x' : int) : (term492 x') = (term493 x').
Proof. exact (MK_COMB (@lem2432376) (@lem2432375 x')). Qed.
Lemma lem2432378 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432379 (x' : int) : (term484 x') = (term494 x').
Proof. exact (MK_COMB (@lem2432377 x') (@lem2432378)). Qed.
Lemma lem2432380 (x' : int) : (term425 x') = (term494 x').
Proof. exact (TRANS (@lem2432314 x') (@lem2432379 x')). Qed.
Lemma lem2432381 (x' : int) : (term437 x') = (term495 x').
Proof. exact (@lem1988287 (real_of_int x') term434). Qed.
Lemma lem2432388 : term434 = term42.
Proof. exact (@lem1982721 term42). Qed.
Lemma lem2432391 (x' : int) : (term44 x') = (term44 x').
Proof. exact (eq_refl (term44 x')). Qed.
Lemma lem2432392 (x' : int) : (term496 x') = (term45 x').
Proof. exact (MK_COMB (@lem2432391 x') (@lem2432388)). Qed.
Lemma lem2432393 (x' : int) : (term45 x') = (term92 x').
Proof. exact (@lem1982792 (real_of_int x') term42). Qed.
Lemma lem2432395 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2432396 : term42 = term94.
Proof. exact (@lem2432395 term43). Qed.
Lemma lem2432398 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2432399 : term97 = term98.
Proof. exact (@lem2432398 term43). Qed.
Lemma lem2432400 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2432401 : term99 = term100.
Proof. exact (MK_COMB (@lem2432400) (@lem2432399)). Qed.
Lemma lem2432402 : term101 = term102.
Proof. exact (MK_COMB (@lem2432401) (@lem2432396)). Qed.
Lemma lem2432403 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2432405 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2432406 : term106 = term107.
Proof. exact (@lem2432405 term43 term43). Qed.
Lemma lem2432407 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432408 : term109 = term43.
Proof. exact (EQ_MP (@lem2432407) (@lem940073)). Qed.
Lemma lem2432409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432410 : term107 = term42.
Proof. exact (MK_COMB (@lem2432409) (@lem2432408)). Qed.
Lemma lem2432411 : term106 = term42.
Proof. exact (TRANS (@lem2432406) (@lem2432410)). Qed.
Lemma lem2432413 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2432414 : term101 = term112.
Proof. exact (@lem2432413 term43 term43). Qed.
Lemma lem2432415 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432416 : term109 = term43.
Proof. exact (EQ_MP (@lem2432415) (@lem940073)). Qed.
Lemma lem2432417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432418 : term107 = term42.
Proof. exact (MK_COMB (@lem2432417) (@lem2432416)). Qed.
Lemma lem2432419 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2432420 : term112 = term97.
Proof. exact (MK_COMB (@lem2432419) (@lem2432418)). Qed.
Lemma lem2432421 : term101 = term97.
Proof. exact (TRANS (@lem2432414) (@lem2432420)). Qed.
Lemma lem2432422 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2432423 : term113 = term114.
Proof. exact (MK_COMB (@lem2432422) (@lem2432421)). Qed.
Lemma lem2432424 : term103 = term98.
Proof. exact (MK_COMB (@lem2432423) (@lem2432411)). Qed.
Lemma lem2432425 : term102 = term98.
Proof. exact (TRANS (@lem2432403) (@lem2432424)). Qed.
Lemma lem2432426 : term101 = term98.
Proof. exact (TRANS (@lem2432402) (@lem2432425)). Qed.
Lemma lem2432428 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2432429 : term98 = term97.
Proof. exact (@lem2432428 term97). Qed.
Lemma lem2432430 : term101 = term97.
Proof. exact (TRANS (@lem2432426) (@lem2432429)). Qed.
Lemma lem2432431 (x' : int) : (term116 x') = (term116 x').
Proof. exact (eq_refl (term116 x')). Qed.
Lemma lem2432434 (x' : int) : (term92 x') = (term117 x').
Proof. exact (MK_COMB (@lem2432431 x') (@lem2432430)). Qed.
Lemma lem2432435 (x' : int) : (term45 x') = (term117 x').
Proof. exact (TRANS (@lem2432393 x') (@lem2432434 x')). Qed.
Lemma lem2432436 (x' : int) : (term496 x') = (term117 x').
Proof. exact (TRANS (@lem2432392 x') (@lem2432435 x')). Qed.
Lemma lem2432437 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432438 (x' : int) : (term497 x') = (term498 x').
Proof. exact (MK_COMB (@lem2432437) (@lem2432436 x')). Qed.
Lemma lem2432439 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432440 (x' : int) : (term495 x') = (term499 x').
Proof. exact (MK_COMB (@lem2432438 x') (@lem2432439)). Qed.
Lemma lem2432441 (x' : int) : (term437 x') = (term499 x').
Proof. exact (TRANS (@lem2432381 x') (@lem2432440 x')). Qed.
Lemma lem2432442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432443 (x' : int) : (term427 x') = (term500 x').
Proof. exact (MK_COMB (@lem2432442) (@lem2432380 x')). Qed.
Lemma lem2432444 (x' : int) : (term438 x') = (term501 x').
Proof. exact (MK_COMB (@lem2432443 x') (@lem2432441 x')). Qed.
Lemma lem2432445 (x : int) : (term452 x) = (term502 x).
Proof. exact (@lem1988287 term54 (term449 x)). Qed.
Lemma lem2432459 (x : int) : (term503 x) = (term504 x).
Proof. exact (@lem1982792 term54 (term449 x)). Qed.
Lemma lem2432460 (x : int) : (term505 x) = (term506 x).
Proof. exact (@lem1982781 (term446 x) term97 term42). Qed.
Lemma lem2432462 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2432463 : term42 = term94.
Proof. exact (@lem2432462 term43). Qed.
Lemma lem2432465 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2432466 : term97 = term98.
Proof. exact (@lem2432465 term43). Qed.
Lemma lem2432467 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2432468 : term99 = term100.
Proof. exact (MK_COMB (@lem2432467) (@lem2432466)). Qed.
Lemma lem2432469 : term101 = term102.
Proof. exact (MK_COMB (@lem2432468) (@lem2432463)). Qed.
Lemma lem2432470 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2432472 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2432473 : term106 = term107.
Proof. exact (@lem2432472 term43 term43). Qed.
Lemma lem2432474 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432475 : term109 = term43.
Proof. exact (EQ_MP (@lem2432474) (@lem940073)). Qed.
Lemma lem2432476 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432477 : term107 = term42.
Proof. exact (MK_COMB (@lem2432476) (@lem2432475)). Qed.
Lemma lem2432478 : term106 = term42.
Proof. exact (TRANS (@lem2432473) (@lem2432477)). Qed.
Lemma lem2432480 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2432481 : term101 = term112.
Proof. exact (@lem2432480 term43 term43). Qed.
Lemma lem2432482 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432483 : term109 = term43.
Proof. exact (EQ_MP (@lem2432482) (@lem940073)). Qed.
Lemma lem2432484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432485 : term107 = term42.
Proof. exact (MK_COMB (@lem2432484) (@lem2432483)). Qed.
Lemma lem2432486 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2432487 : term112 = term97.
Proof. exact (MK_COMB (@lem2432486) (@lem2432485)). Qed.
Lemma lem2432488 : term101 = term97.
Proof. exact (TRANS (@lem2432481) (@lem2432487)). Qed.
Lemma lem2432489 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2432490 : term113 = term114.
Proof. exact (MK_COMB (@lem2432489) (@lem2432488)). Qed.
Lemma lem2432491 : term103 = term98.
Proof. exact (MK_COMB (@lem2432490) (@lem2432478)). Qed.
Lemma lem2432492 : term102 = term98.
Proof. exact (TRANS (@lem2432470) (@lem2432491)). Qed.
Lemma lem2432493 : term101 = term98.
Proof. exact (TRANS (@lem2432469) (@lem2432492)). Qed.
Lemma lem2432495 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2432496 : term98 = term97.
Proof. exact (@lem2432495 term97). Qed.
Lemma lem2432497 : term101 = term97.
Proof. exact (TRANS (@lem2432493) (@lem2432496)). Qed.
Lemma lem2432500 (x : int) : (term507 x) = (term507 x).
Proof. exact (eq_refl (term507 x)). Qed.
Lemma lem2432501 (x : int) : (term506 x) = (term508 x).
Proof. exact (MK_COMB (@lem2432500 x) (@lem2432497)). Qed.
Lemma lem2432502 (x : int) : (term505 x) = (term508 x).
Proof. exact (TRANS (@lem2432460 x) (@lem2432501 x)). Qed.
Lemma lem2432503 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem2432504 (x : int) : (term504 x) = (term509 x).
Proof. exact (MK_COMB (@lem2432503) (@lem2432502 x)). Qed.
Lemma lem2432505 (x : int) : (term509 x) = (term508 x).
Proof. exact (@lem1982721 (term508 x)). Qed.
Lemma lem2432506 (x : int) : (term504 x) = (term508 x).
Proof. exact (TRANS (@lem2432504 x) (@lem2432505 x)). Qed.
Lemma lem2432508 (x : int) : (term503 x) = (term508 x).
Proof. exact (TRANS (@lem2432459 x) (@lem2432506 x)). Qed.
Lemma lem2432509 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432510 (x : int) : (term510 x) = (term511 x).
Proof. exact (MK_COMB (@lem2432509) (@lem2432508 x)). Qed.
Lemma lem2432511 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432512 (x : int) : (term502 x) = (term512 x).
Proof. exact (MK_COMB (@lem2432510 x) (@lem2432511)). Qed.
Lemma lem2432513 (x : int) : (term452 x) = (term512 x).
Proof. exact (TRANS (@lem2432445 x) (@lem2432512 x)). Qed.
Lemma lem2432514 (x' : int) : (term469 x') = (term513 x').
Proof. exact (@lem1988287 term54 (term466 x')). Qed.
Lemma lem2432515 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2432523 (x' : int) : (term463 x') = (term514 x').
Proof. exact (@lem1982792 (term446 x') term42). Qed.
Lemma lem2432525 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2432526 : term42 = term94.
Proof. exact (@lem2432525 term43). Qed.
Lemma lem2432528 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2432529 : term97 = term98.
Proof. exact (@lem2432528 term43). Qed.
Lemma lem2432530 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2432531 : term99 = term100.
Proof. exact (MK_COMB (@lem2432530) (@lem2432529)). Qed.
Lemma lem2432532 : term101 = term102.
Proof. exact (MK_COMB (@lem2432531) (@lem2432526)). Qed.
Lemma lem2432533 : term102 = term103.
Proof. exact (@lem1981613 term97 term42 term42 term42). Qed.
Lemma lem2432535 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2432536 : term106 = term107.
Proof. exact (@lem2432535 term43 term43). Qed.
Lemma lem2432537 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432538 : term109 = term43.
Proof. exact (EQ_MP (@lem2432537) (@lem940073)). Qed.
Lemma lem2432539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432540 : term107 = term42.
Proof. exact (MK_COMB (@lem2432539) (@lem2432538)). Qed.
Lemma lem2432541 : term106 = term42.
Proof. exact (TRANS (@lem2432536) (@lem2432540)). Qed.
Lemma lem2432543 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2432544 : term101 = term112.
Proof. exact (@lem2432543 term43 term43). Qed.
Lemma lem2432545 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432546 : term109 = term43.
Proof. exact (EQ_MP (@lem2432545) (@lem940073)). Qed.
Lemma lem2432547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432548 : term107 = term42.
Proof. exact (MK_COMB (@lem2432547) (@lem2432546)). Qed.
Lemma lem2432549 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2432550 : term112 = term97.
Proof. exact (MK_COMB (@lem2432549) (@lem2432548)). Qed.
Lemma lem2432551 : term101 = term97.
Proof. exact (TRANS (@lem2432544) (@lem2432550)). Qed.
Lemma lem2432552 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2432553 : term113 = term114.
Proof. exact (MK_COMB (@lem2432552) (@lem2432551)). Qed.
Lemma lem2432554 : term103 = term98.
Proof. exact (MK_COMB (@lem2432553) (@lem2432541)). Qed.
Lemma lem2432555 : term102 = term98.
Proof. exact (TRANS (@lem2432533) (@lem2432554)). Qed.
Lemma lem2432556 : term101 = term98.
Proof. exact (TRANS (@lem2432532) (@lem2432555)). Qed.
Lemma lem2432558 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2432559 : term98 = term97.
Proof. exact (@lem2432558 term97). Qed.
Lemma lem2432560 : term101 = term97.
Proof. exact (TRANS (@lem2432556) (@lem2432559)). Qed.
Lemma lem2432561 (x' : int) : (term448 x') = (term448 x').
Proof. exact (eq_refl (term448 x')). Qed.
Lemma lem2432564 (x' : int) : (term514 x') = (term515 x').
Proof. exact (MK_COMB (@lem2432561 x') (@lem2432560)). Qed.
Lemma lem2432566 (x' : int) : (term463 x') = (term515 x').
Proof. exact (TRANS (@lem2432523 x') (@lem2432564 x')). Qed.
Lemma lem2432567 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2432568 (x' : int) : (term465 x') = (term516 x').
Proof. exact (MK_COMB (@lem2432567) (@lem2432566 x')). Qed.
Lemma lem2432569 (x' : int) : (term466 x') = (term517 x').
Proof. exact (MK_COMB (@lem2432568 x') (@lem2432515)). Qed.
Lemma lem2432570 (x' : int) : (term517 x') = (term518 x').
Proof. exact (@lem1982755 (term446 x') term97 term42). Qed.
Lemma lem2432572 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2432573 : term42 = term94.
Proof. exact (@lem2432572 term43). Qed.
Lemma lem2432575 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2432576 : term97 = term98.
Proof. exact (@lem2432575 term43). Qed.
Lemma lem2432577 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2432578 : term215 = term216.
Proof. exact (MK_COMB (@lem2432577) (@lem2432576)). Qed.
Lemma lem2432579 : term217 = term218.
Proof. exact (MK_COMB (@lem2432578) (@lem2432573)). Qed.
Lemma lem2432580 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2432582 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2432583 : term184 = term190.
Proof. exact (@lem2432582 (NUMERAL 0) term43). Qed.
Lemma lem2432584 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2432585 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2432586 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2432585 h1) (fun h1 : term190 = True => @lem2432584)). Qed.
Lemma lem2432587 : term190 = True.
Proof. exact (EQ_MP (@lem2432586) (@lem2432584)). Qed.
Lemma lem2432588 : term184 = True.
Proof. exact (TRANS (@lem2432583) (@lem2432587)). Qed.
Lemma lem2432589 : True = term184.
Proof. exact (SYM (@lem2432588)). Qed.
Lemma lem2432590 : term184.
Proof. exact (EQ_MP (@lem2432589) (@lem0)). Qed.
Lemma lem2432591 : term220.
Proof. exact (@lem2432580 (@lem2432590)). Qed.
Lemma lem2432593 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2432594 : term184 = term190.
Proof. exact (@lem2432593 (NUMERAL 0) term43). Qed.
Lemma lem2432595 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2432596 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2432597 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2432596 h1) (fun h1 : term190 = True => @lem2432595)). Qed.
Lemma lem2432598 : term190 = True.
Proof. exact (EQ_MP (@lem2432597) (@lem2432595)). Qed.
Lemma lem2432599 : term184 = True.
Proof. exact (TRANS (@lem2432594) (@lem2432598)). Qed.
Lemma lem2432600 : True = term184.
Proof. exact (SYM (@lem2432599)). Qed.
Lemma lem2432601 : term184.
Proof. exact (EQ_MP (@lem2432600) (@lem0)). Qed.
Lemma lem2432602 : term221.
Proof. exact (@lem2432591 (@lem2432601)). Qed.
Lemma lem2432604 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2432605 : term184 = term190.
Proof. exact (@lem2432604 (NUMERAL 0) term43). Qed.
Lemma lem2432606 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2432607 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2432608 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2432607 h1) (fun h1 : term190 = True => @lem2432606)). Qed.
Lemma lem2432609 : term190 = True.
Proof. exact (EQ_MP (@lem2432608) (@lem2432606)). Qed.
Lemma lem2432610 : term184 = True.
Proof. exact (TRANS (@lem2432605) (@lem2432609)). Qed.
Lemma lem2432611 : True = term184.
Proof. exact (SYM (@lem2432610)). Qed.
Lemma lem2432612 : term184.
Proof. exact (EQ_MP (@lem2432611) (@lem0)). Qed.
Lemma lem2432613 : term222.
Proof. exact (@lem2432602 (@lem2432612)). Qed.
Lemma lem2432615 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2432616 : term106 = term107.
Proof. exact (@lem2432615 term43 term43). Qed.
Lemma lem2432617 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432618 : term109 = term43.
Proof. exact (EQ_MP (@lem2432617) (@lem940073)). Qed.
Lemma lem2432619 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432620 : term107 = term42.
Proof. exact (MK_COMB (@lem2432619) (@lem2432618)). Qed.
Lemma lem2432621 : term106 = term42.
Proof. exact (TRANS (@lem2432616) (@lem2432620)). Qed.
Lemma lem2432623 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2432624 : term101 = term112.
Proof. exact (@lem2432623 term43 term43). Qed.
Lemma lem2432625 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432626 : term109 = term43.
Proof. exact (EQ_MP (@lem2432625) (@lem940073)). Qed.
Lemma lem2432627 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432628 : term107 = term42.
Proof. exact (MK_COMB (@lem2432627) (@lem2432626)). Qed.
Lemma lem2432629 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2432630 : term112 = term97.
Proof. exact (MK_COMB (@lem2432629) (@lem2432628)). Qed.
Lemma lem2432631 : term101 = term97.
Proof. exact (TRANS (@lem2432624) (@lem2432630)). Qed.
Lemma lem2432632 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2432633 : term223 = term215.
Proof. exact (MK_COMB (@lem2432632) (@lem2432631)). Qed.
Lemma lem2432634 : term224 = term217.
Proof. exact (MK_COMB (@lem2432633) (@lem2432621)). Qed.
Lemma lem2432636 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2432637 : term217 = term54.
Proof. exact (@lem2432636 term43). Qed.
Lemma lem2432638 : term224 = term54.
Proof. exact (TRANS (@lem2432634) (@lem2432637)). Qed.
Lemma lem2432639 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2432640 : term226 = term227.
Proof. exact (MK_COMB (@lem2432639) (@lem2432638)). Qed.
Lemma lem2432641 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2432642 : term228 = term195.
Proof. exact (MK_COMB (@lem2432640) (@lem2432641)). Qed.
Lemma lem2432644 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2432645 : term195 = term54.
Proof. exact (@lem2432644 term43). Qed.
Lemma lem2432646 : term228 = term54.
Proof. exact (TRANS (@lem2432642) (@lem2432645)). Qed.
Lemma lem2432648 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2432649 : term106 = term107.
Proof. exact (@lem2432648 term43 term43). Qed.
Lemma lem2432650 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2432651 : term109 = term43.
Proof. exact (EQ_MP (@lem2432650) (@lem940073)). Qed.
Lemma lem2432652 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2432653 : term107 = term42.
Proof. exact (MK_COMB (@lem2432652) (@lem2432651)). Qed.
Lemma lem2432654 : term106 = term42.
Proof. exact (TRANS (@lem2432649) (@lem2432653)). Qed.
Lemma lem2432655 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2432656 : term229 = term195.
Proof. exact (MK_COMB (@lem2432655) (@lem2432654)). Qed.
Lemma lem2432658 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2432659 : term195 = term54.
Proof. exact (@lem2432658 term43). Qed.
Lemma lem2432660 : term229 = term54.
Proof. exact (TRANS (@lem2432656) (@lem2432659)). Qed.
Lemma lem2432661 : term54 = term229.
Proof. exact (SYM (@lem2432660)). Qed.
Lemma lem2432662 : term228 = term229.
Proof. exact (TRANS (@lem2432646) (@lem2432661)). Qed.
Lemma lem2432663 : term218 = term170.
Proof. exact (@lem2432613 (@lem2432662)). Qed.
Lemma lem2432664 : term217 = term170.
Proof. exact (TRANS (@lem2432579) (@lem2432663)). Qed.
Lemma lem2432666 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2432667 : term170 = term54.
Proof. exact (@lem2432666 term54). Qed.
Lemma lem2432668 : term217 = term54.
Proof. exact (TRANS (@lem2432664) (@lem2432667)). Qed.
Lemma lem2432669 (x' : int) : (term448 x') = (term448 x').
Proof. exact (eq_refl (term448 x')). Qed.
Lemma lem2432670 (x' : int) : (term518 x') = (term519 x').
Proof. exact (MK_COMB (@lem2432669 x') (@lem2432668)). Qed.
Lemma lem2432671 (x' : int) : (term517 x') = (term519 x').
Proof. exact (TRANS (@lem2432570 x') (@lem2432670 x')). Qed.
Lemma lem2432672 (x' : int) : (term519 x') = (term446 x').
Proof. exact (@lem1982723 (term446 x')). Qed.
Lemma lem2432673 (x' : int) : (term517 x') = (term446 x').
Proof. exact (TRANS (@lem2432671 x') (@lem2432672 x')). Qed.
Lemma lem2432674 (x' : int) : (term466 x') = (term446 x').
Proof. exact (TRANS (@lem2432569 x') (@lem2432673 x')). Qed.
Lemma lem2432677 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem2432678 (x' : int) : (term520 x') = (term521 x').
Proof. exact (MK_COMB (@lem2432677) (@lem2432674 x')). Qed.
Lemma lem2432679 (x' : int) : (term521 x') = (term522 x').
Proof. exact (@lem1982792 term54 (term446 x')). Qed.
Lemma lem2432684 (x' : int) : (term522 x') = (term523 x').
Proof. exact (@lem1982721 (term523 x')). Qed.
Lemma lem2432685 (x' : int) : (term521 x') = (term523 x').
Proof. exact (TRANS (@lem2432679 x') (@lem2432684 x')). Qed.
Lemma lem2432686 (x' : int) : (term520 x') = (term523 x').
Proof. exact (TRANS (@lem2432678 x') (@lem2432685 x')). Qed.
Lemma lem2432687 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432688 (x' : int) : (term524 x') = (term525 x').
Proof. exact (MK_COMB (@lem2432687) (@lem2432686 x')). Qed.
Lemma lem2432689 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432690 (x' : int) : (term513 x') = (term526 x').
Proof. exact (MK_COMB (@lem2432688 x') (@lem2432689)). Qed.
Lemma lem2432691 (x' : int) : (term469 x') = (term526 x').
Proof. exact (TRANS (@lem2432514 x') (@lem2432690 x')). Qed.
Lemma lem2432692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432693 (x : int) : (term471 x) = (term527 x).
Proof. exact (MK_COMB (@lem2432692) (@lem2432513 x)). Qed.
Lemma lem2432694 (x : int) (x' : int) : (term472 x x') = (term528 x x').
Proof. exact (MK_COMB (@lem2432693 x) (@lem2432691 x')). Qed.
Lemma lem2432695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432696 (x' : int) : (term473 x') = (term529 x').
Proof. exact (MK_COMB (@lem2432695) (@lem2432444 x')). Qed.
Lemma lem2432697 (x : int) (x' : int) : (term474 x x') = (term530 x x').
Proof. exact (MK_COMB (@lem2432696 x') (@lem2432694 x x')). Qed.
Lemma lem2432698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432699 (x : int) : (term473 x) = (term529 x).
Proof. exact (MK_COMB (@lem2432698) (@lem2432313 x)). Qed.
Lemma lem2432700 (x : int) (x' : int) : (term475 x x') = (term531 x x').
Proof. exact (MK_COMB (@lem2432699 x) (@lem2432697 x x')). Qed.
Lemma lem2432701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432702 (x : int) (x' : int) (y : int) : (term476 y x x') = (term532 x x' y).
Proof. exact (MK_COMB (@lem2432701) (@lem2432182 x x' y)). Qed.
Lemma lem2432703 (y : int) (x : int) (x' : int) : (term477 y x x') = (term533 y x x').
Proof. exact (MK_COMB (@lem2432702 x x' y) (@lem2432700 x x')). Qed.
Lemma lem2432710 (y : int) (x : int) (x' : int) : (term478 y x x') = (term533 y x x').
Proof. exact (TRANS (@lem2432157 y x x') (@lem2432703 y x x')). Qed.
Lemma lem2432724 (x : int) (x' : int) : (term530 x x') = (term534 x x').
Proof. exact (@lem19158 (term512 x) (term501 x') (term526 x')). Qed.
Lemma lem2432731 (x' : int) : (term535 x') = (term536 x').
Proof. exact (@lem19367 (term494 x') (term499 x') (term526 x')). Qed.
Lemma lem2432738 (x' : int) (x : int) : (term537 x' x) = (term538 x' x).
Proof. exact (@lem19367 (term494 x') (term499 x') (term512 x)). Qed.
Lemma lem2432739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432740 (x' : int) (x : int) : (term539 x' x) = (term540 x' x).
Proof. exact (MK_COMB (@lem2432739) (@lem2432738 x' x)). Qed.
Lemma lem2432741 (x : int) (x' : int) : (term534 x x') = (term541 x x').
Proof. exact (MK_COMB (@lem2432740 x' x) (@lem2432731 x')). Qed.
Lemma lem2432743 (x : int) (x' : int) : (term530 x x') = (term541 x x').
Proof. exact (TRANS (@lem2432724 x x') (@lem2432741 x x')). Qed.
Lemma lem2432750 (x : int) : (term529 x) = (term529 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem2432751 (x : int) (x' : int) : (term531 x x') = (term542 x x').
Proof. exact (MK_COMB (@lem2432750 x) (@lem2432743 x x')). Qed.
Lemma lem2432752 (x : int) (x' : int) : (term542 x x') = (term543 x x').
Proof. exact (@lem19158 (term538 x' x) (term501 x) (term536 x')). Qed.
Lemma lem2432753 (x : int) (x' : int) : (term544 x x') = (term545 x x').
Proof. exact (@lem19158 (term546 x') (term501 x) (term547 x')). Qed.
Lemma lem2432760 (x : int) (x' : int) : (term548 x x') = (term549 x x').
Proof. exact (@lem19367 (term494 x) (term499 x) (term547 x')). Qed.
Lemma lem2432767 (x : int) (x' : int) : (term550 x x') = (term551 x x').
Proof. exact (@lem19367 (term494 x) (term499 x) (term546 x')). Qed.
Lemma lem2432768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432769 (x : int) (x' : int) : (term552 x x') = (term553 x x').
Proof. exact (MK_COMB (@lem2432768) (@lem2432767 x x')). Qed.
Lemma lem2432770 (x : int) (x' : int) : (term545 x x') = (term554 x x').
Proof. exact (MK_COMB (@lem2432769 x x') (@lem2432760 x x')). Qed.
Lemma lem2432771 (x : int) (x' : int) : (term544 x x') = (term554 x x').
Proof. exact (TRANS (@lem2432753 x x') (@lem2432770 x x')). Qed.
Lemma lem2432772 (x' : int) (x : int) : (term555 x' x) = (term556 x' x).
Proof. exact (@lem19158 (term557 x' x) (term501 x) (term558 x' x)). Qed.
Lemma lem2432779 (x' : int) (x : int) : (term559 x' x) = (term560 x' x).
Proof. exact (@lem19367 (term494 x) (term499 x) (term558 x' x)). Qed.
Lemma lem2432786 (x' : int) (x : int) : (term561 x' x) = (term562 x' x).
Proof. exact (@lem19367 (term494 x) (term499 x) (term557 x' x)). Qed.
Lemma lem2432787 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432788 (x' : int) (x : int) : (term563 x' x) = (term564 x' x).
Proof. exact (MK_COMB (@lem2432787) (@lem2432786 x' x)). Qed.
Lemma lem2432789 (x' : int) (x : int) : (term556 x' x) = (term565 x' x).
Proof. exact (MK_COMB (@lem2432788 x' x) (@lem2432779 x' x)). Qed.
Lemma lem2432790 (x' : int) (x : int) : (term555 x' x) = (term565 x' x).
Proof. exact (TRANS (@lem2432772 x' x) (@lem2432789 x' x)). Qed.
Lemma lem2432791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432792 (x' : int) (x : int) : (term566 x' x) = (term567 x' x).
Proof. exact (MK_COMB (@lem2432791) (@lem2432790 x' x)). Qed.
Lemma lem2432793 (x : int) (x' : int) : (term543 x x') = (term568 x x').
Proof. exact (MK_COMB (@lem2432792 x' x) (@lem2432771 x x')). Qed.
Lemma lem2432794 (x : int) (x' : int) : (term542 x x') = (term568 x x').
Proof. exact (TRANS (@lem2432752 x x') (@lem2432793 x x')). Qed.
Lemma lem2432795 (x : int) (x' : int) : (term531 x x') = (term568 x x').
Proof. exact (TRANS (@lem2432751 x x') (@lem2432794 x x')). Qed.
Lemma lem2432798 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2432799 (y : int) (x : int) (x' : int) : (term533 y x x') = (term569 y x x').
Proof. exact (MK_COMB (@lem2432798 x x' y) (@lem2432795 x x')). Qed.
Lemma lem2432800 (y : int) (x : int) (x' : int) : (term569 y x x') = (term570 y x x').
Proof. exact (@lem19158 (term565 x' x) ((term481 x x' y) = term54) (term554 x x')). Qed.
Lemma lem2432801 (y : int) (x : int) (x' : int) : (term571 y x x') = (term572 y x x').
Proof. exact (@lem19158 (term551 x x') ((term481 x x' y) = term54) (term549 x x')). Qed.
Lemma lem2432808 (y : int) (x : int) (x' : int) : (term573 y x x') = (term574 y x x').
Proof. exact (@lem19158 (term575 x x') ((term481 x x' y) = term54) (term576 x x')). Qed.
Lemma lem2432815 (y : int) (x : int) (x' : int) : (term577 y x x') = (term578 y x x').
Proof. exact (@lem19158 (term579 x x') ((term481 x x' y) = term54) (term580 x x')). Qed.
Lemma lem2432816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432817 (y : int) (x : int) (x' : int) : (term581 y x x') = (term582 y x x').
Proof. exact (MK_COMB (@lem2432816) (@lem2432815 y x x')). Qed.
Lemma lem2432818 (y : int) (x : int) (x' : int) : (term572 y x x') = (term583 y x x').
Proof. exact (MK_COMB (@lem2432817 y x x') (@lem2432808 y x x')). Qed.
Lemma lem2432819 (y : int) (x : int) (x' : int) : (term571 y x x') = (term583 y x x').
Proof. exact (TRANS (@lem2432801 y x x') (@lem2432818 y x x')). Qed.
Lemma lem2432820 (y : int) (x' : int) (x : int) : (term584 y x' x) = (term585 y x' x).
Proof. exact (@lem19158 (term562 x' x) ((term481 x x' y) = term54) (term560 x' x)). Qed.
Lemma lem2432827 (y : int) (x' : int) (x : int) : (term586 y x' x) = (term587 y x' x).
Proof. exact (@lem19158 (term588 x' x) ((term481 x x' y) = term54) (term589 x' x)). Qed.
Lemma lem2432834 (y : int) (x' : int) (x : int) : (term590 y x' x) = (term591 y x' x).
Proof. exact (@lem19158 (term592 x' x) ((term481 x x' y) = term54) (term593 x' x)). Qed.
Lemma lem2432835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432836 (y : int) (x' : int) (x : int) : (term594 y x' x) = (term595 y x' x).
Proof. exact (MK_COMB (@lem2432835) (@lem2432834 y x' x)). Qed.
Lemma lem2432837 (y : int) (x' : int) (x : int) : (term585 y x' x) = (term596 y x' x).
Proof. exact (MK_COMB (@lem2432836 y x' x) (@lem2432827 y x' x)). Qed.
Lemma lem2432838 (y : int) (x' : int) (x : int) : (term584 y x' x) = (term596 y x' x).
Proof. exact (TRANS (@lem2432820 y x' x) (@lem2432837 y x' x)). Qed.
Lemma lem2432839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432840 (y : int) (x' : int) (x : int) : (term597 y x' x) = (term598 y x' x).
Proof. exact (MK_COMB (@lem2432839) (@lem2432838 y x' x)). Qed.
Lemma lem2432841 (y : int) (x : int) (x' : int) : (term570 y x x') = (term599 y x x').
Proof. exact (MK_COMB (@lem2432840 y x' x) (@lem2432819 y x x')). Qed.
Lemma lem2432842 (y : int) (x : int) (x' : int) : (term569 y x x') = (term599 y x x').
Proof. exact (TRANS (@lem2432800 y x x') (@lem2432841 y x x')). Qed.
Lemma lem2432843 (y : int) (x : int) (x' : int) : (term533 y x x') = (term599 y x x').
Proof. exact (TRANS (@lem2432799 y x x') (@lem2432842 y x x')). Qed.
Lemma lem2432844 (y : int) (x : int) (x' : int) : (term478 y x x') = (term599 y x x').
Proof. exact (TRANS (@lem2432710 y x x') (@lem2432843 y x x')). Qed.
Lemma lem2432846 (a : real) (x : real) (r : real) : (term600 x a r) = (term601 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2432847 (x : int) : (term512 x) = (term602 x).
Proof. exact (@lem2432846 term97 (real_of_int x) term54). Qed.
Lemma lem2432854 (x : int) : (term144 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2432857 : term215 = term215.
Proof. exact (eq_refl term215). Qed.
Lemma lem2432858 (x : int) : (term603 x) = (term604 x).
Proof. exact (MK_COMB (@lem2432857) (@lem2432854 x)). Qed.
Lemma lem2432859 (x : int) : (term604 x) = (term117 x).
Proof. exact (@lem1982761 (real_of_int x) term97). Qed.
Lemma lem2432860 (x : int) : (term603 x) = (term117 x).
Proof. exact (TRANS (@lem2432858 x) (@lem2432859 x)). Qed.
Lemma lem2432861 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432862 (x : int) : (term605 x) = (term498 x).
Proof. exact (MK_COMB (@lem2432861) (@lem2432860 x)). Qed.
Lemma lem2432863 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432864 (x : int) : (term606 x) = (term499 x).
Proof. exact (MK_COMB (@lem2432862 x) (@lem2432863)). Qed.
Lemma lem2432877 (x : int) : (term607 x) = (term490 x).
Proof. exact (@lem1982761 (term121 x) term97). Qed.
Lemma lem2432878 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432879 (x : int) : (term608 x) = (term493 x).
Proof. exact (MK_COMB (@lem2432878) (@lem2432877 x)). Qed.
Lemma lem2432880 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432881 (x : int) : (term609 x) = (term494 x).
Proof. exact (MK_COMB (@lem2432879 x) (@lem2432880)). Qed.
Lemma lem2432882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432883 (x : int) : (term610 x) = (term611 x).
Proof. exact (MK_COMB (@lem2432882) (@lem2432881 x)). Qed.
Lemma lem2432884 (x : int) : (term602 x) = (term612 x).
Proof. exact (MK_COMB (@lem2432883 x) (@lem2432864 x)). Qed.
Lemma lem2432885 (x : int) : (term512 x) = (term612 x).
Proof. exact (TRANS (@lem2432847 x) (@lem2432884 x)). Qed.
Lemma lem2432886 (x' : int) : (term611 x') = (term611 x').
Proof. exact (eq_refl (term611 x')). Qed.
Lemma lem2432887 (x' : int) (x : int) : (term557 x' x) = (term613 x' x).
Proof. exact (MK_COMB (@lem2432886 x') (@lem2432885 x)). Qed.
Lemma lem2432888 (x : int) : (term611 x) = (term611 x).
Proof. exact (eq_refl (term611 x)). Qed.
Lemma lem2432889 (x' : int) (x : int) : (term592 x' x) = (term614 x' x).
Proof. exact (MK_COMB (@lem2432888 x) (@lem2432887 x' x)). Qed.
Lemma lem2432890 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2432893 (y : int) (x' : int) (x : int) : (term615 y x' x) = (term616 y x' x).
Proof. exact (MK_COMB (@lem2432890 x x' y) (@lem2432889 x' x)). Qed.
Lemma lem2432895 (a : real) (x : real) (r : real) : (term600 x a r) = (term601 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2432896 (x : int) : (term512 x) = (term602 x).
Proof. exact (@lem2432895 term97 (real_of_int x) term54). Qed.
Lemma lem2432903 (x : int) : (term144 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2432906 : term215 = term215.
Proof. exact (eq_refl term215). Qed.
Lemma lem2432907 (x : int) : (term603 x) = (term604 x).
Proof. exact (MK_COMB (@lem2432906) (@lem2432903 x)). Qed.
Lemma lem2432908 (x : int) : (term604 x) = (term117 x).
Proof. exact (@lem1982761 (real_of_int x) term97). Qed.
Lemma lem2432909 (x : int) : (term603 x) = (term117 x).
Proof. exact (TRANS (@lem2432907 x) (@lem2432908 x)). Qed.
Lemma lem2432910 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432911 (x : int) : (term605 x) = (term498 x).
Proof. exact (MK_COMB (@lem2432910) (@lem2432909 x)). Qed.
Lemma lem2432912 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432913 (x : int) : (term606 x) = (term499 x).
Proof. exact (MK_COMB (@lem2432911 x) (@lem2432912)). Qed.
Lemma lem2432926 (x : int) : (term607 x) = (term490 x).
Proof. exact (@lem1982761 (term121 x) term97). Qed.
Lemma lem2432927 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432928 (x : int) : (term608 x) = (term493 x).
Proof. exact (MK_COMB (@lem2432927) (@lem2432926 x)). Qed.
Lemma lem2432929 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432930 (x : int) : (term609 x) = (term494 x).
Proof. exact (MK_COMB (@lem2432928 x) (@lem2432929)). Qed.
Lemma lem2432931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432932 (x : int) : (term610 x) = (term611 x).
Proof. exact (MK_COMB (@lem2432931) (@lem2432930 x)). Qed.
Lemma lem2432933 (x : int) : (term602 x) = (term612 x).
Proof. exact (MK_COMB (@lem2432932 x) (@lem2432913 x)). Qed.
Lemma lem2432934 (x : int) : (term512 x) = (term612 x).
Proof. exact (TRANS (@lem2432896 x) (@lem2432933 x)). Qed.
Lemma lem2432935 (x' : int) : (term611 x') = (term611 x').
Proof. exact (eq_refl (term611 x')). Qed.
Lemma lem2432936 (x' : int) (x : int) : (term557 x' x) = (term613 x' x).
Proof. exact (MK_COMB (@lem2432935 x') (@lem2432934 x)). Qed.
Lemma lem2432937 (x : int) : (term617 x) = (term617 x).
Proof. exact (eq_refl (term617 x)). Qed.
Lemma lem2432938 (x' : int) (x : int) : (term593 x' x) = (term618 x' x).
Proof. exact (MK_COMB (@lem2432937 x) (@lem2432936 x' x)). Qed.
Lemma lem2432939 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2432942 (y : int) (x' : int) (x : int) : (term619 y x' x) = (term620 y x' x).
Proof. exact (MK_COMB (@lem2432939 x x' y) (@lem2432938 x' x)). Qed.
Lemma lem2432943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2432944 (y : int) (x' : int) (x : int) : (term621 y x' x) = (term622 y x' x).
Proof. exact (MK_COMB (@lem2432943) (@lem2432893 y x' x)). Qed.
Lemma lem2432945 (y : int) (x' : int) (x : int) : (term591 y x' x) = (term623 y x' x).
Proof. exact (MK_COMB (@lem2432944 y x' x) (@lem2432942 y x' x)). Qed.
Lemma lem2432947 (a : real) (x : real) (r : real) : (term600 x a r) = (term601 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2432948 (x : int) : (term512 x) = (term602 x).
Proof. exact (@lem2432947 term97 (real_of_int x) term54). Qed.
Lemma lem2432955 (x : int) : (term144 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2432958 : term215 = term215.
Proof. exact (eq_refl term215). Qed.
Lemma lem2432959 (x : int) : (term603 x) = (term604 x).
Proof. exact (MK_COMB (@lem2432958) (@lem2432955 x)). Qed.
Lemma lem2432960 (x : int) : (term604 x) = (term117 x).
Proof. exact (@lem1982761 (real_of_int x) term97). Qed.
Lemma lem2432961 (x : int) : (term603 x) = (term117 x).
Proof. exact (TRANS (@lem2432959 x) (@lem2432960 x)). Qed.
Lemma lem2432962 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432963 (x : int) : (term605 x) = (term498 x).
Proof. exact (MK_COMB (@lem2432962) (@lem2432961 x)). Qed.
Lemma lem2432964 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432965 (x : int) : (term606 x) = (term499 x).
Proof. exact (MK_COMB (@lem2432963 x) (@lem2432964)). Qed.
Lemma lem2432978 (x : int) : (term607 x) = (term490 x).
Proof. exact (@lem1982761 (term121 x) term97). Qed.
Lemma lem2432979 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2432980 (x : int) : (term608 x) = (term493 x).
Proof. exact (MK_COMB (@lem2432979) (@lem2432978 x)). Qed.
Lemma lem2432981 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2432982 (x : int) : (term609 x) = (term494 x).
Proof. exact (MK_COMB (@lem2432980 x) (@lem2432981)). Qed.
Lemma lem2432983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2432984 (x : int) : (term610 x) = (term611 x).
Proof. exact (MK_COMB (@lem2432983) (@lem2432982 x)). Qed.
Lemma lem2432985 (x : int) : (term602 x) = (term612 x).
Proof. exact (MK_COMB (@lem2432984 x) (@lem2432965 x)). Qed.
Lemma lem2432986 (x : int) : (term512 x) = (term612 x).
Proof. exact (TRANS (@lem2432948 x) (@lem2432985 x)). Qed.
Lemma lem2432987 (x' : int) : (term617 x') = (term617 x').
Proof. exact (eq_refl (term617 x')). Qed.
Lemma lem2432988 (x' : int) (x : int) : (term558 x' x) = (term624 x' x).
Proof. exact (MK_COMB (@lem2432987 x') (@lem2432986 x)). Qed.
Lemma lem2432989 (x : int) : (term611 x) = (term611 x).
Proof. exact (eq_refl (term611 x)). Qed.
Lemma lem2432990 (x' : int) (x : int) : (term588 x' x) = (term625 x' x).
Proof. exact (MK_COMB (@lem2432989 x) (@lem2432988 x' x)). Qed.
Lemma lem2432991 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2432994 (y : int) (x' : int) (x : int) : (term626 y x' x) = (term627 y x' x).
Proof. exact (MK_COMB (@lem2432991 x x' y) (@lem2432990 x' x)). Qed.
Lemma lem2432996 (a : real) (x : real) (r : real) : (term600 x a r) = (term601 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2432997 (x : int) : (term512 x) = (term602 x).
Proof. exact (@lem2432996 term97 (real_of_int x) term54). Qed.
Lemma lem2433004 (x : int) : (term144 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2433007 : term215 = term215.
Proof. exact (eq_refl term215). Qed.
Lemma lem2433008 (x : int) : (term603 x) = (term604 x).
Proof. exact (MK_COMB (@lem2433007) (@lem2433004 x)). Qed.
Lemma lem2433009 (x : int) : (term604 x) = (term117 x).
Proof. exact (@lem1982761 (real_of_int x) term97). Qed.
Lemma lem2433010 (x : int) : (term603 x) = (term117 x).
Proof. exact (TRANS (@lem2433008 x) (@lem2433009 x)). Qed.
Lemma lem2433011 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433012 (x : int) : (term605 x) = (term498 x).
Proof. exact (MK_COMB (@lem2433011) (@lem2433010 x)). Qed.
Lemma lem2433013 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433014 (x : int) : (term606 x) = (term499 x).
Proof. exact (MK_COMB (@lem2433012 x) (@lem2433013)). Qed.
Lemma lem2433027 (x : int) : (term607 x) = (term490 x).
Proof. exact (@lem1982761 (term121 x) term97). Qed.
Lemma lem2433028 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433029 (x : int) : (term608 x) = (term493 x).
Proof. exact (MK_COMB (@lem2433028) (@lem2433027 x)). Qed.
Lemma lem2433030 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433031 (x : int) : (term609 x) = (term494 x).
Proof. exact (MK_COMB (@lem2433029 x) (@lem2433030)). Qed.
Lemma lem2433032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2433033 (x : int) : (term610 x) = (term611 x).
Proof. exact (MK_COMB (@lem2433032) (@lem2433031 x)). Qed.
Lemma lem2433034 (x : int) : (term602 x) = (term612 x).
Proof. exact (MK_COMB (@lem2433033 x) (@lem2433014 x)). Qed.
Lemma lem2433035 (x : int) : (term512 x) = (term612 x).
Proof. exact (TRANS (@lem2432997 x) (@lem2433034 x)). Qed.
Lemma lem2433036 (x' : int) : (term617 x') = (term617 x').
Proof. exact (eq_refl (term617 x')). Qed.
Lemma lem2433037 (x' : int) (x : int) : (term558 x' x) = (term624 x' x).
Proof. exact (MK_COMB (@lem2433036 x') (@lem2433035 x)). Qed.
Lemma lem2433038 (x : int) : (term617 x) = (term617 x).
Proof. exact (eq_refl (term617 x)). Qed.
Lemma lem2433039 (x' : int) (x : int) : (term589 x' x) = (term628 x' x).
Proof. exact (MK_COMB (@lem2433038 x) (@lem2433037 x' x)). Qed.
Lemma lem2433040 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2433043 (y : int) (x' : int) (x : int) : (term629 y x' x) = (term630 y x' x).
Proof. exact (MK_COMB (@lem2433040 x x' y) (@lem2433039 x' x)). Qed.
Lemma lem2433044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2433045 (y : int) (x' : int) (x : int) : (term631 y x' x) = (term632 y x' x).
Proof. exact (MK_COMB (@lem2433044) (@lem2432994 y x' x)). Qed.
Lemma lem2433046 (y : int) (x' : int) (x : int) : (term587 y x' x) = (term633 y x' x).
Proof. exact (MK_COMB (@lem2433045 y x' x) (@lem2433043 y x' x)). Qed.
Lemma lem2433047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2433048 (y : int) (x' : int) (x : int) : (term595 y x' x) = (term634 y x' x).
Proof. exact (MK_COMB (@lem2433047) (@lem2432945 y x' x)). Qed.
Lemma lem2433049 (y : int) (x' : int) (x : int) : (term596 y x' x) = (term635 y x' x).
Proof. exact (MK_COMB (@lem2433048 y x' x) (@lem2433046 y x' x)). Qed.
Lemma lem2433051 (x : real) (r : real) : (term636 x r) = (term637 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2433052 (x' : int) : (term526 x') = (term638 x').
Proof. exact (@lem2433051 (real_of_int x') term54). Qed.
Lemma lem2433059 (x' : int) : (term144 x') = (real_of_int x').
Proof. exact (@lem1982733 (real_of_int x')). Qed.
Lemma lem2433060 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433061 (x' : int) : (term639 x') = (term640 x').
Proof. exact (MK_COMB (@lem2433060) (@lem2433059 x')). Qed.
Lemma lem2433062 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433063 (x' : int) : (term641 x') = (term642 x').
Proof. exact (MK_COMB (@lem2433061 x') (@lem2433062)). Qed.
Lemma lem2433076 (x' : int) : (term643 x') = (term643 x').
Proof. exact (eq_refl (term643 x')). Qed.
Lemma lem2433077 (x' : int) : (term638 x') = (term644 x').
Proof. exact (MK_COMB (@lem2433076 x') (@lem2433063 x')). Qed.
Lemma lem2433078 (x' : int) : (term526 x') = (term644 x').
Proof. exact (TRANS (@lem2433052 x') (@lem2433077 x')). Qed.
Lemma lem2433079 (x' : int) : (term611 x') = (term611 x').
Proof. exact (eq_refl (term611 x')). Qed.
Lemma lem2433080 (x' : int) : (term546 x') = (term645 x').
Proof. exact (MK_COMB (@lem2433079 x') (@lem2433078 x')). Qed.
Lemma lem2433081 (x : int) : (term611 x) = (term611 x).
Proof. exact (eq_refl (term611 x)). Qed.
Lemma lem2433082 (x : int) (x' : int) : (term579 x x') = (term646 x x').
Proof. exact (MK_COMB (@lem2433081 x) (@lem2433080 x')). Qed.
Lemma lem2433083 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2433086 (y : int) (x : int) (x' : int) : (term647 y x x') = (term648 y x x').
Proof. exact (MK_COMB (@lem2433083 x x' y) (@lem2433082 x x')). Qed.
Lemma lem2433088 (x : real) (r : real) : (term636 x r) = (term637 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2433089 (x' : int) : (term526 x') = (term638 x').
Proof. exact (@lem2433088 (real_of_int x') term54). Qed.
Lemma lem2433096 (x' : int) : (term144 x') = (real_of_int x').
Proof. exact (@lem1982733 (real_of_int x')). Qed.
Lemma lem2433097 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433098 (x' : int) : (term639 x') = (term640 x').
Proof. exact (MK_COMB (@lem2433097) (@lem2433096 x')). Qed.
Lemma lem2433099 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433100 (x' : int) : (term641 x') = (term642 x').
Proof. exact (MK_COMB (@lem2433098 x') (@lem2433099)). Qed.
Lemma lem2433113 (x' : int) : (term643 x') = (term643 x').
Proof. exact (eq_refl (term643 x')). Qed.
Lemma lem2433114 (x' : int) : (term638 x') = (term644 x').
Proof. exact (MK_COMB (@lem2433113 x') (@lem2433100 x')). Qed.
Lemma lem2433115 (x' : int) : (term526 x') = (term644 x').
Proof. exact (TRANS (@lem2433089 x') (@lem2433114 x')). Qed.
Lemma lem2433116 (x' : int) : (term611 x') = (term611 x').
Proof. exact (eq_refl (term611 x')). Qed.
Lemma lem2433117 (x' : int) : (term546 x') = (term645 x').
Proof. exact (MK_COMB (@lem2433116 x') (@lem2433115 x')). Qed.
Lemma lem2433118 (x : int) : (term617 x) = (term617 x).
Proof. exact (eq_refl (term617 x)). Qed.
Lemma lem2433119 (x : int) (x' : int) : (term580 x x') = (term649 x x').
Proof. exact (MK_COMB (@lem2433118 x) (@lem2433117 x')). Qed.
Lemma lem2433120 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2433123 (y : int) (x : int) (x' : int) : (term650 y x x') = (term651 y x x').
Proof. exact (MK_COMB (@lem2433120 x x' y) (@lem2433119 x x')). Qed.
Lemma lem2433124 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2433125 (y : int) (x : int) (x' : int) : (term652 y x x') = (term653 y x x').
Proof. exact (MK_COMB (@lem2433124) (@lem2433086 y x x')). Qed.
Lemma lem2433126 (y : int) (x : int) (x' : int) : (term578 y x x') = (term654 y x x').
Proof. exact (MK_COMB (@lem2433125 y x x') (@lem2433123 y x x')). Qed.
Lemma lem2433128 (x : real) (r : real) : (term636 x r) = (term637 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2433129 (x' : int) : (term526 x') = (term638 x').
Proof. exact (@lem2433128 (real_of_int x') term54). Qed.
Lemma lem2433136 (x' : int) : (term144 x') = (real_of_int x').
Proof. exact (@lem1982733 (real_of_int x')). Qed.
Lemma lem2433137 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433138 (x' : int) : (term639 x') = (term640 x').
Proof. exact (MK_COMB (@lem2433137) (@lem2433136 x')). Qed.
Lemma lem2433139 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433140 (x' : int) : (term641 x') = (term642 x').
Proof. exact (MK_COMB (@lem2433138 x') (@lem2433139)). Qed.
Lemma lem2433153 (x' : int) : (term643 x') = (term643 x').
Proof. exact (eq_refl (term643 x')). Qed.
Lemma lem2433154 (x' : int) : (term638 x') = (term644 x').
Proof. exact (MK_COMB (@lem2433153 x') (@lem2433140 x')). Qed.
Lemma lem2433155 (x' : int) : (term526 x') = (term644 x').
Proof. exact (TRANS (@lem2433129 x') (@lem2433154 x')). Qed.
Lemma lem2433156 (x' : int) : (term617 x') = (term617 x').
Proof. exact (eq_refl (term617 x')). Qed.
Lemma lem2433157 (x' : int) : (term547 x') = (term655 x').
Proof. exact (MK_COMB (@lem2433156 x') (@lem2433155 x')). Qed.
Lemma lem2433158 (x : int) : (term611 x) = (term611 x).
Proof. exact (eq_refl (term611 x)). Qed.
Lemma lem2433159 (x : int) (x' : int) : (term575 x x') = (term656 x x').
Proof. exact (MK_COMB (@lem2433158 x) (@lem2433157 x')). Qed.
Lemma lem2433160 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2433163 (y : int) (x : int) (x' : int) : (term657 y x x') = (term658 y x x').
Proof. exact (MK_COMB (@lem2433160 x x' y) (@lem2433159 x x')). Qed.
Lemma lem2433165 (x : real) (r : real) : (term636 x r) = (term637 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2433166 (x' : int) : (term526 x') = (term638 x').
Proof. exact (@lem2433165 (real_of_int x') term54). Qed.
Lemma lem2433173 (x' : int) : (term144 x') = (real_of_int x').
Proof. exact (@lem1982733 (real_of_int x')). Qed.
Lemma lem2433174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433175 (x' : int) : (term639 x') = (term640 x').
Proof. exact (MK_COMB (@lem2433174) (@lem2433173 x')). Qed.
Lemma lem2433176 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433177 (x' : int) : (term641 x') = (term642 x').
Proof. exact (MK_COMB (@lem2433175 x') (@lem2433176)). Qed.
Lemma lem2433190 (x' : int) : (term643 x') = (term643 x').
Proof. exact (eq_refl (term643 x')). Qed.
Lemma lem2433191 (x' : int) : (term638 x') = (term644 x').
Proof. exact (MK_COMB (@lem2433190 x') (@lem2433177 x')). Qed.
Lemma lem2433192 (x' : int) : (term526 x') = (term644 x').
Proof. exact (TRANS (@lem2433166 x') (@lem2433191 x')). Qed.
Lemma lem2433193 (x' : int) : (term617 x') = (term617 x').
Proof. exact (eq_refl (term617 x')). Qed.
Lemma lem2433194 (x' : int) : (term547 x') = (term655 x').
Proof. exact (MK_COMB (@lem2433193 x') (@lem2433192 x')). Qed.
Lemma lem2433195 (x : int) : (term617 x) = (term617 x).
Proof. exact (eq_refl (term617 x)). Qed.
Lemma lem2433196 (x : int) (x' : int) : (term576 x x') = (term659 x x').
Proof. exact (MK_COMB (@lem2433195 x) (@lem2433194 x')). Qed.
Lemma lem2433197 (x : int) (x' : int) (y : int) : (term532 x x' y) = (term532 x x' y).
Proof. exact (eq_refl (term532 x x' y)). Qed.
Lemma lem2433200 (y : int) (x : int) (x' : int) : (term660 y x x') = (term661 y x x').
Proof. exact (MK_COMB (@lem2433197 x x' y) (@lem2433196 x x')). Qed.
Lemma lem2433201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2433202 (y : int) (x : int) (x' : int) : (term662 y x x') = (term663 y x x').
Proof. exact (MK_COMB (@lem2433201) (@lem2433163 y x x')). Qed.
Lemma lem2433203 (y : int) (x : int) (x' : int) : (term574 y x x') = (term664 y x x').
Proof. exact (MK_COMB (@lem2433202 y x x') (@lem2433200 y x x')). Qed.
Lemma lem2433204 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2433205 (y : int) (x : int) (x' : int) : (term582 y x x') = (term665 y x x').
Proof. exact (MK_COMB (@lem2433204) (@lem2433126 y x x')). Qed.
Lemma lem2433206 (y : int) (x : int) (x' : int) : (term583 y x x') = (term666 y x x').
Proof. exact (MK_COMB (@lem2433205 y x x') (@lem2433203 y x x')). Qed.
Lemma lem2433207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2433208 (y : int) (x' : int) (x : int) : (term598 y x' x) = (term667 y x' x).
Proof. exact (MK_COMB (@lem2433207) (@lem2433049 y x' x)). Qed.
Lemma lem2433209 (y : int) (x : int) (x' : int) : (term599 y x x') = (term668 y x x').
Proof. exact (MK_COMB (@lem2433208 y x' x) (@lem2433206 y x x')). Qed.
Lemma lem2433210 (y : int) (x : int) (x' : int) (h1 : term668 y x x') : term668 y x x'.
Proof. exact (h1). Qed.
Lemma lem2433211 (y : int) (x' : int) (x : int) (h1 : term635 y x' x) : term635 y x' x.
Proof. exact (h1). Qed.
Lemma lem2433212 (y : int) (x' : int) (x : int) (h1 : term623 y x' x) : term623 y x' x.
Proof. exact (h1). Qed.
Lemma lem2433213 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term616 y x' x.
Proof. exact (h1). Qed.
Lemma lem2433214 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term614 x' x.
Proof. exact (proj2 (@lem2433213 y x' x h1)). Qed.
Lemma lem2433216 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term613 x' x.
Proof. exact (proj2 (@lem2433214 y x' x h1)). Qed.
Lemma lem2433218 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term612 x.
Proof. exact (proj2 (@lem2433216 y x' x h1)). Qed.
Lemma lem2433220 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term499 x.
Proof. exact (proj2 (@lem2433218 y x' x h1)). Qed.
Lemma lem2433221 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term494 x.
Proof. exact (proj1 (@lem2433218 y x' x h1)). Qed.
Lemma lem2433223 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2433224 : term183 = term184.
Proof. exact (@lem2433223 term54 term42). Qed.
Lemma lem2433226 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433227 : term42 = term94.
Proof. exact (@lem2433226 term43). Qed.
Lemma lem2433229 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433230 : term54 = term170.
Proof. exact (@lem2433229 (NUMERAL 0)). Qed.
Lemma lem2433231 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2433232 : term185 = term186.
Proof. exact (MK_COMB (@lem2433231) (@lem2433230)). Qed.
Lemma lem2433233 : term184 = term187.
Proof. exact (MK_COMB (@lem2433232) (@lem2433227)). Qed.
Lemma lem2433234 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2433236 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433237 : term184 = term190.
Proof. exact (@lem2433236 (NUMERAL 0) term43). Qed.
Lemma lem2433238 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433239 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433240 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433239 h1) (fun h1 : term190 = True => @lem2433238)). Qed.
Lemma lem2433241 : term190 = True.
Proof. exact (EQ_MP (@lem2433240) (@lem2433238)). Qed.
Lemma lem2433242 : term184 = True.
Proof. exact (TRANS (@lem2433237) (@lem2433241)). Qed.
Lemma lem2433243 : True = term184.
Proof. exact (SYM (@lem2433242)). Qed.
Lemma lem2433244 : term184.
Proof. exact (EQ_MP (@lem2433243) (@lem0)). Qed.
Lemma lem2433245 : term192.
Proof. exact (@lem2433234 (@lem2433244)). Qed.
Lemma lem2433247 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433248 : term184 = term190.
Proof. exact (@lem2433247 (NUMERAL 0) term43). Qed.
Lemma lem2433249 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433250 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433251 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433250 h1) (fun h1 : term190 = True => @lem2433249)). Qed.
Lemma lem2433252 : term190 = True.
Proof. exact (EQ_MP (@lem2433251) (@lem2433249)). Qed.
Lemma lem2433253 : term184 = True.
Proof. exact (TRANS (@lem2433248) (@lem2433252)). Qed.
Lemma lem2433254 : True = term184.
Proof. exact (SYM (@lem2433253)). Qed.
Lemma lem2433255 : term184.
Proof. exact (EQ_MP (@lem2433254) (@lem0)). Qed.
Lemma lem2433256 : term187 = term193.
Proof. exact (@lem2433245 (@lem2433255)). Qed.
Lemma lem2433258 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433259 : term106 = term107.
Proof. exact (@lem2433258 term43 term43). Qed.
Lemma lem2433260 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433261 : term109 = term43.
Proof. exact (EQ_MP (@lem2433260) (@lem940073)). Qed.
Lemma lem2433262 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433263 : term107 = term42.
Proof. exact (MK_COMB (@lem2433262) (@lem2433261)). Qed.
Lemma lem2433264 : term106 = term42.
Proof. exact (TRANS (@lem2433259) (@lem2433263)). Qed.
Lemma lem2433266 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433267 : term195 = term54.
Proof. exact (@lem2433266 term43). Qed.
Lemma lem2433268 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2433269 : term196 = term185.
Proof. exact (MK_COMB (@lem2433268) (@lem2433267)). Qed.
Lemma lem2433270 : term193 = term184.
Proof. exact (MK_COMB (@lem2433269) (@lem2433264)). Qed.
Lemma lem2433272 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433273 : term184 = term190.
Proof. exact (@lem2433272 (NUMERAL 0) term43). Qed.
Lemma lem2433274 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433275 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433276 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433275 h1) (fun h1 : term190 = True => @lem2433274)). Qed.
Lemma lem2433277 : term190 = True.
Proof. exact (EQ_MP (@lem2433276) (@lem2433274)). Qed.
Lemma lem2433278 : term184 = True.
Proof. exact (TRANS (@lem2433273) (@lem2433277)). Qed.
Lemma lem2433279 : term193 = True.
Proof. exact (TRANS (@lem2433270) (@lem2433278)). Qed.
Lemma lem2433280 : term187 = True.
Proof. exact (TRANS (@lem2433256) (@lem2433279)). Qed.
Lemma lem2433281 : term184 = True.
Proof. exact (TRANS (@lem2433233) (@lem2433280)). Qed.
Lemma lem2433282 : term183 = True.
Proof. exact (TRANS (@lem2433224) (@lem2433281)). Qed.
Lemma lem2433283 : True = term183.
Proof. exact (SYM (@lem2433282)). Qed.
Lemma lem2433284 : term183.
Proof. exact (EQ_MP (@lem2433283) (@lem0)). Qed.
Lemma lem2433285 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term669 x.
Proof. exact (conj (@lem2433284) (@lem2433220 y x' x h1)). Qed.
Lemma lem2433287 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2433288 (x : int) : term670 x.
Proof. exact (@lem2433287 term42 (term117 x)). Qed.
Lemma lem2433289 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term671 x.
Proof. exact (@lem2433288 x (@lem2433285 y x' x h1)). Qed.
Lemma lem2433290 (x : int) : (term672 x) = (term117 x).
Proof. exact (@lem1982733 (term117 x)). Qed.
Lemma lem2433291 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433292 (x : int) : (term673 x) = (term498 x).
Proof. exact (MK_COMB (@lem2433291) (@lem2433290 x)). Qed.
Lemma lem2433293 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433294 (x : int) : (term671 x) = (term499 x).
Proof. exact (MK_COMB (@lem2433292 x) (@lem2433293)). Qed.
Lemma lem2433295 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term499 x.
Proof. exact (EQ_MP (@lem2433294 x) (@lem2433289 y x' x h1)). Qed.
Lemma lem2433297 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2433298 : term183 = term184.
Proof. exact (@lem2433297 term54 term42). Qed.
Lemma lem2433300 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433301 : term42 = term94.
Proof. exact (@lem2433300 term43). Qed.
Lemma lem2433303 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433304 : term54 = term170.
Proof. exact (@lem2433303 (NUMERAL 0)). Qed.
Lemma lem2433305 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2433306 : term185 = term186.
Proof. exact (MK_COMB (@lem2433305) (@lem2433304)). Qed.
Lemma lem2433307 : term184 = term187.
Proof. exact (MK_COMB (@lem2433306) (@lem2433301)). Qed.
Lemma lem2433308 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2433310 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433311 : term184 = term190.
Proof. exact (@lem2433310 (NUMERAL 0) term43). Qed.
Lemma lem2433312 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433313 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433314 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433313 h1) (fun h1 : term190 = True => @lem2433312)). Qed.
Lemma lem2433315 : term190 = True.
Proof. exact (EQ_MP (@lem2433314) (@lem2433312)). Qed.
Lemma lem2433316 : term184 = True.
Proof. exact (TRANS (@lem2433311) (@lem2433315)). Qed.
Lemma lem2433317 : True = term184.
Proof. exact (SYM (@lem2433316)). Qed.
Lemma lem2433318 : term184.
Proof. exact (EQ_MP (@lem2433317) (@lem0)). Qed.
Lemma lem2433319 : term192.
Proof. exact (@lem2433308 (@lem2433318)). Qed.
Lemma lem2433321 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433322 : term184 = term190.
Proof. exact (@lem2433321 (NUMERAL 0) term43). Qed.
Lemma lem2433323 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433324 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433325 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433324 h1) (fun h1 : term190 = True => @lem2433323)). Qed.
Lemma lem2433326 : term190 = True.
Proof. exact (EQ_MP (@lem2433325) (@lem2433323)). Qed.
Lemma lem2433327 : term184 = True.
Proof. exact (TRANS (@lem2433322) (@lem2433326)). Qed.
Lemma lem2433328 : True = term184.
Proof. exact (SYM (@lem2433327)). Qed.
Lemma lem2433329 : term184.
Proof. exact (EQ_MP (@lem2433328) (@lem0)). Qed.
Lemma lem2433330 : term187 = term193.
Proof. exact (@lem2433319 (@lem2433329)). Qed.
Lemma lem2433332 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433333 : term106 = term107.
Proof. exact (@lem2433332 term43 term43). Qed.
Lemma lem2433334 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433335 : term109 = term43.
Proof. exact (EQ_MP (@lem2433334) (@lem940073)). Qed.
Lemma lem2433336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433337 : term107 = term42.
Proof. exact (MK_COMB (@lem2433336) (@lem2433335)). Qed.
Lemma lem2433338 : term106 = term42.
Proof. exact (TRANS (@lem2433333) (@lem2433337)). Qed.
Lemma lem2433340 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433341 : term195 = term54.
Proof. exact (@lem2433340 term43). Qed.
Lemma lem2433342 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2433343 : term196 = term185.
Proof. exact (MK_COMB (@lem2433342) (@lem2433341)). Qed.
Lemma lem2433344 : term193 = term184.
Proof. exact (MK_COMB (@lem2433343) (@lem2433338)). Qed.
Lemma lem2433346 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433347 : term184 = term190.
Proof. exact (@lem2433346 (NUMERAL 0) term43). Qed.
Lemma lem2433348 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433349 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433350 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433349 h1) (fun h1 : term190 = True => @lem2433348)). Qed.
Lemma lem2433351 : term190 = True.
Proof. exact (EQ_MP (@lem2433350) (@lem2433348)). Qed.
Lemma lem2433352 : term184 = True.
Proof. exact (TRANS (@lem2433347) (@lem2433351)). Qed.
Lemma lem2433353 : term193 = True.
Proof. exact (TRANS (@lem2433344) (@lem2433352)). Qed.
Lemma lem2433354 : term187 = True.
Proof. exact (TRANS (@lem2433330) (@lem2433353)). Qed.
Lemma lem2433355 : term184 = True.
Proof. exact (TRANS (@lem2433307) (@lem2433354)). Qed.
Lemma lem2433356 : term183 = True.
Proof. exact (TRANS (@lem2433298) (@lem2433355)). Qed.
Lemma lem2433357 : True = term183.
Proof. exact (SYM (@lem2433356)). Qed.
Lemma lem2433358 : term183.
Proof. exact (EQ_MP (@lem2433357) (@lem0)). Qed.
Lemma lem2433359 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term674 x.
Proof. exact (conj (@lem2433358) (@lem2433221 y x' x h1)). Qed.
Lemma lem2433361 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2433362 (x : int) : term675 x.
Proof. exact (@lem2433361 term42 (term490 x)). Qed.
Lemma lem2433363 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term676 x.
Proof. exact (@lem2433362 x (@lem2433359 y x' x h1)). Qed.
Lemma lem2433364 (x : int) : (term677 x) = (term490 x).
Proof. exact (@lem1982733 (term490 x)). Qed.
Lemma lem2433365 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433366 (x : int) : (term678 x) = (term493 x).
Proof. exact (MK_COMB (@lem2433365) (@lem2433364 x)). Qed.
Lemma lem2433367 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433368 (x : int) : (term676 x) = (term494 x).
Proof. exact (MK_COMB (@lem2433366 x) (@lem2433367)). Qed.
Lemma lem2433369 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term494 x.
Proof. exact (EQ_MP (@lem2433368 x) (@lem2433363 y x' x h1)). Qed.
Lemma lem2433370 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term612 x.
Proof. exact (conj (@lem2433369 y x' x h1) (@lem2433295 y x' x h1)). Qed.
Lemma lem2433372 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2433373 (x : int) : term679 x.
Proof. exact (@lem2433372 (term490 x) (term117 x)). Qed.
Lemma lem2433374 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term680 x.
Proof. exact (@lem2433373 x (@lem2433370 y x' x h1)). Qed.
Lemma lem2433375 (x : int) : (term681 x) = (term682 x).
Proof. exact (@lem1982753 (term121 x) (real_of_int x) term97 term97). Qed.
Lemma lem2433376 (x : int) : (term683 x) = (term236 x).
Proof. exact (@lem1982713 term97 (real_of_int x)). Qed.
Lemma lem2433378 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433379 : term42 = term94.
Proof. exact (@lem2433378 term43). Qed.
Lemma lem2433381 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2433382 : term97 = term98.
Proof. exact (@lem2433381 term43). Qed.
Lemma lem2433383 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433384 : term215 = term216.
Proof. exact (MK_COMB (@lem2433383) (@lem2433382)). Qed.
Lemma lem2433385 : term217 = term218.
Proof. exact (MK_COMB (@lem2433384) (@lem2433379)). Qed.
Lemma lem2433386 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2433388 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433389 : term184 = term190.
Proof. exact (@lem2433388 (NUMERAL 0) term43). Qed.
Lemma lem2433390 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433391 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433392 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433391 h1) (fun h1 : term190 = True => @lem2433390)). Qed.
Lemma lem2433393 : term190 = True.
Proof. exact (EQ_MP (@lem2433392) (@lem2433390)). Qed.
Lemma lem2433394 : term184 = True.
Proof. exact (TRANS (@lem2433389) (@lem2433393)). Qed.
Lemma lem2433395 : True = term184.
Proof. exact (SYM (@lem2433394)). Qed.
Lemma lem2433396 : term184.
Proof. exact (EQ_MP (@lem2433395) (@lem0)). Qed.
Lemma lem2433397 : term220.
Proof. exact (@lem2433386 (@lem2433396)). Qed.
Lemma lem2433399 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433400 : term184 = term190.
Proof. exact (@lem2433399 (NUMERAL 0) term43). Qed.
Lemma lem2433401 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433402 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433403 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433402 h1) (fun h1 : term190 = True => @lem2433401)). Qed.
Lemma lem2433404 : term190 = True.
Proof. exact (EQ_MP (@lem2433403) (@lem2433401)). Qed.
Lemma lem2433405 : term184 = True.
Proof. exact (TRANS (@lem2433400) (@lem2433404)). Qed.
Lemma lem2433406 : True = term184.
Proof. exact (SYM (@lem2433405)). Qed.
Lemma lem2433407 : term184.
Proof. exact (EQ_MP (@lem2433406) (@lem0)). Qed.
Lemma lem2433408 : term221.
Proof. exact (@lem2433397 (@lem2433407)). Qed.
Lemma lem2433410 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433411 : term184 = term190.
Proof. exact (@lem2433410 (NUMERAL 0) term43). Qed.
Lemma lem2433412 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433413 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433414 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433413 h1) (fun h1 : term190 = True => @lem2433412)). Qed.
Lemma lem2433415 : term190 = True.
Proof. exact (EQ_MP (@lem2433414) (@lem2433412)). Qed.
Lemma lem2433416 : term184 = True.
Proof. exact (TRANS (@lem2433411) (@lem2433415)). Qed.
Lemma lem2433417 : True = term184.
Proof. exact (SYM (@lem2433416)). Qed.
Lemma lem2433418 : term184.
Proof. exact (EQ_MP (@lem2433417) (@lem0)). Qed.
Lemma lem2433419 : term222.
Proof. exact (@lem2433408 (@lem2433418)). Qed.
Lemma lem2433421 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433422 : term106 = term107.
Proof. exact (@lem2433421 term43 term43). Qed.
Lemma lem2433423 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433424 : term109 = term43.
Proof. exact (EQ_MP (@lem2433423) (@lem940073)). Qed.
Lemma lem2433425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433426 : term107 = term42.
Proof. exact (MK_COMB (@lem2433425) (@lem2433424)). Qed.
Lemma lem2433427 : term106 = term42.
Proof. exact (TRANS (@lem2433422) (@lem2433426)). Qed.
Lemma lem2433429 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2433430 : term101 = term112.
Proof. exact (@lem2433429 term43 term43). Qed.
Lemma lem2433431 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433432 : term109 = term43.
Proof. exact (EQ_MP (@lem2433431) (@lem940073)). Qed.
Lemma lem2433433 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433434 : term107 = term42.
Proof. exact (MK_COMB (@lem2433433) (@lem2433432)). Qed.
Lemma lem2433435 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2433436 : term112 = term97.
Proof. exact (MK_COMB (@lem2433435) (@lem2433434)). Qed.
Lemma lem2433437 : term101 = term97.
Proof. exact (TRANS (@lem2433430) (@lem2433436)). Qed.
Lemma lem2433438 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433439 : term223 = term215.
Proof. exact (MK_COMB (@lem2433438) (@lem2433437)). Qed.
Lemma lem2433440 : term224 = term217.
Proof. exact (MK_COMB (@lem2433439) (@lem2433427)). Qed.
Lemma lem2433442 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2433443 : term217 = term54.
Proof. exact (@lem2433442 term43). Qed.
Lemma lem2433444 : term224 = term54.
Proof. exact (TRANS (@lem2433440) (@lem2433443)). Qed.
Lemma lem2433445 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2433446 : term226 = term227.
Proof. exact (MK_COMB (@lem2433445) (@lem2433444)). Qed.
Lemma lem2433447 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2433448 : term228 = term195.
Proof. exact (MK_COMB (@lem2433446) (@lem2433447)). Qed.
Lemma lem2433450 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433451 : term195 = term54.
Proof. exact (@lem2433450 term43). Qed.
Lemma lem2433452 : term228 = term54.
Proof. exact (TRANS (@lem2433448) (@lem2433451)). Qed.
Lemma lem2433454 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433455 : term106 = term107.
Proof. exact (@lem2433454 term43 term43). Qed.
Lemma lem2433456 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433457 : term109 = term43.
Proof. exact (EQ_MP (@lem2433456) (@lem940073)). Qed.
Lemma lem2433458 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433459 : term107 = term42.
Proof. exact (MK_COMB (@lem2433458) (@lem2433457)). Qed.
Lemma lem2433460 : term106 = term42.
Proof. exact (TRANS (@lem2433455) (@lem2433459)). Qed.
Lemma lem2433461 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2433462 : term229 = term195.
Proof. exact (MK_COMB (@lem2433461) (@lem2433460)). Qed.
Lemma lem2433464 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433465 : term195 = term54.
Proof. exact (@lem2433464 term43). Qed.
Lemma lem2433466 : term229 = term54.
Proof. exact (TRANS (@lem2433462) (@lem2433465)). Qed.
Lemma lem2433467 : term54 = term229.
Proof. exact (SYM (@lem2433466)). Qed.
Lemma lem2433468 : term228 = term229.
Proof. exact (TRANS (@lem2433452) (@lem2433467)). Qed.
Lemma lem2433469 : term218 = term170.
Proof. exact (@lem2433419 (@lem2433468)). Qed.
Lemma lem2433470 : term217 = term170.
Proof. exact (TRANS (@lem2433385) (@lem2433469)). Qed.
Lemma lem2433472 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2433473 : term170 = term54.
Proof. exact (@lem2433472 term54). Qed.
Lemma lem2433474 : term217 = term54.
Proof. exact (TRANS (@lem2433470) (@lem2433473)). Qed.
Lemma lem2433475 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2433476 : term230 = term227.
Proof. exact (MK_COMB (@lem2433475) (@lem2433474)). Qed.
Lemma lem2433477 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2433478 (x : int) : (term236 x) = (term237 x).
Proof. exact (MK_COMB (@lem2433476) (@lem2433477 x)). Qed.
Lemma lem2433479 (x : int) : (term683 x) = (term237 x).
Proof. exact (TRANS (@lem2433376 x) (@lem2433478 x)). Qed.
Lemma lem2433480 (x : int) : (term237 x) = term54.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2433481 (x : int) : (term683 x) = term54.
Proof. exact (TRANS (@lem2433479 x) (@lem2433480 x)). Qed.
Lemma lem2433482 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433483 (x : int) : (term684 x) = term148.
Proof. exact (MK_COMB (@lem2433482) (@lem2433481 x)). Qed.
Lemma lem2433485 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2433486 : term97 = term98.
Proof. exact (@lem2433485 term43). Qed.
Lemma lem2433488 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2433489 : term97 = term98.
Proof. exact (@lem2433488 term43). Qed.
Lemma lem2433490 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433491 : term215 = term216.
Proof. exact (MK_COMB (@lem2433490) (@lem2433489)). Qed.
Lemma lem2433492 : term685 = term686.
Proof. exact (MK_COMB (@lem2433491) (@lem2433486)). Qed.
Lemma lem2433493 : term687.
Proof. exact (@lem1981473 term97 term42 term97 term42 term688 term42). Qed.
Lemma lem2433495 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433496 : term184 = term190.
Proof. exact (@lem2433495 (NUMERAL 0) term43). Qed.
Lemma lem2433497 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433498 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433499 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433498 h1) (fun h1 : term190 = True => @lem2433497)). Qed.
Lemma lem2433500 : term190 = True.
Proof. exact (EQ_MP (@lem2433499) (@lem2433497)). Qed.
Lemma lem2433501 : term184 = True.
Proof. exact (TRANS (@lem2433496) (@lem2433500)). Qed.
Lemma lem2433502 : True = term184.
Proof. exact (SYM (@lem2433501)). Qed.
Lemma lem2433503 : term184.
Proof. exact (EQ_MP (@lem2433502) (@lem0)). Qed.
Lemma lem2433504 : term689.
Proof. exact (@lem2433493 (@lem2433503)). Qed.
Lemma lem2433506 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433507 : term184 = term190.
Proof. exact (@lem2433506 (NUMERAL 0) term43). Qed.
Lemma lem2433508 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433509 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433510 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433509 h1) (fun h1 : term190 = True => @lem2433508)). Qed.
Lemma lem2433511 : term190 = True.
Proof. exact (EQ_MP (@lem2433510) (@lem2433508)). Qed.
Lemma lem2433512 : term184 = True.
Proof. exact (TRANS (@lem2433507) (@lem2433511)). Qed.
Lemma lem2433513 : True = term184.
Proof. exact (SYM (@lem2433512)). Qed.
Lemma lem2433514 : term184.
Proof. exact (EQ_MP (@lem2433513) (@lem0)). Qed.
Lemma lem2433515 : term690.
Proof. exact (@lem2433504 (@lem2433514)). Qed.
Lemma lem2433517 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433518 : term184 = term190.
Proof. exact (@lem2433517 (NUMERAL 0) term43). Qed.
Lemma lem2433519 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433520 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433521 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433520 h1) (fun h1 : term190 = True => @lem2433519)). Qed.
Lemma lem2433522 : term190 = True.
Proof. exact (EQ_MP (@lem2433521) (@lem2433519)). Qed.
Lemma lem2433523 : term184 = True.
Proof. exact (TRANS (@lem2433518) (@lem2433522)). Qed.
Lemma lem2433524 : True = term184.
Proof. exact (SYM (@lem2433523)). Qed.
Lemma lem2433525 : term184.
Proof. exact (EQ_MP (@lem2433524) (@lem0)). Qed.
Lemma lem2433526 : term691.
Proof. exact (@lem2433515 (@lem2433525)). Qed.
Lemma lem2433528 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2433529 : term101 = term112.
Proof. exact (@lem2433528 term43 term43). Qed.
Lemma lem2433530 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433531 : term109 = term43.
Proof. exact (EQ_MP (@lem2433530) (@lem940073)). Qed.
Lemma lem2433532 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433533 : term107 = term42.
Proof. exact (MK_COMB (@lem2433532) (@lem2433531)). Qed.
Lemma lem2433534 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2433535 : term112 = term97.
Proof. exact (MK_COMB (@lem2433534) (@lem2433533)). Qed.
Lemma lem2433536 : term101 = term97.
Proof. exact (TRANS (@lem2433529) (@lem2433535)). Qed.
Lemma lem2433538 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2433539 : term101 = term112.
Proof. exact (@lem2433538 term43 term43). Qed.
Lemma lem2433540 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433541 : term109 = term43.
Proof. exact (EQ_MP (@lem2433540) (@lem940073)). Qed.
Lemma lem2433542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433543 : term107 = term42.
Proof. exact (MK_COMB (@lem2433542) (@lem2433541)). Qed.
Lemma lem2433544 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2433545 : term112 = term97.
Proof. exact (MK_COMB (@lem2433544) (@lem2433543)). Qed.
Lemma lem2433546 : term101 = term97.
Proof. exact (TRANS (@lem2433539) (@lem2433545)). Qed.
Lemma lem2433547 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433548 : term223 = term215.
Proof. exact (MK_COMB (@lem2433547) (@lem2433546)). Qed.
Lemma lem2433549 : term692 = term685.
Proof. exact (MK_COMB (@lem2433548) (@lem2433536)). Qed.
Lemma lem2433550 : term685 = term693.
Proof. exact (@lem1367763 term43 term43). Qed.
Lemma lem2433551 : term694 = term695.
Proof. exact (@lem706885). Qed.
Lemma lem2433552 : (term694 = term695) = (term696 = term697).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term695). Qed.
Lemma lem2433553 : term696 = term697.
Proof. exact (EQ_MP (@lem2433552) (@lem2433551)). Qed.
Lemma lem2433554 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433555 : term698 = term699.
Proof. exact (MK_COMB (@lem2433554) (@lem2433553)). Qed.
Lemma lem2433556 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2433557 : term693 = term688.
Proof. exact (MK_COMB (@lem2433556) (@lem2433555)). Qed.
Lemma lem2433558 : term685 = term688.
Proof. exact (TRANS (@lem2433550) (@lem2433557)). Qed.
Lemma lem2433559 : term692 = term688.
Proof. exact (TRANS (@lem2433549) (@lem2433558)). Qed.
Lemma lem2433560 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2433561 : term700 = term701.
Proof. exact (MK_COMB (@lem2433560) (@lem2433559)). Qed.
Lemma lem2433562 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2433563 : term702 = term703.
Proof. exact (MK_COMB (@lem2433561) (@lem2433562)). Qed.
Lemma lem2433565 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2433566 : term703 = term704.
Proof. exact (@lem2433565 term697 term43). Qed.
Lemma lem2433567 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2433568 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2433569 : term706 = term697.
Proof. exact (EQ_MP (@lem2433568) (@lem2433567)). Qed.
Lemma lem2433570 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433571 : term707 = term699.
Proof. exact (MK_COMB (@lem2433570) (@lem2433569)). Qed.
Lemma lem2433572 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2433573 : term704 = term688.
Proof. exact (MK_COMB (@lem2433572) (@lem2433571)). Qed.
Lemma lem2433574 : term703 = term688.
Proof. exact (TRANS (@lem2433566) (@lem2433573)). Qed.
Lemma lem2433575 : term702 = term688.
Proof. exact (TRANS (@lem2433563) (@lem2433574)). Qed.
Lemma lem2433577 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433578 : term106 = term107.
Proof. exact (@lem2433577 term43 term43). Qed.
Lemma lem2433579 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433580 : term109 = term43.
Proof. exact (EQ_MP (@lem2433579) (@lem940073)). Qed.
Lemma lem2433581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433582 : term107 = term42.
Proof. exact (MK_COMB (@lem2433581) (@lem2433580)). Qed.
Lemma lem2433583 : term106 = term42.
Proof. exact (TRANS (@lem2433578) (@lem2433582)). Qed.
Lemma lem2433584 : term701 = term701.
Proof. exact (eq_refl term701). Qed.
Lemma lem2433585 : term708 = term703.
Proof. exact (MK_COMB (@lem2433584) (@lem2433583)). Qed.
Lemma lem2433587 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2433588 : term703 = term704.
Proof. exact (@lem2433587 term697 term43). Qed.
Lemma lem2433589 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2433590 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2433591 : term706 = term697.
Proof. exact (EQ_MP (@lem2433590) (@lem2433589)). Qed.
Lemma lem2433592 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433593 : term707 = term699.
Proof. exact (MK_COMB (@lem2433592) (@lem2433591)). Qed.
Lemma lem2433594 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2433595 : term704 = term688.
Proof. exact (MK_COMB (@lem2433594) (@lem2433593)). Qed.
Lemma lem2433596 : term703 = term688.
Proof. exact (TRANS (@lem2433588) (@lem2433595)). Qed.
Lemma lem2433597 : term708 = term688.
Proof. exact (TRANS (@lem2433585) (@lem2433596)). Qed.
Lemma lem2433598 : term688 = term708.
Proof. exact (SYM (@lem2433597)). Qed.
Lemma lem2433599 : term702 = term708.
Proof. exact (TRANS (@lem2433575) (@lem2433598)). Qed.
Lemma lem2433600 : term686 = term709.
Proof. exact (@lem2433526 (@lem2433599)). Qed.
Lemma lem2433601 : term685 = term709.
Proof. exact (TRANS (@lem2433492) (@lem2433600)). Qed.
Lemma lem2433603 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2433604 : term709 = term688.
Proof. exact (@lem2433603 term688). Qed.
Lemma lem2433605 : term685 = term688.
Proof. exact (TRANS (@lem2433601) (@lem2433604)). Qed.
Lemma lem2433606 (x : int) : (term682 x) = term710.
Proof. exact (MK_COMB (@lem2433483 x) (@lem2433605)). Qed.
Lemma lem2433607 (x : int) : (term681 x) = term710.
Proof. exact (TRANS (@lem2433375 x) (@lem2433606 x)). Qed.
Lemma lem2433608 : term710 = term688.
Proof. exact (@lem1982721 term688). Qed.
Lemma lem2433609 (x : int) : (term681 x) = term688.
Proof. exact (TRANS (@lem2433607 x) (@lem2433608)). Qed.
Lemma lem2433610 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433611 (x : int) : (term711 x) = term712.
Proof. exact (MK_COMB (@lem2433610) (@lem2433609 x)). Qed.
Lemma lem2433612 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433613 (x : int) : (term680 x) = term713.
Proof. exact (MK_COMB (@lem2433611 x) (@lem2433612)). Qed.
Lemma lem2433614 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : term713.
Proof. exact (EQ_MP (@lem2433613 x) (@lem2433374 y x' x h1)). Qed.
Lemma lem2433616 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2433617 : term713 = term714.
Proof. exact (@lem2433616 term54 term688). Qed.
Lemma lem2433619 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2433620 : term688 = term709.
Proof. exact (@lem2433619 term697). Qed.
Lemma lem2433622 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433623 : term54 = term170.
Proof. exact (@lem2433622 (NUMERAL 0)). Qed.
Lemma lem2433624 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2433625 : term74 = term244.
Proof. exact (MK_COMB (@lem2433624) (@lem2433623)). Qed.
Lemma lem2433626 : term714 = term715.
Proof. exact (MK_COMB (@lem2433625) (@lem2433620)). Qed.
Lemma lem2433627 : term716.
Proof. exact (@lem1980026 term54 term42 term688 term42). Qed.
Lemma lem2433629 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433630 : term184 = term190.
Proof. exact (@lem2433629 (NUMERAL 0) term43). Qed.
Lemma lem2433631 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433632 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433633 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433632 h1) (fun h1 : term190 = True => @lem2433631)). Qed.
Lemma lem2433634 : term190 = True.
Proof. exact (EQ_MP (@lem2433633) (@lem2433631)). Qed.
Lemma lem2433635 : term184 = True.
Proof. exact (TRANS (@lem2433630) (@lem2433634)). Qed.
Lemma lem2433636 : True = term184.
Proof. exact (SYM (@lem2433635)). Qed.
Lemma lem2433637 : term184.
Proof. exact (EQ_MP (@lem2433636) (@lem0)). Qed.
Lemma lem2433638 : term717.
Proof. exact (@lem2433627 (@lem2433637)). Qed.
Lemma lem2433640 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433641 : term184 = term190.
Proof. exact (@lem2433640 (NUMERAL 0) term43). Qed.
Lemma lem2433642 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433643 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433644 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433643 h1) (fun h1 : term190 = True => @lem2433642)). Qed.
Lemma lem2433645 : term190 = True.
Proof. exact (EQ_MP (@lem2433644) (@lem2433642)). Qed.
Lemma lem2433646 : term184 = True.
Proof. exact (TRANS (@lem2433641) (@lem2433645)). Qed.
Lemma lem2433647 : True = term184.
Proof. exact (SYM (@lem2433646)). Qed.
Lemma lem2433648 : term184.
Proof. exact (EQ_MP (@lem2433647) (@lem0)). Qed.
Lemma lem2433649 : term715 = term718.
Proof. exact (@lem2433638 (@lem2433648)). Qed.
Lemma lem2433651 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2433652 : term703 = term704.
Proof. exact (@lem2433651 term697 term43). Qed.
Lemma lem2433653 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2433654 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2433655 : term706 = term697.
Proof. exact (EQ_MP (@lem2433654) (@lem2433653)). Qed.
Lemma lem2433656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433657 : term707 = term699.
Proof. exact (MK_COMB (@lem2433656) (@lem2433655)). Qed.
Lemma lem2433658 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2433659 : term704 = term688.
Proof. exact (MK_COMB (@lem2433658) (@lem2433657)). Qed.
Lemma lem2433660 : term703 = term688.
Proof. exact (TRANS (@lem2433652) (@lem2433659)). Qed.
Lemma lem2433662 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433663 : term195 = term54.
Proof. exact (@lem2433662 term43). Qed.
Lemma lem2433664 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2433665 : term249 = term74.
Proof. exact (MK_COMB (@lem2433664) (@lem2433663)). Qed.
Lemma lem2433666 : term718 = term714.
Proof. exact (MK_COMB (@lem2433665) (@lem2433660)). Qed.
Lemma lem2433668 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2433669 : term714 = term719.
Proof. exact (@lem2433668 (NUMERAL 0) term697). Qed.
Lemma lem2433670 : term720 = term695.
Proof. exact (@lem912803). Qed.
Lemma lem2433671 (h1 : term720 = term695) : (term697 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term695 h1). Qed.
Lemma lem2433672 : (term720 = term695) = ((term697 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term720 = term695 => @lem2433671 h1) (fun h1 : (term697 = (NUMERAL 0)) = False => @lem2433670)). Qed.
Lemma lem2433673 : (term697 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2433672) (@lem2433670)). Qed.
Lemma lem2433674 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2433675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2433676 : term253 = (and True).
Proof. exact (MK_COMB (@lem2433675) (@lem2433674)). Qed.
Lemma lem2433677 : term719 = (True /\ False).
Proof. exact (MK_COMB (@lem2433676) (@lem2433673)). Qed.
Lemma lem2433679 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2433680 : term719 = False.
Proof. exact (TRANS (@lem2433677) (@lem2433679)). Qed.
Lemma lem2433681 : term714 = False.
Proof. exact (TRANS (@lem2433669) (@lem2433680)). Qed.
Lemma lem2433682 : term718 = False.
Proof. exact (TRANS (@lem2433666) (@lem2433681)). Qed.
Lemma lem2433683 : term715 = False.
Proof. exact (TRANS (@lem2433649) (@lem2433682)). Qed.
Lemma lem2433684 : term714 = False.
Proof. exact (TRANS (@lem2433626) (@lem2433683)). Qed.
Lemma lem2433685 : term713 = False.
Proof. exact (TRANS (@lem2433617) (@lem2433684)). Qed.
Lemma lem2433686 (y : int) (x' : int) (x : int) (h1 : term616 y x' x) : False.
Proof. exact (EQ_MP (@lem2433685) (@lem2433614 y x' x h1)). Qed.
Lemma lem2433687 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term620 y x' x.
Proof. exact (h1). Qed.
Lemma lem2433688 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term618 x' x.
Proof. exact (proj2 (@lem2433687 y x' x h1)). Qed.
Lemma lem2433690 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term613 x' x.
Proof. exact (proj2 (@lem2433688 y x' x h1)). Qed.
Lemma lem2433692 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term612 x.
Proof. exact (proj2 (@lem2433690 y x' x h1)). Qed.
Lemma lem2433694 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term499 x.
Proof. exact (proj2 (@lem2433692 y x' x h1)). Qed.
Lemma lem2433695 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term494 x.
Proof. exact (proj1 (@lem2433692 y x' x h1)). Qed.
Lemma lem2433697 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2433698 : term183 = term184.
Proof. exact (@lem2433697 term54 term42). Qed.
Lemma lem2433700 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433701 : term42 = term94.
Proof. exact (@lem2433700 term43). Qed.
Lemma lem2433703 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433704 : term54 = term170.
Proof. exact (@lem2433703 (NUMERAL 0)). Qed.
Lemma lem2433705 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2433706 : term185 = term186.
Proof. exact (MK_COMB (@lem2433705) (@lem2433704)). Qed.
Lemma lem2433707 : term184 = term187.
Proof. exact (MK_COMB (@lem2433706) (@lem2433701)). Qed.
Lemma lem2433708 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2433710 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433711 : term184 = term190.
Proof. exact (@lem2433710 (NUMERAL 0) term43). Qed.
Lemma lem2433712 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433713 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433714 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433713 h1) (fun h1 : term190 = True => @lem2433712)). Qed.
Lemma lem2433715 : term190 = True.
Proof. exact (EQ_MP (@lem2433714) (@lem2433712)). Qed.
Lemma lem2433716 : term184 = True.
Proof. exact (TRANS (@lem2433711) (@lem2433715)). Qed.
Lemma lem2433717 : True = term184.
Proof. exact (SYM (@lem2433716)). Qed.
Lemma lem2433718 : term184.
Proof. exact (EQ_MP (@lem2433717) (@lem0)). Qed.
Lemma lem2433719 : term192.
Proof. exact (@lem2433708 (@lem2433718)). Qed.
Lemma lem2433721 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433722 : term184 = term190.
Proof. exact (@lem2433721 (NUMERAL 0) term43). Qed.
Lemma lem2433723 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433724 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433725 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433724 h1) (fun h1 : term190 = True => @lem2433723)). Qed.
Lemma lem2433726 : term190 = True.
Proof. exact (EQ_MP (@lem2433725) (@lem2433723)). Qed.
Lemma lem2433727 : term184 = True.
Proof. exact (TRANS (@lem2433722) (@lem2433726)). Qed.
Lemma lem2433728 : True = term184.
Proof. exact (SYM (@lem2433727)). Qed.
Lemma lem2433729 : term184.
Proof. exact (EQ_MP (@lem2433728) (@lem0)). Qed.
Lemma lem2433730 : term187 = term193.
Proof. exact (@lem2433719 (@lem2433729)). Qed.
Lemma lem2433732 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433733 : term106 = term107.
Proof. exact (@lem2433732 term43 term43). Qed.
Lemma lem2433734 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433735 : term109 = term43.
Proof. exact (EQ_MP (@lem2433734) (@lem940073)). Qed.
Lemma lem2433736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433737 : term107 = term42.
Proof. exact (MK_COMB (@lem2433736) (@lem2433735)). Qed.
Lemma lem2433738 : term106 = term42.
Proof. exact (TRANS (@lem2433733) (@lem2433737)). Qed.
Lemma lem2433740 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433741 : term195 = term54.
Proof. exact (@lem2433740 term43). Qed.
Lemma lem2433742 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2433743 : term196 = term185.
Proof. exact (MK_COMB (@lem2433742) (@lem2433741)). Qed.
Lemma lem2433744 : term193 = term184.
Proof. exact (MK_COMB (@lem2433743) (@lem2433738)). Qed.
Lemma lem2433746 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433747 : term184 = term190.
Proof. exact (@lem2433746 (NUMERAL 0) term43). Qed.
Lemma lem2433748 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433749 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433750 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433749 h1) (fun h1 : term190 = True => @lem2433748)). Qed.
Lemma lem2433751 : term190 = True.
Proof. exact (EQ_MP (@lem2433750) (@lem2433748)). Qed.
Lemma lem2433752 : term184 = True.
Proof. exact (TRANS (@lem2433747) (@lem2433751)). Qed.
Lemma lem2433753 : term193 = True.
Proof. exact (TRANS (@lem2433744) (@lem2433752)). Qed.
Lemma lem2433754 : term187 = True.
Proof. exact (TRANS (@lem2433730) (@lem2433753)). Qed.
Lemma lem2433755 : term184 = True.
Proof. exact (TRANS (@lem2433707) (@lem2433754)). Qed.
Lemma lem2433756 : term183 = True.
Proof. exact (TRANS (@lem2433698) (@lem2433755)). Qed.
Lemma lem2433757 : True = term183.
Proof. exact (SYM (@lem2433756)). Qed.
Lemma lem2433758 : term183.
Proof. exact (EQ_MP (@lem2433757) (@lem0)). Qed.
Lemma lem2433759 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term669 x.
Proof. exact (conj (@lem2433758) (@lem2433694 y x' x h1)). Qed.
Lemma lem2433761 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2433762 (x : int) : term670 x.
Proof. exact (@lem2433761 term42 (term117 x)). Qed.
Lemma lem2433763 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term671 x.
Proof. exact (@lem2433762 x (@lem2433759 y x' x h1)). Qed.
Lemma lem2433764 (x : int) : (term672 x) = (term117 x).
Proof. exact (@lem1982733 (term117 x)). Qed.
Lemma lem2433765 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433766 (x : int) : (term673 x) = (term498 x).
Proof. exact (MK_COMB (@lem2433765) (@lem2433764 x)). Qed.
Lemma lem2433767 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433768 (x : int) : (term671 x) = (term499 x).
Proof. exact (MK_COMB (@lem2433766 x) (@lem2433767)). Qed.
Lemma lem2433769 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term499 x.
Proof. exact (EQ_MP (@lem2433768 x) (@lem2433763 y x' x h1)). Qed.
Lemma lem2433771 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2433772 : term183 = term184.
Proof. exact (@lem2433771 term54 term42). Qed.
Lemma lem2433774 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433775 : term42 = term94.
Proof. exact (@lem2433774 term43). Qed.
Lemma lem2433777 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433778 : term54 = term170.
Proof. exact (@lem2433777 (NUMERAL 0)). Qed.
Lemma lem2433779 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2433780 : term185 = term186.
Proof. exact (MK_COMB (@lem2433779) (@lem2433778)). Qed.
Lemma lem2433781 : term184 = term187.
Proof. exact (MK_COMB (@lem2433780) (@lem2433775)). Qed.
Lemma lem2433782 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2433784 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433785 : term184 = term190.
Proof. exact (@lem2433784 (NUMERAL 0) term43). Qed.
Lemma lem2433786 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433787 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433788 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433787 h1) (fun h1 : term190 = True => @lem2433786)). Qed.
Lemma lem2433789 : term190 = True.
Proof. exact (EQ_MP (@lem2433788) (@lem2433786)). Qed.
Lemma lem2433790 : term184 = True.
Proof. exact (TRANS (@lem2433785) (@lem2433789)). Qed.
Lemma lem2433791 : True = term184.
Proof. exact (SYM (@lem2433790)). Qed.
Lemma lem2433792 : term184.
Proof. exact (EQ_MP (@lem2433791) (@lem0)). Qed.
Lemma lem2433793 : term192.
Proof. exact (@lem2433782 (@lem2433792)). Qed.
Lemma lem2433795 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433796 : term184 = term190.
Proof. exact (@lem2433795 (NUMERAL 0) term43). Qed.
Lemma lem2433797 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433798 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433799 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433798 h1) (fun h1 : term190 = True => @lem2433797)). Qed.
Lemma lem2433800 : term190 = True.
Proof. exact (EQ_MP (@lem2433799) (@lem2433797)). Qed.
Lemma lem2433801 : term184 = True.
Proof. exact (TRANS (@lem2433796) (@lem2433800)). Qed.
Lemma lem2433802 : True = term184.
Proof. exact (SYM (@lem2433801)). Qed.
Lemma lem2433803 : term184.
Proof. exact (EQ_MP (@lem2433802) (@lem0)). Qed.
Lemma lem2433804 : term187 = term193.
Proof. exact (@lem2433793 (@lem2433803)). Qed.
Lemma lem2433806 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433807 : term106 = term107.
Proof. exact (@lem2433806 term43 term43). Qed.
Lemma lem2433808 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433809 : term109 = term43.
Proof. exact (EQ_MP (@lem2433808) (@lem940073)). Qed.
Lemma lem2433810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433811 : term107 = term42.
Proof. exact (MK_COMB (@lem2433810) (@lem2433809)). Qed.
Lemma lem2433812 : term106 = term42.
Proof. exact (TRANS (@lem2433807) (@lem2433811)). Qed.
Lemma lem2433814 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433815 : term195 = term54.
Proof. exact (@lem2433814 term43). Qed.
Lemma lem2433816 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2433817 : term196 = term185.
Proof. exact (MK_COMB (@lem2433816) (@lem2433815)). Qed.
Lemma lem2433818 : term193 = term184.
Proof. exact (MK_COMB (@lem2433817) (@lem2433812)). Qed.
Lemma lem2433820 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433821 : term184 = term190.
Proof. exact (@lem2433820 (NUMERAL 0) term43). Qed.
Lemma lem2433822 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433823 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433824 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433823 h1) (fun h1 : term190 = True => @lem2433822)). Qed.
Lemma lem2433825 : term190 = True.
Proof. exact (EQ_MP (@lem2433824) (@lem2433822)). Qed.
Lemma lem2433826 : term184 = True.
Proof. exact (TRANS (@lem2433821) (@lem2433825)). Qed.
Lemma lem2433827 : term193 = True.
Proof. exact (TRANS (@lem2433818) (@lem2433826)). Qed.
Lemma lem2433828 : term187 = True.
Proof. exact (TRANS (@lem2433804) (@lem2433827)). Qed.
Lemma lem2433829 : term184 = True.
Proof. exact (TRANS (@lem2433781) (@lem2433828)). Qed.
Lemma lem2433830 : term183 = True.
Proof. exact (TRANS (@lem2433772) (@lem2433829)). Qed.
Lemma lem2433831 : True = term183.
Proof. exact (SYM (@lem2433830)). Qed.
Lemma lem2433832 : term183.
Proof. exact (EQ_MP (@lem2433831) (@lem0)). Qed.
Lemma lem2433833 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term674 x.
Proof. exact (conj (@lem2433832) (@lem2433695 y x' x h1)). Qed.
Lemma lem2433835 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2433836 (x : int) : term675 x.
Proof. exact (@lem2433835 term42 (term490 x)). Qed.
Lemma lem2433837 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term676 x.
Proof. exact (@lem2433836 x (@lem2433833 y x' x h1)). Qed.
Lemma lem2433838 (x : int) : (term677 x) = (term490 x).
Proof. exact (@lem1982733 (term490 x)). Qed.
Lemma lem2433839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2433840 (x : int) : (term678 x) = (term493 x).
Proof. exact (MK_COMB (@lem2433839) (@lem2433838 x)). Qed.
Lemma lem2433841 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2433842 (x : int) : (term676 x) = (term494 x).
Proof. exact (MK_COMB (@lem2433840 x) (@lem2433841)). Qed.
Lemma lem2433843 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term494 x.
Proof. exact (EQ_MP (@lem2433842 x) (@lem2433837 y x' x h1)). Qed.
Lemma lem2433844 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term612 x.
Proof. exact (conj (@lem2433843 y x' x h1) (@lem2433769 y x' x h1)). Qed.
Lemma lem2433846 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2433847 (x : int) : term679 x.
Proof. exact (@lem2433846 (term490 x) (term117 x)). Qed.
Lemma lem2433848 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term680 x.
Proof. exact (@lem2433847 x (@lem2433844 y x' x h1)). Qed.
Lemma lem2433849 (x : int) : (term681 x) = (term682 x).
Proof. exact (@lem1982753 (term121 x) (real_of_int x) term97 term97). Qed.
Lemma lem2433850 (x : int) : (term683 x) = (term236 x).
Proof. exact (@lem1982713 term97 (real_of_int x)). Qed.
Lemma lem2433852 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2433853 : term42 = term94.
Proof. exact (@lem2433852 term43). Qed.
Lemma lem2433855 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2433856 : term97 = term98.
Proof. exact (@lem2433855 term43). Qed.
Lemma lem2433857 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433858 : term215 = term216.
Proof. exact (MK_COMB (@lem2433857) (@lem2433856)). Qed.
Lemma lem2433859 : term217 = term218.
Proof. exact (MK_COMB (@lem2433858) (@lem2433853)). Qed.
Lemma lem2433860 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2433862 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433863 : term184 = term190.
Proof. exact (@lem2433862 (NUMERAL 0) term43). Qed.
Lemma lem2433864 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433865 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433866 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433865 h1) (fun h1 : term190 = True => @lem2433864)). Qed.
Lemma lem2433867 : term190 = True.
Proof. exact (EQ_MP (@lem2433866) (@lem2433864)). Qed.
Lemma lem2433868 : term184 = True.
Proof. exact (TRANS (@lem2433863) (@lem2433867)). Qed.
Lemma lem2433869 : True = term184.
Proof. exact (SYM (@lem2433868)). Qed.
Lemma lem2433870 : term184.
Proof. exact (EQ_MP (@lem2433869) (@lem0)). Qed.
Lemma lem2433871 : term220.
Proof. exact (@lem2433860 (@lem2433870)). Qed.
Lemma lem2433873 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433874 : term184 = term190.
Proof. exact (@lem2433873 (NUMERAL 0) term43). Qed.
Lemma lem2433875 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433876 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433877 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433876 h1) (fun h1 : term190 = True => @lem2433875)). Qed.
Lemma lem2433878 : term190 = True.
Proof. exact (EQ_MP (@lem2433877) (@lem2433875)). Qed.
Lemma lem2433879 : term184 = True.
Proof. exact (TRANS (@lem2433874) (@lem2433878)). Qed.
Lemma lem2433880 : True = term184.
Proof. exact (SYM (@lem2433879)). Qed.
Lemma lem2433881 : term184.
Proof. exact (EQ_MP (@lem2433880) (@lem0)). Qed.
Lemma lem2433882 : term221.
Proof. exact (@lem2433871 (@lem2433881)). Qed.
Lemma lem2433884 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433885 : term184 = term190.
Proof. exact (@lem2433884 (NUMERAL 0) term43). Qed.
Lemma lem2433886 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433887 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433888 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433887 h1) (fun h1 : term190 = True => @lem2433886)). Qed.
Lemma lem2433889 : term190 = True.
Proof. exact (EQ_MP (@lem2433888) (@lem2433886)). Qed.
Lemma lem2433890 : term184 = True.
Proof. exact (TRANS (@lem2433885) (@lem2433889)). Qed.
Lemma lem2433891 : True = term184.
Proof. exact (SYM (@lem2433890)). Qed.
Lemma lem2433892 : term184.
Proof. exact (EQ_MP (@lem2433891) (@lem0)). Qed.
Lemma lem2433893 : term222.
Proof. exact (@lem2433882 (@lem2433892)). Qed.
Lemma lem2433895 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433896 : term106 = term107.
Proof. exact (@lem2433895 term43 term43). Qed.
Lemma lem2433897 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433898 : term109 = term43.
Proof. exact (EQ_MP (@lem2433897) (@lem940073)). Qed.
Lemma lem2433899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433900 : term107 = term42.
Proof. exact (MK_COMB (@lem2433899) (@lem2433898)). Qed.
Lemma lem2433901 : term106 = term42.
Proof. exact (TRANS (@lem2433896) (@lem2433900)). Qed.
Lemma lem2433903 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2433904 : term101 = term112.
Proof. exact (@lem2433903 term43 term43). Qed.
Lemma lem2433905 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433906 : term109 = term43.
Proof. exact (EQ_MP (@lem2433905) (@lem940073)). Qed.
Lemma lem2433907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433908 : term107 = term42.
Proof. exact (MK_COMB (@lem2433907) (@lem2433906)). Qed.
Lemma lem2433909 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2433910 : term112 = term97.
Proof. exact (MK_COMB (@lem2433909) (@lem2433908)). Qed.
Lemma lem2433911 : term101 = term97.
Proof. exact (TRANS (@lem2433904) (@lem2433910)). Qed.
Lemma lem2433912 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433913 : term223 = term215.
Proof. exact (MK_COMB (@lem2433912) (@lem2433911)). Qed.
Lemma lem2433914 : term224 = term217.
Proof. exact (MK_COMB (@lem2433913) (@lem2433901)). Qed.
Lemma lem2433916 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2433917 : term217 = term54.
Proof. exact (@lem2433916 term43). Qed.
Lemma lem2433918 : term224 = term54.
Proof. exact (TRANS (@lem2433914) (@lem2433917)). Qed.
Lemma lem2433919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2433920 : term226 = term227.
Proof. exact (MK_COMB (@lem2433919) (@lem2433918)). Qed.
Lemma lem2433921 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2433922 : term228 = term195.
Proof. exact (MK_COMB (@lem2433920) (@lem2433921)). Qed.
Lemma lem2433924 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433925 : term195 = term54.
Proof. exact (@lem2433924 term43). Qed.
Lemma lem2433926 : term228 = term54.
Proof. exact (TRANS (@lem2433922) (@lem2433925)). Qed.
Lemma lem2433928 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2433929 : term106 = term107.
Proof. exact (@lem2433928 term43 term43). Qed.
Lemma lem2433930 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2433931 : term109 = term43.
Proof. exact (EQ_MP (@lem2433930) (@lem940073)). Qed.
Lemma lem2433932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2433933 : term107 = term42.
Proof. exact (MK_COMB (@lem2433932) (@lem2433931)). Qed.
Lemma lem2433934 : term106 = term42.
Proof. exact (TRANS (@lem2433929) (@lem2433933)). Qed.
Lemma lem2433935 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2433936 : term229 = term195.
Proof. exact (MK_COMB (@lem2433935) (@lem2433934)). Qed.
Lemma lem2433938 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2433939 : term195 = term54.
Proof. exact (@lem2433938 term43). Qed.
Lemma lem2433940 : term229 = term54.
Proof. exact (TRANS (@lem2433936) (@lem2433939)). Qed.
Lemma lem2433941 : term54 = term229.
Proof. exact (SYM (@lem2433940)). Qed.
Lemma lem2433942 : term228 = term229.
Proof. exact (TRANS (@lem2433926) (@lem2433941)). Qed.
Lemma lem2433943 : term218 = term170.
Proof. exact (@lem2433893 (@lem2433942)). Qed.
Lemma lem2433944 : term217 = term170.
Proof. exact (TRANS (@lem2433859) (@lem2433943)). Qed.
Lemma lem2433946 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2433947 : term170 = term54.
Proof. exact (@lem2433946 term54). Qed.
Lemma lem2433948 : term217 = term54.
Proof. exact (TRANS (@lem2433944) (@lem2433947)). Qed.
Lemma lem2433949 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2433950 : term230 = term227.
Proof. exact (MK_COMB (@lem2433949) (@lem2433948)). Qed.
Lemma lem2433951 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2433952 (x : int) : (term236 x) = (term237 x).
Proof. exact (MK_COMB (@lem2433950) (@lem2433951 x)). Qed.
Lemma lem2433953 (x : int) : (term683 x) = (term237 x).
Proof. exact (TRANS (@lem2433850 x) (@lem2433952 x)). Qed.
Lemma lem2433954 (x : int) : (term237 x) = term54.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2433955 (x : int) : (term683 x) = term54.
Proof. exact (TRANS (@lem2433953 x) (@lem2433954 x)). Qed.
Lemma lem2433956 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433957 (x : int) : (term684 x) = term148.
Proof. exact (MK_COMB (@lem2433956) (@lem2433955 x)). Qed.
Lemma lem2433959 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2433960 : term97 = term98.
Proof. exact (@lem2433959 term43). Qed.
Lemma lem2433962 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2433963 : term97 = term98.
Proof. exact (@lem2433962 term43). Qed.
Lemma lem2433964 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2433965 : term215 = term216.
Proof. exact (MK_COMB (@lem2433964) (@lem2433963)). Qed.
Lemma lem2433966 : term685 = term686.
Proof. exact (MK_COMB (@lem2433965) (@lem2433960)). Qed.
Lemma lem2433967 : term687.
Proof. exact (@lem1981473 term97 term42 term97 term42 term688 term42). Qed.
Lemma lem2433969 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433970 : term184 = term190.
Proof. exact (@lem2433969 (NUMERAL 0) term43). Qed.
Lemma lem2433971 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433972 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433973 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433972 h1) (fun h1 : term190 = True => @lem2433971)). Qed.
Lemma lem2433974 : term190 = True.
Proof. exact (EQ_MP (@lem2433973) (@lem2433971)). Qed.
Lemma lem2433975 : term184 = True.
Proof. exact (TRANS (@lem2433970) (@lem2433974)). Qed.
Lemma lem2433976 : True = term184.
Proof. exact (SYM (@lem2433975)). Qed.
Lemma lem2433977 : term184.
Proof. exact (EQ_MP (@lem2433976) (@lem0)). Qed.
Lemma lem2433978 : term689.
Proof. exact (@lem2433967 (@lem2433977)). Qed.
Lemma lem2433980 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433981 : term184 = term190.
Proof. exact (@lem2433980 (NUMERAL 0) term43). Qed.
Lemma lem2433982 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433983 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433984 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433983 h1) (fun h1 : term190 = True => @lem2433982)). Qed.
Lemma lem2433985 : term190 = True.
Proof. exact (EQ_MP (@lem2433984) (@lem2433982)). Qed.
Lemma lem2433986 : term184 = True.
Proof. exact (TRANS (@lem2433981) (@lem2433985)). Qed.
Lemma lem2433987 : True = term184.
Proof. exact (SYM (@lem2433986)). Qed.
Lemma lem2433988 : term184.
Proof. exact (EQ_MP (@lem2433987) (@lem0)). Qed.
Lemma lem2433989 : term690.
Proof. exact (@lem2433978 (@lem2433988)). Qed.
Lemma lem2433991 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2433992 : term184 = term190.
Proof. exact (@lem2433991 (NUMERAL 0) term43). Qed.
Lemma lem2433993 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2433994 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2433995 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2433994 h1) (fun h1 : term190 = True => @lem2433993)). Qed.
Lemma lem2433996 : term190 = True.
Proof. exact (EQ_MP (@lem2433995) (@lem2433993)). Qed.
Lemma lem2433997 : term184 = True.
Proof. exact (TRANS (@lem2433992) (@lem2433996)). Qed.
Lemma lem2433998 : True = term184.
Proof. exact (SYM (@lem2433997)). Qed.
Lemma lem2433999 : term184.
Proof. exact (EQ_MP (@lem2433998) (@lem0)). Qed.
Lemma lem2434000 : term691.
Proof. exact (@lem2433989 (@lem2433999)). Qed.
Lemma lem2434002 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434003 : term101 = term112.
Proof. exact (@lem2434002 term43 term43). Qed.
Lemma lem2434004 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434005 : term109 = term43.
Proof. exact (EQ_MP (@lem2434004) (@lem940073)). Qed.
Lemma lem2434006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434007 : term107 = term42.
Proof. exact (MK_COMB (@lem2434006) (@lem2434005)). Qed.
Lemma lem2434008 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434009 : term112 = term97.
Proof. exact (MK_COMB (@lem2434008) (@lem2434007)). Qed.
Lemma lem2434010 : term101 = term97.
Proof. exact (TRANS (@lem2434003) (@lem2434009)). Qed.
Lemma lem2434012 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434013 : term101 = term112.
Proof. exact (@lem2434012 term43 term43). Qed.
Lemma lem2434014 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434015 : term109 = term43.
Proof. exact (EQ_MP (@lem2434014) (@lem940073)). Qed.
Lemma lem2434016 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434017 : term107 = term42.
Proof. exact (MK_COMB (@lem2434016) (@lem2434015)). Qed.
Lemma lem2434018 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434019 : term112 = term97.
Proof. exact (MK_COMB (@lem2434018) (@lem2434017)). Qed.
Lemma lem2434020 : term101 = term97.
Proof. exact (TRANS (@lem2434013) (@lem2434019)). Qed.
Lemma lem2434021 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434022 : term223 = term215.
Proof. exact (MK_COMB (@lem2434021) (@lem2434020)). Qed.
Lemma lem2434023 : term692 = term685.
Proof. exact (MK_COMB (@lem2434022) (@lem2434010)). Qed.
Lemma lem2434024 : term685 = term693.
Proof. exact (@lem1367763 term43 term43). Qed.
Lemma lem2434025 : term694 = term695.
Proof. exact (@lem706885). Qed.
Lemma lem2434026 : (term694 = term695) = (term696 = term697).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term695). Qed.
Lemma lem2434027 : term696 = term697.
Proof. exact (EQ_MP (@lem2434026) (@lem2434025)). Qed.
Lemma lem2434028 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434029 : term698 = term699.
Proof. exact (MK_COMB (@lem2434028) (@lem2434027)). Qed.
Lemma lem2434030 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434031 : term693 = term688.
Proof. exact (MK_COMB (@lem2434030) (@lem2434029)). Qed.
Lemma lem2434032 : term685 = term688.
Proof. exact (TRANS (@lem2434024) (@lem2434031)). Qed.
Lemma lem2434033 : term692 = term688.
Proof. exact (TRANS (@lem2434023) (@lem2434032)). Qed.
Lemma lem2434034 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2434035 : term700 = term701.
Proof. exact (MK_COMB (@lem2434034) (@lem2434033)). Qed.
Lemma lem2434036 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2434037 : term702 = term703.
Proof. exact (MK_COMB (@lem2434035) (@lem2434036)). Qed.
Lemma lem2434039 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434040 : term703 = term704.
Proof. exact (@lem2434039 term697 term43). Qed.
Lemma lem2434041 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2434042 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2434043 : term706 = term697.
Proof. exact (EQ_MP (@lem2434042) (@lem2434041)). Qed.
Lemma lem2434044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434045 : term707 = term699.
Proof. exact (MK_COMB (@lem2434044) (@lem2434043)). Qed.
Lemma lem2434046 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434047 : term704 = term688.
Proof. exact (MK_COMB (@lem2434046) (@lem2434045)). Qed.
Lemma lem2434048 : term703 = term688.
Proof. exact (TRANS (@lem2434040) (@lem2434047)). Qed.
Lemma lem2434049 : term702 = term688.
Proof. exact (TRANS (@lem2434037) (@lem2434048)). Qed.
Lemma lem2434051 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434052 : term106 = term107.
Proof. exact (@lem2434051 term43 term43). Qed.
Lemma lem2434053 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434054 : term109 = term43.
Proof. exact (EQ_MP (@lem2434053) (@lem940073)). Qed.
Lemma lem2434055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434056 : term107 = term42.
Proof. exact (MK_COMB (@lem2434055) (@lem2434054)). Qed.
Lemma lem2434057 : term106 = term42.
Proof. exact (TRANS (@lem2434052) (@lem2434056)). Qed.
Lemma lem2434058 : term701 = term701.
Proof. exact (eq_refl term701). Qed.
Lemma lem2434059 : term708 = term703.
Proof. exact (MK_COMB (@lem2434058) (@lem2434057)). Qed.
Lemma lem2434061 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434062 : term703 = term704.
Proof. exact (@lem2434061 term697 term43). Qed.
Lemma lem2434063 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2434064 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2434065 : term706 = term697.
Proof. exact (EQ_MP (@lem2434064) (@lem2434063)). Qed.
Lemma lem2434066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434067 : term707 = term699.
Proof. exact (MK_COMB (@lem2434066) (@lem2434065)). Qed.
Lemma lem2434068 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434069 : term704 = term688.
Proof. exact (MK_COMB (@lem2434068) (@lem2434067)). Qed.
Lemma lem2434070 : term703 = term688.
Proof. exact (TRANS (@lem2434062) (@lem2434069)). Qed.
Lemma lem2434071 : term708 = term688.
Proof. exact (TRANS (@lem2434059) (@lem2434070)). Qed.
Lemma lem2434072 : term688 = term708.
Proof. exact (SYM (@lem2434071)). Qed.
Lemma lem2434073 : term702 = term708.
Proof. exact (TRANS (@lem2434049) (@lem2434072)). Qed.
Lemma lem2434074 : term686 = term709.
Proof. exact (@lem2434000 (@lem2434073)). Qed.
Lemma lem2434075 : term685 = term709.
Proof. exact (TRANS (@lem2433966) (@lem2434074)). Qed.
Lemma lem2434077 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2434078 : term709 = term688.
Proof. exact (@lem2434077 term688). Qed.
Lemma lem2434079 : term685 = term688.
Proof. exact (TRANS (@lem2434075) (@lem2434078)). Qed.
Lemma lem2434080 (x : int) : (term682 x) = term710.
Proof. exact (MK_COMB (@lem2433957 x) (@lem2434079)). Qed.
Lemma lem2434081 (x : int) : (term681 x) = term710.
Proof. exact (TRANS (@lem2433849 x) (@lem2434080 x)). Qed.
Lemma lem2434082 : term710 = term688.
Proof. exact (@lem1982721 term688). Qed.
Lemma lem2434083 (x : int) : (term681 x) = term688.
Proof. exact (TRANS (@lem2434081 x) (@lem2434082)). Qed.
Lemma lem2434084 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2434085 (x : int) : (term711 x) = term712.
Proof. exact (MK_COMB (@lem2434084) (@lem2434083 x)). Qed.
Lemma lem2434086 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2434087 (x : int) : (term680 x) = term713.
Proof. exact (MK_COMB (@lem2434085 x) (@lem2434086)). Qed.
Lemma lem2434088 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : term713.
Proof. exact (EQ_MP (@lem2434087 x) (@lem2433848 y x' x h1)). Qed.
Lemma lem2434090 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2434091 : term713 = term714.
Proof. exact (@lem2434090 term54 term688). Qed.
Lemma lem2434093 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2434094 : term688 = term709.
Proof. exact (@lem2434093 term697). Qed.
Lemma lem2434096 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434097 : term54 = term170.
Proof. exact (@lem2434096 (NUMERAL 0)). Qed.
Lemma lem2434098 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2434099 : term74 = term244.
Proof. exact (MK_COMB (@lem2434098) (@lem2434097)). Qed.
Lemma lem2434100 : term714 = term715.
Proof. exact (MK_COMB (@lem2434099) (@lem2434094)). Qed.
Lemma lem2434101 : term716.
Proof. exact (@lem1980026 term54 term42 term688 term42). Qed.
Lemma lem2434103 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434104 : term184 = term190.
Proof. exact (@lem2434103 (NUMERAL 0) term43). Qed.
Lemma lem2434105 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434106 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434107 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434106 h1) (fun h1 : term190 = True => @lem2434105)). Qed.
Lemma lem2434108 : term190 = True.
Proof. exact (EQ_MP (@lem2434107) (@lem2434105)). Qed.
Lemma lem2434109 : term184 = True.
Proof. exact (TRANS (@lem2434104) (@lem2434108)). Qed.
Lemma lem2434110 : True = term184.
Proof. exact (SYM (@lem2434109)). Qed.
Lemma lem2434111 : term184.
Proof. exact (EQ_MP (@lem2434110) (@lem0)). Qed.
Lemma lem2434112 : term717.
Proof. exact (@lem2434101 (@lem2434111)). Qed.
Lemma lem2434114 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434115 : term184 = term190.
Proof. exact (@lem2434114 (NUMERAL 0) term43). Qed.
Lemma lem2434116 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434117 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434118 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434117 h1) (fun h1 : term190 = True => @lem2434116)). Qed.
Lemma lem2434119 : term190 = True.
Proof. exact (EQ_MP (@lem2434118) (@lem2434116)). Qed.
Lemma lem2434120 : term184 = True.
Proof. exact (TRANS (@lem2434115) (@lem2434119)). Qed.
Lemma lem2434121 : True = term184.
Proof. exact (SYM (@lem2434120)). Qed.
Lemma lem2434122 : term184.
Proof. exact (EQ_MP (@lem2434121) (@lem0)). Qed.
Lemma lem2434123 : term715 = term718.
Proof. exact (@lem2434112 (@lem2434122)). Qed.
Lemma lem2434125 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434126 : term703 = term704.
Proof. exact (@lem2434125 term697 term43). Qed.
Lemma lem2434127 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2434128 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2434129 : term706 = term697.
Proof. exact (EQ_MP (@lem2434128) (@lem2434127)). Qed.
Lemma lem2434130 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434131 : term707 = term699.
Proof. exact (MK_COMB (@lem2434130) (@lem2434129)). Qed.
Lemma lem2434132 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434133 : term704 = term688.
Proof. exact (MK_COMB (@lem2434132) (@lem2434131)). Qed.
Lemma lem2434134 : term703 = term688.
Proof. exact (TRANS (@lem2434126) (@lem2434133)). Qed.
Lemma lem2434136 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434137 : term195 = term54.
Proof. exact (@lem2434136 term43). Qed.
Lemma lem2434138 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2434139 : term249 = term74.
Proof. exact (MK_COMB (@lem2434138) (@lem2434137)). Qed.
Lemma lem2434140 : term718 = term714.
Proof. exact (MK_COMB (@lem2434139) (@lem2434134)). Qed.
Lemma lem2434142 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2434143 : term714 = term719.
Proof. exact (@lem2434142 (NUMERAL 0) term697). Qed.
Lemma lem2434144 : term720 = term695.
Proof. exact (@lem912803). Qed.
Lemma lem2434145 (h1 : term720 = term695) : (term697 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term695 h1). Qed.
Lemma lem2434146 : (term720 = term695) = ((term697 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term720 = term695 => @lem2434145 h1) (fun h1 : (term697 = (NUMERAL 0)) = False => @lem2434144)). Qed.
Lemma lem2434147 : (term697 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2434146) (@lem2434144)). Qed.
Lemma lem2434148 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2434149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2434150 : term253 = (and True).
Proof. exact (MK_COMB (@lem2434149) (@lem2434148)). Qed.
Lemma lem2434151 : term719 = (True /\ False).
Proof. exact (MK_COMB (@lem2434150) (@lem2434147)). Qed.
Lemma lem2434153 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2434154 : term719 = False.
Proof. exact (TRANS (@lem2434151) (@lem2434153)). Qed.
Lemma lem2434155 : term714 = False.
Proof. exact (TRANS (@lem2434143) (@lem2434154)). Qed.
Lemma lem2434156 : term718 = False.
Proof. exact (TRANS (@lem2434140) (@lem2434155)). Qed.
Lemma lem2434157 : term715 = False.
Proof. exact (TRANS (@lem2434123) (@lem2434156)). Qed.
Lemma lem2434158 : term714 = False.
Proof. exact (TRANS (@lem2434100) (@lem2434157)). Qed.
Lemma lem2434159 : term713 = False.
Proof. exact (TRANS (@lem2434091) (@lem2434158)). Qed.
Lemma lem2434160 (y : int) (x' : int) (x : int) (h1 : term620 y x' x) : False.
Proof. exact (EQ_MP (@lem2434159) (@lem2434088 y x' x h1)). Qed.
Lemma lem2434161 (y : int) (x' : int) (x : int) (h1 : term623 y x' x) : False.
Proof. exact (or_elim (@lem2433212 y x' x h1) (fun h0 : term616 y x' x => @lem2433686 y x' x h0) (fun h0 : term620 y x' x => @lem2434160 y x' x h0)). Qed.
Lemma lem2434162 (y : int) (x' : int) (x : int) (h1 : term633 y x' x) : term633 y x' x.
Proof. exact (h1). Qed.
Lemma lem2434163 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term627 y x' x.
Proof. exact (h1). Qed.
Lemma lem2434164 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term625 x' x.
Proof. exact (proj2 (@lem2434163 y x' x h1)). Qed.
Lemma lem2434166 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term624 x' x.
Proof. exact (proj2 (@lem2434164 y x' x h1)). Qed.
Lemma lem2434168 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term612 x.
Proof. exact (proj2 (@lem2434166 y x' x h1)). Qed.
Lemma lem2434170 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term499 x.
Proof. exact (proj2 (@lem2434168 y x' x h1)). Qed.
Lemma lem2434171 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term494 x.
Proof. exact (proj1 (@lem2434168 y x' x h1)). Qed.
Lemma lem2434173 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2434174 : term183 = term184.
Proof. exact (@lem2434173 term54 term42). Qed.
Lemma lem2434176 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434177 : term42 = term94.
Proof. exact (@lem2434176 term43). Qed.
Lemma lem2434179 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434180 : term54 = term170.
Proof. exact (@lem2434179 (NUMERAL 0)). Qed.
Lemma lem2434181 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2434182 : term185 = term186.
Proof. exact (MK_COMB (@lem2434181) (@lem2434180)). Qed.
Lemma lem2434183 : term184 = term187.
Proof. exact (MK_COMB (@lem2434182) (@lem2434177)). Qed.
Lemma lem2434184 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2434186 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434187 : term184 = term190.
Proof. exact (@lem2434186 (NUMERAL 0) term43). Qed.
Lemma lem2434188 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434189 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434190 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434189 h1) (fun h1 : term190 = True => @lem2434188)). Qed.
Lemma lem2434191 : term190 = True.
Proof. exact (EQ_MP (@lem2434190) (@lem2434188)). Qed.
Lemma lem2434192 : term184 = True.
Proof. exact (TRANS (@lem2434187) (@lem2434191)). Qed.
Lemma lem2434193 : True = term184.
Proof. exact (SYM (@lem2434192)). Qed.
Lemma lem2434194 : term184.
Proof. exact (EQ_MP (@lem2434193) (@lem0)). Qed.
Lemma lem2434195 : term192.
Proof. exact (@lem2434184 (@lem2434194)). Qed.
Lemma lem2434197 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434198 : term184 = term190.
Proof. exact (@lem2434197 (NUMERAL 0) term43). Qed.
Lemma lem2434199 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434200 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434201 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434200 h1) (fun h1 : term190 = True => @lem2434199)). Qed.
Lemma lem2434202 : term190 = True.
Proof. exact (EQ_MP (@lem2434201) (@lem2434199)). Qed.
Lemma lem2434203 : term184 = True.
Proof. exact (TRANS (@lem2434198) (@lem2434202)). Qed.
Lemma lem2434204 : True = term184.
Proof. exact (SYM (@lem2434203)). Qed.
Lemma lem2434205 : term184.
Proof. exact (EQ_MP (@lem2434204) (@lem0)). Qed.
Lemma lem2434206 : term187 = term193.
Proof. exact (@lem2434195 (@lem2434205)). Qed.
Lemma lem2434208 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434209 : term106 = term107.
Proof. exact (@lem2434208 term43 term43). Qed.
Lemma lem2434210 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434211 : term109 = term43.
Proof. exact (EQ_MP (@lem2434210) (@lem940073)). Qed.
Lemma lem2434212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434213 : term107 = term42.
Proof. exact (MK_COMB (@lem2434212) (@lem2434211)). Qed.
Lemma lem2434214 : term106 = term42.
Proof. exact (TRANS (@lem2434209) (@lem2434213)). Qed.
Lemma lem2434216 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434217 : term195 = term54.
Proof. exact (@lem2434216 term43). Qed.
Lemma lem2434218 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2434219 : term196 = term185.
Proof. exact (MK_COMB (@lem2434218) (@lem2434217)). Qed.
Lemma lem2434220 : term193 = term184.
Proof. exact (MK_COMB (@lem2434219) (@lem2434214)). Qed.
Lemma lem2434222 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434223 : term184 = term190.
Proof. exact (@lem2434222 (NUMERAL 0) term43). Qed.
Lemma lem2434224 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434225 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434226 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434225 h1) (fun h1 : term190 = True => @lem2434224)). Qed.
Lemma lem2434227 : term190 = True.
Proof. exact (EQ_MP (@lem2434226) (@lem2434224)). Qed.
Lemma lem2434228 : term184 = True.
Proof. exact (TRANS (@lem2434223) (@lem2434227)). Qed.
Lemma lem2434229 : term193 = True.
Proof. exact (TRANS (@lem2434220) (@lem2434228)). Qed.
Lemma lem2434230 : term187 = True.
Proof. exact (TRANS (@lem2434206) (@lem2434229)). Qed.
Lemma lem2434231 : term184 = True.
Proof. exact (TRANS (@lem2434183) (@lem2434230)). Qed.
Lemma lem2434232 : term183 = True.
Proof. exact (TRANS (@lem2434174) (@lem2434231)). Qed.
Lemma lem2434233 : True = term183.
Proof. exact (SYM (@lem2434232)). Qed.
Lemma lem2434234 : term183.
Proof. exact (EQ_MP (@lem2434233) (@lem0)). Qed.
Lemma lem2434235 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term669 x.
Proof. exact (conj (@lem2434234) (@lem2434170 y x' x h1)). Qed.
Lemma lem2434237 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2434238 (x : int) : term670 x.
Proof. exact (@lem2434237 term42 (term117 x)). Qed.
Lemma lem2434239 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term671 x.
Proof. exact (@lem2434238 x (@lem2434235 y x' x h1)). Qed.
Lemma lem2434240 (x : int) : (term672 x) = (term117 x).
Proof. exact (@lem1982733 (term117 x)). Qed.
Lemma lem2434241 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2434242 (x : int) : (term673 x) = (term498 x).
Proof. exact (MK_COMB (@lem2434241) (@lem2434240 x)). Qed.
Lemma lem2434243 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2434244 (x : int) : (term671 x) = (term499 x).
Proof. exact (MK_COMB (@lem2434242 x) (@lem2434243)). Qed.
Lemma lem2434245 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term499 x.
Proof. exact (EQ_MP (@lem2434244 x) (@lem2434239 y x' x h1)). Qed.
Lemma lem2434247 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2434248 : term183 = term184.
Proof. exact (@lem2434247 term54 term42). Qed.
Lemma lem2434250 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434251 : term42 = term94.
Proof. exact (@lem2434250 term43). Qed.
Lemma lem2434253 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434254 : term54 = term170.
Proof. exact (@lem2434253 (NUMERAL 0)). Qed.
Lemma lem2434255 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2434256 : term185 = term186.
Proof. exact (MK_COMB (@lem2434255) (@lem2434254)). Qed.
Lemma lem2434257 : term184 = term187.
Proof. exact (MK_COMB (@lem2434256) (@lem2434251)). Qed.
Lemma lem2434258 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2434260 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434261 : term184 = term190.
Proof. exact (@lem2434260 (NUMERAL 0) term43). Qed.
Lemma lem2434262 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434263 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434264 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434263 h1) (fun h1 : term190 = True => @lem2434262)). Qed.
Lemma lem2434265 : term190 = True.
Proof. exact (EQ_MP (@lem2434264) (@lem2434262)). Qed.
Lemma lem2434266 : term184 = True.
Proof. exact (TRANS (@lem2434261) (@lem2434265)). Qed.
Lemma lem2434267 : True = term184.
Proof. exact (SYM (@lem2434266)). Qed.
Lemma lem2434268 : term184.
Proof. exact (EQ_MP (@lem2434267) (@lem0)). Qed.
Lemma lem2434269 : term192.
Proof. exact (@lem2434258 (@lem2434268)). Qed.
Lemma lem2434271 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434272 : term184 = term190.
Proof. exact (@lem2434271 (NUMERAL 0) term43). Qed.
Lemma lem2434273 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434274 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434275 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434274 h1) (fun h1 : term190 = True => @lem2434273)). Qed.
Lemma lem2434276 : term190 = True.
Proof. exact (EQ_MP (@lem2434275) (@lem2434273)). Qed.
Lemma lem2434277 : term184 = True.
Proof. exact (TRANS (@lem2434272) (@lem2434276)). Qed.
Lemma lem2434278 : True = term184.
Proof. exact (SYM (@lem2434277)). Qed.
Lemma lem2434279 : term184.
Proof. exact (EQ_MP (@lem2434278) (@lem0)). Qed.
Lemma lem2434280 : term187 = term193.
Proof. exact (@lem2434269 (@lem2434279)). Qed.
Lemma lem2434282 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434283 : term106 = term107.
Proof. exact (@lem2434282 term43 term43). Qed.
Lemma lem2434284 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434285 : term109 = term43.
Proof. exact (EQ_MP (@lem2434284) (@lem940073)). Qed.
Lemma lem2434286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434287 : term107 = term42.
Proof. exact (MK_COMB (@lem2434286) (@lem2434285)). Qed.
Lemma lem2434288 : term106 = term42.
Proof. exact (TRANS (@lem2434283) (@lem2434287)). Qed.
Lemma lem2434290 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434291 : term195 = term54.
Proof. exact (@lem2434290 term43). Qed.
Lemma lem2434292 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2434293 : term196 = term185.
Proof. exact (MK_COMB (@lem2434292) (@lem2434291)). Qed.
Lemma lem2434294 : term193 = term184.
Proof. exact (MK_COMB (@lem2434293) (@lem2434288)). Qed.
Lemma lem2434296 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434297 : term184 = term190.
Proof. exact (@lem2434296 (NUMERAL 0) term43). Qed.
Lemma lem2434298 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434299 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434300 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434299 h1) (fun h1 : term190 = True => @lem2434298)). Qed.
Lemma lem2434301 : term190 = True.
Proof. exact (EQ_MP (@lem2434300) (@lem2434298)). Qed.
Lemma lem2434302 : term184 = True.
Proof. exact (TRANS (@lem2434297) (@lem2434301)). Qed.
Lemma lem2434303 : term193 = True.
Proof. exact (TRANS (@lem2434294) (@lem2434302)). Qed.
Lemma lem2434304 : term187 = True.
Proof. exact (TRANS (@lem2434280) (@lem2434303)). Qed.
Lemma lem2434305 : term184 = True.
Proof. exact (TRANS (@lem2434257) (@lem2434304)). Qed.
Lemma lem2434306 : term183 = True.
Proof. exact (TRANS (@lem2434248) (@lem2434305)). Qed.
Lemma lem2434307 : True = term183.
Proof. exact (SYM (@lem2434306)). Qed.
Lemma lem2434308 : term183.
Proof. exact (EQ_MP (@lem2434307) (@lem0)). Qed.
Lemma lem2434309 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term674 x.
Proof. exact (conj (@lem2434308) (@lem2434171 y x' x h1)). Qed.
Lemma lem2434311 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2434312 (x : int) : term675 x.
Proof. exact (@lem2434311 term42 (term490 x)). Qed.
Lemma lem2434313 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term676 x.
Proof. exact (@lem2434312 x (@lem2434309 y x' x h1)). Qed.
Lemma lem2434314 (x : int) : (term677 x) = (term490 x).
Proof. exact (@lem1982733 (term490 x)). Qed.
Lemma lem2434315 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2434316 (x : int) : (term678 x) = (term493 x).
Proof. exact (MK_COMB (@lem2434315) (@lem2434314 x)). Qed.
Lemma lem2434317 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2434318 (x : int) : (term676 x) = (term494 x).
Proof. exact (MK_COMB (@lem2434316 x) (@lem2434317)). Qed.
Lemma lem2434319 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term494 x.
Proof. exact (EQ_MP (@lem2434318 x) (@lem2434313 y x' x h1)). Qed.
Lemma lem2434320 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term612 x.
Proof. exact (conj (@lem2434319 y x' x h1) (@lem2434245 y x' x h1)). Qed.
Lemma lem2434322 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2434323 (x : int) : term679 x.
Proof. exact (@lem2434322 (term490 x) (term117 x)). Qed.
Lemma lem2434324 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term680 x.
Proof. exact (@lem2434323 x (@lem2434320 y x' x h1)). Qed.
Lemma lem2434325 (x : int) : (term681 x) = (term682 x).
Proof. exact (@lem1982753 (term121 x) (real_of_int x) term97 term97). Qed.
Lemma lem2434326 (x : int) : (term683 x) = (term236 x).
Proof. exact (@lem1982713 term97 (real_of_int x)). Qed.
Lemma lem2434328 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434329 : term42 = term94.
Proof. exact (@lem2434328 term43). Qed.
Lemma lem2434331 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2434332 : term97 = term98.
Proof. exact (@lem2434331 term43). Qed.
Lemma lem2434333 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434334 : term215 = term216.
Proof. exact (MK_COMB (@lem2434333) (@lem2434332)). Qed.
Lemma lem2434335 : term217 = term218.
Proof. exact (MK_COMB (@lem2434334) (@lem2434329)). Qed.
Lemma lem2434336 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2434338 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434339 : term184 = term190.
Proof. exact (@lem2434338 (NUMERAL 0) term43). Qed.
Lemma lem2434340 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434341 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434342 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434341 h1) (fun h1 : term190 = True => @lem2434340)). Qed.
Lemma lem2434343 : term190 = True.
Proof. exact (EQ_MP (@lem2434342) (@lem2434340)). Qed.
Lemma lem2434344 : term184 = True.
Proof. exact (TRANS (@lem2434339) (@lem2434343)). Qed.
Lemma lem2434345 : True = term184.
Proof. exact (SYM (@lem2434344)). Qed.
Lemma lem2434346 : term184.
Proof. exact (EQ_MP (@lem2434345) (@lem0)). Qed.
Lemma lem2434347 : term220.
Proof. exact (@lem2434336 (@lem2434346)). Qed.
Lemma lem2434349 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434350 : term184 = term190.
Proof. exact (@lem2434349 (NUMERAL 0) term43). Qed.
Lemma lem2434351 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434352 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434353 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434352 h1) (fun h1 : term190 = True => @lem2434351)). Qed.
Lemma lem2434354 : term190 = True.
Proof. exact (EQ_MP (@lem2434353) (@lem2434351)). Qed.
Lemma lem2434355 : term184 = True.
Proof. exact (TRANS (@lem2434350) (@lem2434354)). Qed.
Lemma lem2434356 : True = term184.
Proof. exact (SYM (@lem2434355)). Qed.
Lemma lem2434357 : term184.
Proof. exact (EQ_MP (@lem2434356) (@lem0)). Qed.
Lemma lem2434358 : term221.
Proof. exact (@lem2434347 (@lem2434357)). Qed.
Lemma lem2434360 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434361 : term184 = term190.
Proof. exact (@lem2434360 (NUMERAL 0) term43). Qed.
Lemma lem2434362 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434363 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434364 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434363 h1) (fun h1 : term190 = True => @lem2434362)). Qed.
Lemma lem2434365 : term190 = True.
Proof. exact (EQ_MP (@lem2434364) (@lem2434362)). Qed.
Lemma lem2434366 : term184 = True.
Proof. exact (TRANS (@lem2434361) (@lem2434365)). Qed.
Lemma lem2434367 : True = term184.
Proof. exact (SYM (@lem2434366)). Qed.
Lemma lem2434368 : term184.
Proof. exact (EQ_MP (@lem2434367) (@lem0)). Qed.
Lemma lem2434369 : term222.
Proof. exact (@lem2434358 (@lem2434368)). Qed.
Lemma lem2434371 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434372 : term106 = term107.
Proof. exact (@lem2434371 term43 term43). Qed.
Lemma lem2434373 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434374 : term109 = term43.
Proof. exact (EQ_MP (@lem2434373) (@lem940073)). Qed.
Lemma lem2434375 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434376 : term107 = term42.
Proof. exact (MK_COMB (@lem2434375) (@lem2434374)). Qed.
Lemma lem2434377 : term106 = term42.
Proof. exact (TRANS (@lem2434372) (@lem2434376)). Qed.
Lemma lem2434379 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434380 : term101 = term112.
Proof. exact (@lem2434379 term43 term43). Qed.
Lemma lem2434381 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434382 : term109 = term43.
Proof. exact (EQ_MP (@lem2434381) (@lem940073)). Qed.
Lemma lem2434383 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434384 : term107 = term42.
Proof. exact (MK_COMB (@lem2434383) (@lem2434382)). Qed.
Lemma lem2434385 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434386 : term112 = term97.
Proof. exact (MK_COMB (@lem2434385) (@lem2434384)). Qed.
Lemma lem2434387 : term101 = term97.
Proof. exact (TRANS (@lem2434380) (@lem2434386)). Qed.
Lemma lem2434388 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434389 : term223 = term215.
Proof. exact (MK_COMB (@lem2434388) (@lem2434387)). Qed.
Lemma lem2434390 : term224 = term217.
Proof. exact (MK_COMB (@lem2434389) (@lem2434377)). Qed.
Lemma lem2434392 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2434393 : term217 = term54.
Proof. exact (@lem2434392 term43). Qed.
Lemma lem2434394 : term224 = term54.
Proof. exact (TRANS (@lem2434390) (@lem2434393)). Qed.
Lemma lem2434395 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2434396 : term226 = term227.
Proof. exact (MK_COMB (@lem2434395) (@lem2434394)). Qed.
Lemma lem2434397 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2434398 : term228 = term195.
Proof. exact (MK_COMB (@lem2434396) (@lem2434397)). Qed.
Lemma lem2434400 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434401 : term195 = term54.
Proof. exact (@lem2434400 term43). Qed.
Lemma lem2434402 : term228 = term54.
Proof. exact (TRANS (@lem2434398) (@lem2434401)). Qed.
Lemma lem2434404 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434405 : term106 = term107.
Proof. exact (@lem2434404 term43 term43). Qed.
Lemma lem2434406 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434407 : term109 = term43.
Proof. exact (EQ_MP (@lem2434406) (@lem940073)). Qed.
Lemma lem2434408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434409 : term107 = term42.
Proof. exact (MK_COMB (@lem2434408) (@lem2434407)). Qed.
Lemma lem2434410 : term106 = term42.
Proof. exact (TRANS (@lem2434405) (@lem2434409)). Qed.
Lemma lem2434411 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2434412 : term229 = term195.
Proof. exact (MK_COMB (@lem2434411) (@lem2434410)). Qed.
Lemma lem2434414 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434415 : term195 = term54.
Proof. exact (@lem2434414 term43). Qed.
Lemma lem2434416 : term229 = term54.
Proof. exact (TRANS (@lem2434412) (@lem2434415)). Qed.
Lemma lem2434417 : term54 = term229.
Proof. exact (SYM (@lem2434416)). Qed.
Lemma lem2434418 : term228 = term229.
Proof. exact (TRANS (@lem2434402) (@lem2434417)). Qed.
Lemma lem2434419 : term218 = term170.
Proof. exact (@lem2434369 (@lem2434418)). Qed.
Lemma lem2434420 : term217 = term170.
Proof. exact (TRANS (@lem2434335) (@lem2434419)). Qed.
Lemma lem2434422 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2434423 : term170 = term54.
Proof. exact (@lem2434422 term54). Qed.
Lemma lem2434424 : term217 = term54.
Proof. exact (TRANS (@lem2434420) (@lem2434423)). Qed.
Lemma lem2434425 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2434426 : term230 = term227.
Proof. exact (MK_COMB (@lem2434425) (@lem2434424)). Qed.
Lemma lem2434427 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2434428 (x : int) : (term236 x) = (term237 x).
Proof. exact (MK_COMB (@lem2434426) (@lem2434427 x)). Qed.
Lemma lem2434429 (x : int) : (term683 x) = (term237 x).
Proof. exact (TRANS (@lem2434326 x) (@lem2434428 x)). Qed.
Lemma lem2434430 (x : int) : (term237 x) = term54.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2434431 (x : int) : (term683 x) = term54.
Proof. exact (TRANS (@lem2434429 x) (@lem2434430 x)). Qed.
Lemma lem2434432 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434433 (x : int) : (term684 x) = term148.
Proof. exact (MK_COMB (@lem2434432) (@lem2434431 x)). Qed.
Lemma lem2434435 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2434436 : term97 = term98.
Proof. exact (@lem2434435 term43). Qed.
Lemma lem2434438 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2434439 : term97 = term98.
Proof. exact (@lem2434438 term43). Qed.
Lemma lem2434440 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434441 : term215 = term216.
Proof. exact (MK_COMB (@lem2434440) (@lem2434439)). Qed.
Lemma lem2434442 : term685 = term686.
Proof. exact (MK_COMB (@lem2434441) (@lem2434436)). Qed.
Lemma lem2434443 : term687.
Proof. exact (@lem1981473 term97 term42 term97 term42 term688 term42). Qed.
Lemma lem2434445 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434446 : term184 = term190.
Proof. exact (@lem2434445 (NUMERAL 0) term43). Qed.
Lemma lem2434447 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434448 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434449 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434448 h1) (fun h1 : term190 = True => @lem2434447)). Qed.
Lemma lem2434450 : term190 = True.
Proof. exact (EQ_MP (@lem2434449) (@lem2434447)). Qed.
Lemma lem2434451 : term184 = True.
Proof. exact (TRANS (@lem2434446) (@lem2434450)). Qed.
Lemma lem2434452 : True = term184.
Proof. exact (SYM (@lem2434451)). Qed.
Lemma lem2434453 : term184.
Proof. exact (EQ_MP (@lem2434452) (@lem0)). Qed.
Lemma lem2434454 : term689.
Proof. exact (@lem2434443 (@lem2434453)). Qed.
Lemma lem2434456 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434457 : term184 = term190.
Proof. exact (@lem2434456 (NUMERAL 0) term43). Qed.
Lemma lem2434458 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434459 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434460 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434459 h1) (fun h1 : term190 = True => @lem2434458)). Qed.
Lemma lem2434461 : term190 = True.
Proof. exact (EQ_MP (@lem2434460) (@lem2434458)). Qed.
Lemma lem2434462 : term184 = True.
Proof. exact (TRANS (@lem2434457) (@lem2434461)). Qed.
Lemma lem2434463 : True = term184.
Proof. exact (SYM (@lem2434462)). Qed.
Lemma lem2434464 : term184.
Proof. exact (EQ_MP (@lem2434463) (@lem0)). Qed.
Lemma lem2434465 : term690.
Proof. exact (@lem2434454 (@lem2434464)). Qed.
Lemma lem2434467 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434468 : term184 = term190.
Proof. exact (@lem2434467 (NUMERAL 0) term43). Qed.
Lemma lem2434469 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434470 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434471 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434470 h1) (fun h1 : term190 = True => @lem2434469)). Qed.
Lemma lem2434472 : term190 = True.
Proof. exact (EQ_MP (@lem2434471) (@lem2434469)). Qed.
Lemma lem2434473 : term184 = True.
Proof. exact (TRANS (@lem2434468) (@lem2434472)). Qed.
Lemma lem2434474 : True = term184.
Proof. exact (SYM (@lem2434473)). Qed.
Lemma lem2434475 : term184.
Proof. exact (EQ_MP (@lem2434474) (@lem0)). Qed.
Lemma lem2434476 : term691.
Proof. exact (@lem2434465 (@lem2434475)). Qed.
Lemma lem2434478 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434479 : term101 = term112.
Proof. exact (@lem2434478 term43 term43). Qed.
Lemma lem2434480 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434481 : term109 = term43.
Proof. exact (EQ_MP (@lem2434480) (@lem940073)). Qed.
Lemma lem2434482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434483 : term107 = term42.
Proof. exact (MK_COMB (@lem2434482) (@lem2434481)). Qed.
Lemma lem2434484 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434485 : term112 = term97.
Proof. exact (MK_COMB (@lem2434484) (@lem2434483)). Qed.
Lemma lem2434486 : term101 = term97.
Proof. exact (TRANS (@lem2434479) (@lem2434485)). Qed.
Lemma lem2434488 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434489 : term101 = term112.
Proof. exact (@lem2434488 term43 term43). Qed.
Lemma lem2434490 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434491 : term109 = term43.
Proof. exact (EQ_MP (@lem2434490) (@lem940073)). Qed.
Lemma lem2434492 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434493 : term107 = term42.
Proof. exact (MK_COMB (@lem2434492) (@lem2434491)). Qed.
Lemma lem2434494 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434495 : term112 = term97.
Proof. exact (MK_COMB (@lem2434494) (@lem2434493)). Qed.
Lemma lem2434496 : term101 = term97.
Proof. exact (TRANS (@lem2434489) (@lem2434495)). Qed.
Lemma lem2434497 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434498 : term223 = term215.
Proof. exact (MK_COMB (@lem2434497) (@lem2434496)). Qed.
Lemma lem2434499 : term692 = term685.
Proof. exact (MK_COMB (@lem2434498) (@lem2434486)). Qed.
Lemma lem2434500 : term685 = term693.
Proof. exact (@lem1367763 term43 term43). Qed.
Lemma lem2434501 : term694 = term695.
Proof. exact (@lem706885). Qed.
Lemma lem2434502 : (term694 = term695) = (term696 = term697).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term695). Qed.
Lemma lem2434503 : term696 = term697.
Proof. exact (EQ_MP (@lem2434502) (@lem2434501)). Qed.
Lemma lem2434504 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434505 : term698 = term699.
Proof. exact (MK_COMB (@lem2434504) (@lem2434503)). Qed.
Lemma lem2434506 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434507 : term693 = term688.
Proof. exact (MK_COMB (@lem2434506) (@lem2434505)). Qed.
Lemma lem2434508 : term685 = term688.
Proof. exact (TRANS (@lem2434500) (@lem2434507)). Qed.
Lemma lem2434509 : term692 = term688.
Proof. exact (TRANS (@lem2434499) (@lem2434508)). Qed.
Lemma lem2434510 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2434511 : term700 = term701.
Proof. exact (MK_COMB (@lem2434510) (@lem2434509)). Qed.
Lemma lem2434512 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2434513 : term702 = term703.
Proof. exact (MK_COMB (@lem2434511) (@lem2434512)). Qed.
Lemma lem2434515 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434516 : term703 = term704.
Proof. exact (@lem2434515 term697 term43). Qed.
Lemma lem2434517 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2434518 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2434519 : term706 = term697.
Proof. exact (EQ_MP (@lem2434518) (@lem2434517)). Qed.
Lemma lem2434520 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434521 : term707 = term699.
Proof. exact (MK_COMB (@lem2434520) (@lem2434519)). Qed.
Lemma lem2434522 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434523 : term704 = term688.
Proof. exact (MK_COMB (@lem2434522) (@lem2434521)). Qed.
Lemma lem2434524 : term703 = term688.
Proof. exact (TRANS (@lem2434516) (@lem2434523)). Qed.
Lemma lem2434525 : term702 = term688.
Proof. exact (TRANS (@lem2434513) (@lem2434524)). Qed.
Lemma lem2434527 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434528 : term106 = term107.
Proof. exact (@lem2434527 term43 term43). Qed.
Lemma lem2434529 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434530 : term109 = term43.
Proof. exact (EQ_MP (@lem2434529) (@lem940073)). Qed.
Lemma lem2434531 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434532 : term107 = term42.
Proof. exact (MK_COMB (@lem2434531) (@lem2434530)). Qed.
Lemma lem2434533 : term106 = term42.
Proof. exact (TRANS (@lem2434528) (@lem2434532)). Qed.
Lemma lem2434534 : term701 = term701.
Proof. exact (eq_refl term701). Qed.
Lemma lem2434535 : term708 = term703.
Proof. exact (MK_COMB (@lem2434534) (@lem2434533)). Qed.
Lemma lem2434537 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434538 : term703 = term704.
Proof. exact (@lem2434537 term697 term43). Qed.
Lemma lem2434539 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2434540 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2434541 : term706 = term697.
Proof. exact (EQ_MP (@lem2434540) (@lem2434539)). Qed.
Lemma lem2434542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434543 : term707 = term699.
Proof. exact (MK_COMB (@lem2434542) (@lem2434541)). Qed.
Lemma lem2434544 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434545 : term704 = term688.
Proof. exact (MK_COMB (@lem2434544) (@lem2434543)). Qed.
Lemma lem2434546 : term703 = term688.
Proof. exact (TRANS (@lem2434538) (@lem2434545)). Qed.
Lemma lem2434547 : term708 = term688.
Proof. exact (TRANS (@lem2434535) (@lem2434546)). Qed.
Lemma lem2434548 : term688 = term708.
Proof. exact (SYM (@lem2434547)). Qed.
Lemma lem2434549 : term702 = term708.
Proof. exact (TRANS (@lem2434525) (@lem2434548)). Qed.
Lemma lem2434550 : term686 = term709.
Proof. exact (@lem2434476 (@lem2434549)). Qed.
Lemma lem2434551 : term685 = term709.
Proof. exact (TRANS (@lem2434442) (@lem2434550)). Qed.
Lemma lem2434553 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2434554 : term709 = term688.
Proof. exact (@lem2434553 term688). Qed.
Lemma lem2434555 : term685 = term688.
Proof. exact (TRANS (@lem2434551) (@lem2434554)). Qed.
Lemma lem2434556 (x : int) : (term682 x) = term710.
Proof. exact (MK_COMB (@lem2434433 x) (@lem2434555)). Qed.
Lemma lem2434557 (x : int) : (term681 x) = term710.
Proof. exact (TRANS (@lem2434325 x) (@lem2434556 x)). Qed.
Lemma lem2434558 : term710 = term688.
Proof. exact (@lem1982721 term688). Qed.
Lemma lem2434559 (x : int) : (term681 x) = term688.
Proof. exact (TRANS (@lem2434557 x) (@lem2434558)). Qed.
Lemma lem2434560 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2434561 (x : int) : (term711 x) = term712.
Proof. exact (MK_COMB (@lem2434560) (@lem2434559 x)). Qed.
Lemma lem2434562 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2434563 (x : int) : (term680 x) = term713.
Proof. exact (MK_COMB (@lem2434561 x) (@lem2434562)). Qed.
Lemma lem2434564 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : term713.
Proof. exact (EQ_MP (@lem2434563 x) (@lem2434324 y x' x h1)). Qed.
Lemma lem2434566 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2434567 : term713 = term714.
Proof. exact (@lem2434566 term54 term688). Qed.
Lemma lem2434569 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2434570 : term688 = term709.
Proof. exact (@lem2434569 term697). Qed.
Lemma lem2434572 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434573 : term54 = term170.
Proof. exact (@lem2434572 (NUMERAL 0)). Qed.
Lemma lem2434574 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2434575 : term74 = term244.
Proof. exact (MK_COMB (@lem2434574) (@lem2434573)). Qed.
Lemma lem2434576 : term714 = term715.
Proof. exact (MK_COMB (@lem2434575) (@lem2434570)). Qed.
Lemma lem2434577 : term716.
Proof. exact (@lem1980026 term54 term42 term688 term42). Qed.
Lemma lem2434579 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434580 : term184 = term190.
Proof. exact (@lem2434579 (NUMERAL 0) term43). Qed.
Lemma lem2434581 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434582 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434583 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434582 h1) (fun h1 : term190 = True => @lem2434581)). Qed.
Lemma lem2434584 : term190 = True.
Proof. exact (EQ_MP (@lem2434583) (@lem2434581)). Qed.
Lemma lem2434585 : term184 = True.
Proof. exact (TRANS (@lem2434580) (@lem2434584)). Qed.
Lemma lem2434586 : True = term184.
Proof. exact (SYM (@lem2434585)). Qed.
Lemma lem2434587 : term184.
Proof. exact (EQ_MP (@lem2434586) (@lem0)). Qed.
Lemma lem2434588 : term717.
Proof. exact (@lem2434577 (@lem2434587)). Qed.
Lemma lem2434590 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434591 : term184 = term190.
Proof. exact (@lem2434590 (NUMERAL 0) term43). Qed.
Lemma lem2434592 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434593 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434594 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434593 h1) (fun h1 : term190 = True => @lem2434592)). Qed.
Lemma lem2434595 : term190 = True.
Proof. exact (EQ_MP (@lem2434594) (@lem2434592)). Qed.
Lemma lem2434596 : term184 = True.
Proof. exact (TRANS (@lem2434591) (@lem2434595)). Qed.
Lemma lem2434597 : True = term184.
Proof. exact (SYM (@lem2434596)). Qed.
Lemma lem2434598 : term184.
Proof. exact (EQ_MP (@lem2434597) (@lem0)). Qed.
Lemma lem2434599 : term715 = term718.
Proof. exact (@lem2434588 (@lem2434598)). Qed.
Lemma lem2434601 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434602 : term703 = term704.
Proof. exact (@lem2434601 term697 term43). Qed.
Lemma lem2434603 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2434604 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2434605 : term706 = term697.
Proof. exact (EQ_MP (@lem2434604) (@lem2434603)). Qed.
Lemma lem2434606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434607 : term707 = term699.
Proof. exact (MK_COMB (@lem2434606) (@lem2434605)). Qed.
Lemma lem2434608 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434609 : term704 = term688.
Proof. exact (MK_COMB (@lem2434608) (@lem2434607)). Qed.
Lemma lem2434610 : term703 = term688.
Proof. exact (TRANS (@lem2434602) (@lem2434609)). Qed.
Lemma lem2434612 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434613 : term195 = term54.
Proof. exact (@lem2434612 term43). Qed.
Lemma lem2434614 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2434615 : term249 = term74.
Proof. exact (MK_COMB (@lem2434614) (@lem2434613)). Qed.
Lemma lem2434616 : term718 = term714.
Proof. exact (MK_COMB (@lem2434615) (@lem2434610)). Qed.
Lemma lem2434618 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2434619 : term714 = term719.
Proof. exact (@lem2434618 (NUMERAL 0) term697). Qed.
Lemma lem2434620 : term720 = term695.
Proof. exact (@lem912803). Qed.
Lemma lem2434621 (h1 : term720 = term695) : (term697 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term695 h1). Qed.
Lemma lem2434622 : (term720 = term695) = ((term697 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term720 = term695 => @lem2434621 h1) (fun h1 : (term697 = (NUMERAL 0)) = False => @lem2434620)). Qed.
Lemma lem2434623 : (term697 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2434622) (@lem2434620)). Qed.
Lemma lem2434624 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2434625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2434626 : term253 = (and True).
Proof. exact (MK_COMB (@lem2434625) (@lem2434624)). Qed.
Lemma lem2434627 : term719 = (True /\ False).
Proof. exact (MK_COMB (@lem2434626) (@lem2434623)). Qed.
Lemma lem2434629 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2434630 : term719 = False.
Proof. exact (TRANS (@lem2434627) (@lem2434629)). Qed.
Lemma lem2434631 : term714 = False.
Proof. exact (TRANS (@lem2434619) (@lem2434630)). Qed.
Lemma lem2434632 : term718 = False.
Proof. exact (TRANS (@lem2434616) (@lem2434631)). Qed.
Lemma lem2434633 : term715 = False.
Proof. exact (TRANS (@lem2434599) (@lem2434632)). Qed.
Lemma lem2434634 : term714 = False.
Proof. exact (TRANS (@lem2434576) (@lem2434633)). Qed.
Lemma lem2434635 : term713 = False.
Proof. exact (TRANS (@lem2434567) (@lem2434634)). Qed.
Lemma lem2434636 (y : int) (x' : int) (x : int) (h1 : term627 y x' x) : False.
Proof. exact (EQ_MP (@lem2434635) (@lem2434564 y x' x h1)). Qed.
Lemma lem2434637 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term630 y x' x.
Proof. exact (h1). Qed.
Lemma lem2434638 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term628 x' x.
Proof. exact (proj2 (@lem2434637 y x' x h1)). Qed.
Lemma lem2434640 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term624 x' x.
Proof. exact (proj2 (@lem2434638 y x' x h1)). Qed.
Lemma lem2434642 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term612 x.
Proof. exact (proj2 (@lem2434640 y x' x h1)). Qed.
Lemma lem2434644 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term499 x.
Proof. exact (proj2 (@lem2434642 y x' x h1)). Qed.
Lemma lem2434645 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term494 x.
Proof. exact (proj1 (@lem2434642 y x' x h1)). Qed.
Lemma lem2434647 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2434648 : term183 = term184.
Proof. exact (@lem2434647 term54 term42). Qed.
Lemma lem2434650 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434651 : term42 = term94.
Proof. exact (@lem2434650 term43). Qed.
Lemma lem2434653 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434654 : term54 = term170.
Proof. exact (@lem2434653 (NUMERAL 0)). Qed.
Lemma lem2434655 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2434656 : term185 = term186.
Proof. exact (MK_COMB (@lem2434655) (@lem2434654)). Qed.
Lemma lem2434657 : term184 = term187.
Proof. exact (MK_COMB (@lem2434656) (@lem2434651)). Qed.
Lemma lem2434658 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2434660 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434661 : term184 = term190.
Proof. exact (@lem2434660 (NUMERAL 0) term43). Qed.
Lemma lem2434662 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434663 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434664 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434663 h1) (fun h1 : term190 = True => @lem2434662)). Qed.
Lemma lem2434665 : term190 = True.
Proof. exact (EQ_MP (@lem2434664) (@lem2434662)). Qed.
Lemma lem2434666 : term184 = True.
Proof. exact (TRANS (@lem2434661) (@lem2434665)). Qed.
Lemma lem2434667 : True = term184.
Proof. exact (SYM (@lem2434666)). Qed.
Lemma lem2434668 : term184.
Proof. exact (EQ_MP (@lem2434667) (@lem0)). Qed.
Lemma lem2434669 : term192.
Proof. exact (@lem2434658 (@lem2434668)). Qed.
Lemma lem2434671 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434672 : term184 = term190.
Proof. exact (@lem2434671 (NUMERAL 0) term43). Qed.
Lemma lem2434673 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434674 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434675 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434674 h1) (fun h1 : term190 = True => @lem2434673)). Qed.
Lemma lem2434676 : term190 = True.
Proof. exact (EQ_MP (@lem2434675) (@lem2434673)). Qed.
Lemma lem2434677 : term184 = True.
Proof. exact (TRANS (@lem2434672) (@lem2434676)). Qed.
Lemma lem2434678 : True = term184.
Proof. exact (SYM (@lem2434677)). Qed.
Lemma lem2434679 : term184.
Proof. exact (EQ_MP (@lem2434678) (@lem0)). Qed.
Lemma lem2434680 : term187 = term193.
Proof. exact (@lem2434669 (@lem2434679)). Qed.
Lemma lem2434682 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434683 : term106 = term107.
Proof. exact (@lem2434682 term43 term43). Qed.
Lemma lem2434684 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434685 : term109 = term43.
Proof. exact (EQ_MP (@lem2434684) (@lem940073)). Qed.
Lemma lem2434686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434687 : term107 = term42.
Proof. exact (MK_COMB (@lem2434686) (@lem2434685)). Qed.
Lemma lem2434688 : term106 = term42.
Proof. exact (TRANS (@lem2434683) (@lem2434687)). Qed.
Lemma lem2434690 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434691 : term195 = term54.
Proof. exact (@lem2434690 term43). Qed.
Lemma lem2434692 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2434693 : term196 = term185.
Proof. exact (MK_COMB (@lem2434692) (@lem2434691)). Qed.
Lemma lem2434694 : term193 = term184.
Proof. exact (MK_COMB (@lem2434693) (@lem2434688)). Qed.
Lemma lem2434696 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434697 : term184 = term190.
Proof. exact (@lem2434696 (NUMERAL 0) term43). Qed.
Lemma lem2434698 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434699 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434700 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434699 h1) (fun h1 : term190 = True => @lem2434698)). Qed.
Lemma lem2434701 : term190 = True.
Proof. exact (EQ_MP (@lem2434700) (@lem2434698)). Qed.
Lemma lem2434702 : term184 = True.
Proof. exact (TRANS (@lem2434697) (@lem2434701)). Qed.
Lemma lem2434703 : term193 = True.
Proof. exact (TRANS (@lem2434694) (@lem2434702)). Qed.
Lemma lem2434704 : term187 = True.
Proof. exact (TRANS (@lem2434680) (@lem2434703)). Qed.
Lemma lem2434705 : term184 = True.
Proof. exact (TRANS (@lem2434657) (@lem2434704)). Qed.
Lemma lem2434706 : term183 = True.
Proof. exact (TRANS (@lem2434648) (@lem2434705)). Qed.
Lemma lem2434707 : True = term183.
Proof. exact (SYM (@lem2434706)). Qed.
Lemma lem2434708 : term183.
Proof. exact (EQ_MP (@lem2434707) (@lem0)). Qed.
Lemma lem2434709 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term669 x.
Proof. exact (conj (@lem2434708) (@lem2434644 y x' x h1)). Qed.
Lemma lem2434711 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2434712 (x : int) : term670 x.
Proof. exact (@lem2434711 term42 (term117 x)). Qed.
Lemma lem2434713 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term671 x.
Proof. exact (@lem2434712 x (@lem2434709 y x' x h1)). Qed.
Lemma lem2434714 (x : int) : (term672 x) = (term117 x).
Proof. exact (@lem1982733 (term117 x)). Qed.
Lemma lem2434715 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2434716 (x : int) : (term673 x) = (term498 x).
Proof. exact (MK_COMB (@lem2434715) (@lem2434714 x)). Qed.
Lemma lem2434717 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2434718 (x : int) : (term671 x) = (term499 x).
Proof. exact (MK_COMB (@lem2434716 x) (@lem2434717)). Qed.
Lemma lem2434719 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term499 x.
Proof. exact (EQ_MP (@lem2434718 x) (@lem2434713 y x' x h1)). Qed.
Lemma lem2434721 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2434722 : term183 = term184.
Proof. exact (@lem2434721 term54 term42). Qed.
Lemma lem2434724 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434725 : term42 = term94.
Proof. exact (@lem2434724 term43). Qed.
Lemma lem2434727 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434728 : term54 = term170.
Proof. exact (@lem2434727 (NUMERAL 0)). Qed.
Lemma lem2434729 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2434730 : term185 = term186.
Proof. exact (MK_COMB (@lem2434729) (@lem2434728)). Qed.
Lemma lem2434731 : term184 = term187.
Proof. exact (MK_COMB (@lem2434730) (@lem2434725)). Qed.
Lemma lem2434732 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2434734 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434735 : term184 = term190.
Proof. exact (@lem2434734 (NUMERAL 0) term43). Qed.
Lemma lem2434736 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434737 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434738 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434737 h1) (fun h1 : term190 = True => @lem2434736)). Qed.
Lemma lem2434739 : term190 = True.
Proof. exact (EQ_MP (@lem2434738) (@lem2434736)). Qed.
Lemma lem2434740 : term184 = True.
Proof. exact (TRANS (@lem2434735) (@lem2434739)). Qed.
Lemma lem2434741 : True = term184.
Proof. exact (SYM (@lem2434740)). Qed.
Lemma lem2434742 : term184.
Proof. exact (EQ_MP (@lem2434741) (@lem0)). Qed.
Lemma lem2434743 : term192.
Proof. exact (@lem2434732 (@lem2434742)). Qed.
Lemma lem2434745 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434746 : term184 = term190.
Proof. exact (@lem2434745 (NUMERAL 0) term43). Qed.
Lemma lem2434747 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434748 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434749 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434748 h1) (fun h1 : term190 = True => @lem2434747)). Qed.
Lemma lem2434750 : term190 = True.
Proof. exact (EQ_MP (@lem2434749) (@lem2434747)). Qed.
Lemma lem2434751 : term184 = True.
Proof. exact (TRANS (@lem2434746) (@lem2434750)). Qed.
Lemma lem2434752 : True = term184.
Proof. exact (SYM (@lem2434751)). Qed.
Lemma lem2434753 : term184.
Proof. exact (EQ_MP (@lem2434752) (@lem0)). Qed.
Lemma lem2434754 : term187 = term193.
Proof. exact (@lem2434743 (@lem2434753)). Qed.
Lemma lem2434756 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434757 : term106 = term107.
Proof. exact (@lem2434756 term43 term43). Qed.
Lemma lem2434758 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434759 : term109 = term43.
Proof. exact (EQ_MP (@lem2434758) (@lem940073)). Qed.
Lemma lem2434760 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434761 : term107 = term42.
Proof. exact (MK_COMB (@lem2434760) (@lem2434759)). Qed.
Lemma lem2434762 : term106 = term42.
Proof. exact (TRANS (@lem2434757) (@lem2434761)). Qed.
Lemma lem2434764 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434765 : term195 = term54.
Proof. exact (@lem2434764 term43). Qed.
Lemma lem2434766 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2434767 : term196 = term185.
Proof. exact (MK_COMB (@lem2434766) (@lem2434765)). Qed.
Lemma lem2434768 : term193 = term184.
Proof. exact (MK_COMB (@lem2434767) (@lem2434762)). Qed.
Lemma lem2434770 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434771 : term184 = term190.
Proof. exact (@lem2434770 (NUMERAL 0) term43). Qed.
Lemma lem2434772 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434773 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434774 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434773 h1) (fun h1 : term190 = True => @lem2434772)). Qed.
Lemma lem2434775 : term190 = True.
Proof. exact (EQ_MP (@lem2434774) (@lem2434772)). Qed.
Lemma lem2434776 : term184 = True.
Proof. exact (TRANS (@lem2434771) (@lem2434775)). Qed.
Lemma lem2434777 : term193 = True.
Proof. exact (TRANS (@lem2434768) (@lem2434776)). Qed.
Lemma lem2434778 : term187 = True.
Proof. exact (TRANS (@lem2434754) (@lem2434777)). Qed.
Lemma lem2434779 : term184 = True.
Proof. exact (TRANS (@lem2434731) (@lem2434778)). Qed.
Lemma lem2434780 : term183 = True.
Proof. exact (TRANS (@lem2434722) (@lem2434779)). Qed.
Lemma lem2434781 : True = term183.
Proof. exact (SYM (@lem2434780)). Qed.
Lemma lem2434782 : term183.
Proof. exact (EQ_MP (@lem2434781) (@lem0)). Qed.
Lemma lem2434783 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term674 x.
Proof. exact (conj (@lem2434782) (@lem2434645 y x' x h1)). Qed.
Lemma lem2434785 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2434786 (x : int) : term675 x.
Proof. exact (@lem2434785 term42 (term490 x)). Qed.
Lemma lem2434787 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term676 x.
Proof. exact (@lem2434786 x (@lem2434783 y x' x h1)). Qed.
Lemma lem2434788 (x : int) : (term677 x) = (term490 x).
Proof. exact (@lem1982733 (term490 x)). Qed.
Lemma lem2434789 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2434790 (x : int) : (term678 x) = (term493 x).
Proof. exact (MK_COMB (@lem2434789) (@lem2434788 x)). Qed.
Lemma lem2434791 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2434792 (x : int) : (term676 x) = (term494 x).
Proof. exact (MK_COMB (@lem2434790 x) (@lem2434791)). Qed.
Lemma lem2434793 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term494 x.
Proof. exact (EQ_MP (@lem2434792 x) (@lem2434787 y x' x h1)). Qed.
Lemma lem2434794 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term612 x.
Proof. exact (conj (@lem2434793 y x' x h1) (@lem2434719 y x' x h1)). Qed.
Lemma lem2434796 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2434797 (x : int) : term679 x.
Proof. exact (@lem2434796 (term490 x) (term117 x)). Qed.
Lemma lem2434798 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term680 x.
Proof. exact (@lem2434797 x (@lem2434794 y x' x h1)). Qed.
Lemma lem2434799 (x : int) : (term681 x) = (term682 x).
Proof. exact (@lem1982753 (term121 x) (real_of_int x) term97 term97). Qed.
Lemma lem2434800 (x : int) : (term683 x) = (term236 x).
Proof. exact (@lem1982713 term97 (real_of_int x)). Qed.
Lemma lem2434802 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2434803 : term42 = term94.
Proof. exact (@lem2434802 term43). Qed.
Lemma lem2434805 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2434806 : term97 = term98.
Proof. exact (@lem2434805 term43). Qed.
Lemma lem2434807 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434808 : term215 = term216.
Proof. exact (MK_COMB (@lem2434807) (@lem2434806)). Qed.
Lemma lem2434809 : term217 = term218.
Proof. exact (MK_COMB (@lem2434808) (@lem2434803)). Qed.
Lemma lem2434810 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2434812 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434813 : term184 = term190.
Proof. exact (@lem2434812 (NUMERAL 0) term43). Qed.
Lemma lem2434814 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434815 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434816 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434815 h1) (fun h1 : term190 = True => @lem2434814)). Qed.
Lemma lem2434817 : term190 = True.
Proof. exact (EQ_MP (@lem2434816) (@lem2434814)). Qed.
Lemma lem2434818 : term184 = True.
Proof. exact (TRANS (@lem2434813) (@lem2434817)). Qed.
Lemma lem2434819 : True = term184.
Proof. exact (SYM (@lem2434818)). Qed.
Lemma lem2434820 : term184.
Proof. exact (EQ_MP (@lem2434819) (@lem0)). Qed.
Lemma lem2434821 : term220.
Proof. exact (@lem2434810 (@lem2434820)). Qed.
Lemma lem2434823 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434824 : term184 = term190.
Proof. exact (@lem2434823 (NUMERAL 0) term43). Qed.
Lemma lem2434825 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434826 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434827 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434826 h1) (fun h1 : term190 = True => @lem2434825)). Qed.
Lemma lem2434828 : term190 = True.
Proof. exact (EQ_MP (@lem2434827) (@lem2434825)). Qed.
Lemma lem2434829 : term184 = True.
Proof. exact (TRANS (@lem2434824) (@lem2434828)). Qed.
Lemma lem2434830 : True = term184.
Proof. exact (SYM (@lem2434829)). Qed.
Lemma lem2434831 : term184.
Proof. exact (EQ_MP (@lem2434830) (@lem0)). Qed.
Lemma lem2434832 : term221.
Proof. exact (@lem2434821 (@lem2434831)). Qed.
Lemma lem2434834 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434835 : term184 = term190.
Proof. exact (@lem2434834 (NUMERAL 0) term43). Qed.
Lemma lem2434836 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434837 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434838 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434837 h1) (fun h1 : term190 = True => @lem2434836)). Qed.
Lemma lem2434839 : term190 = True.
Proof. exact (EQ_MP (@lem2434838) (@lem2434836)). Qed.
Lemma lem2434840 : term184 = True.
Proof. exact (TRANS (@lem2434835) (@lem2434839)). Qed.
Lemma lem2434841 : True = term184.
Proof. exact (SYM (@lem2434840)). Qed.
Lemma lem2434842 : term184.
Proof. exact (EQ_MP (@lem2434841) (@lem0)). Qed.
Lemma lem2434843 : term222.
Proof. exact (@lem2434832 (@lem2434842)). Qed.
Lemma lem2434845 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434846 : term106 = term107.
Proof. exact (@lem2434845 term43 term43). Qed.
Lemma lem2434847 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434848 : term109 = term43.
Proof. exact (EQ_MP (@lem2434847) (@lem940073)). Qed.
Lemma lem2434849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434850 : term107 = term42.
Proof. exact (MK_COMB (@lem2434849) (@lem2434848)). Qed.
Lemma lem2434851 : term106 = term42.
Proof. exact (TRANS (@lem2434846) (@lem2434850)). Qed.
Lemma lem2434853 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434854 : term101 = term112.
Proof. exact (@lem2434853 term43 term43). Qed.
Lemma lem2434855 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434856 : term109 = term43.
Proof. exact (EQ_MP (@lem2434855) (@lem940073)). Qed.
Lemma lem2434857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434858 : term107 = term42.
Proof. exact (MK_COMB (@lem2434857) (@lem2434856)). Qed.
Lemma lem2434859 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434860 : term112 = term97.
Proof. exact (MK_COMB (@lem2434859) (@lem2434858)). Qed.
Lemma lem2434861 : term101 = term97.
Proof. exact (TRANS (@lem2434854) (@lem2434860)). Qed.
Lemma lem2434862 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434863 : term223 = term215.
Proof. exact (MK_COMB (@lem2434862) (@lem2434861)). Qed.
Lemma lem2434864 : term224 = term217.
Proof. exact (MK_COMB (@lem2434863) (@lem2434851)). Qed.
Lemma lem2434866 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2434867 : term217 = term54.
Proof. exact (@lem2434866 term43). Qed.
Lemma lem2434868 : term224 = term54.
Proof. exact (TRANS (@lem2434864) (@lem2434867)). Qed.
Lemma lem2434869 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2434870 : term226 = term227.
Proof. exact (MK_COMB (@lem2434869) (@lem2434868)). Qed.
Lemma lem2434871 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2434872 : term228 = term195.
Proof. exact (MK_COMB (@lem2434870) (@lem2434871)). Qed.
Lemma lem2434874 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434875 : term195 = term54.
Proof. exact (@lem2434874 term43). Qed.
Lemma lem2434876 : term228 = term54.
Proof. exact (TRANS (@lem2434872) (@lem2434875)). Qed.
Lemma lem2434878 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2434879 : term106 = term107.
Proof. exact (@lem2434878 term43 term43). Qed.
Lemma lem2434880 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434881 : term109 = term43.
Proof. exact (EQ_MP (@lem2434880) (@lem940073)). Qed.
Lemma lem2434882 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434883 : term107 = term42.
Proof. exact (MK_COMB (@lem2434882) (@lem2434881)). Qed.
Lemma lem2434884 : term106 = term42.
Proof. exact (TRANS (@lem2434879) (@lem2434883)). Qed.
Lemma lem2434885 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2434886 : term229 = term195.
Proof. exact (MK_COMB (@lem2434885) (@lem2434884)). Qed.
Lemma lem2434888 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2434889 : term195 = term54.
Proof. exact (@lem2434888 term43). Qed.
Lemma lem2434890 : term229 = term54.
Proof. exact (TRANS (@lem2434886) (@lem2434889)). Qed.
Lemma lem2434891 : term54 = term229.
Proof. exact (SYM (@lem2434890)). Qed.
Lemma lem2434892 : term228 = term229.
Proof. exact (TRANS (@lem2434876) (@lem2434891)). Qed.
Lemma lem2434893 : term218 = term170.
Proof. exact (@lem2434843 (@lem2434892)). Qed.
Lemma lem2434894 : term217 = term170.
Proof. exact (TRANS (@lem2434809) (@lem2434893)). Qed.
Lemma lem2434896 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2434897 : term170 = term54.
Proof. exact (@lem2434896 term54). Qed.
Lemma lem2434898 : term217 = term54.
Proof. exact (TRANS (@lem2434894) (@lem2434897)). Qed.
Lemma lem2434899 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2434900 : term230 = term227.
Proof. exact (MK_COMB (@lem2434899) (@lem2434898)). Qed.
Lemma lem2434901 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2434902 (x : int) : (term236 x) = (term237 x).
Proof. exact (MK_COMB (@lem2434900) (@lem2434901 x)). Qed.
Lemma lem2434903 (x : int) : (term683 x) = (term237 x).
Proof. exact (TRANS (@lem2434800 x) (@lem2434902 x)). Qed.
Lemma lem2434904 (x : int) : (term237 x) = term54.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2434905 (x : int) : (term683 x) = term54.
Proof. exact (TRANS (@lem2434903 x) (@lem2434904 x)). Qed.
Lemma lem2434906 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434907 (x : int) : (term684 x) = term148.
Proof. exact (MK_COMB (@lem2434906) (@lem2434905 x)). Qed.
Lemma lem2434909 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2434910 : term97 = term98.
Proof. exact (@lem2434909 term43). Qed.
Lemma lem2434912 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2434913 : term97 = term98.
Proof. exact (@lem2434912 term43). Qed.
Lemma lem2434914 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434915 : term215 = term216.
Proof. exact (MK_COMB (@lem2434914) (@lem2434913)). Qed.
Lemma lem2434916 : term685 = term686.
Proof. exact (MK_COMB (@lem2434915) (@lem2434910)). Qed.
Lemma lem2434917 : term687.
Proof. exact (@lem1981473 term97 term42 term97 term42 term688 term42). Qed.
Lemma lem2434919 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434920 : term184 = term190.
Proof. exact (@lem2434919 (NUMERAL 0) term43). Qed.
Lemma lem2434921 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434922 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434923 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434922 h1) (fun h1 : term190 = True => @lem2434921)). Qed.
Lemma lem2434924 : term190 = True.
Proof. exact (EQ_MP (@lem2434923) (@lem2434921)). Qed.
Lemma lem2434925 : term184 = True.
Proof. exact (TRANS (@lem2434920) (@lem2434924)). Qed.
Lemma lem2434926 : True = term184.
Proof. exact (SYM (@lem2434925)). Qed.
Lemma lem2434927 : term184.
Proof. exact (EQ_MP (@lem2434926) (@lem0)). Qed.
Lemma lem2434928 : term689.
Proof. exact (@lem2434917 (@lem2434927)). Qed.
Lemma lem2434930 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434931 : term184 = term190.
Proof. exact (@lem2434930 (NUMERAL 0) term43). Qed.
Lemma lem2434932 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434933 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434934 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434933 h1) (fun h1 : term190 = True => @lem2434932)). Qed.
Lemma lem2434935 : term190 = True.
Proof. exact (EQ_MP (@lem2434934) (@lem2434932)). Qed.
Lemma lem2434936 : term184 = True.
Proof. exact (TRANS (@lem2434931) (@lem2434935)). Qed.
Lemma lem2434937 : True = term184.
Proof. exact (SYM (@lem2434936)). Qed.
Lemma lem2434938 : term184.
Proof. exact (EQ_MP (@lem2434937) (@lem0)). Qed.
Lemma lem2434939 : term690.
Proof. exact (@lem2434928 (@lem2434938)). Qed.
Lemma lem2434941 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2434942 : term184 = term190.
Proof. exact (@lem2434941 (NUMERAL 0) term43). Qed.
Lemma lem2434943 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2434944 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2434945 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2434944 h1) (fun h1 : term190 = True => @lem2434943)). Qed.
Lemma lem2434946 : term190 = True.
Proof. exact (EQ_MP (@lem2434945) (@lem2434943)). Qed.
Lemma lem2434947 : term184 = True.
Proof. exact (TRANS (@lem2434942) (@lem2434946)). Qed.
Lemma lem2434948 : True = term184.
Proof. exact (SYM (@lem2434947)). Qed.
Lemma lem2434949 : term184.
Proof. exact (EQ_MP (@lem2434948) (@lem0)). Qed.
Lemma lem2434950 : term691.
Proof. exact (@lem2434939 (@lem2434949)). Qed.
Lemma lem2434952 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434953 : term101 = term112.
Proof. exact (@lem2434952 term43 term43). Qed.
Lemma lem2434954 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434955 : term109 = term43.
Proof. exact (EQ_MP (@lem2434954) (@lem940073)). Qed.
Lemma lem2434956 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434957 : term107 = term42.
Proof. exact (MK_COMB (@lem2434956) (@lem2434955)). Qed.
Lemma lem2434958 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434959 : term112 = term97.
Proof. exact (MK_COMB (@lem2434958) (@lem2434957)). Qed.
Lemma lem2434960 : term101 = term97.
Proof. exact (TRANS (@lem2434953) (@lem2434959)). Qed.
Lemma lem2434962 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434963 : term101 = term112.
Proof. exact (@lem2434962 term43 term43). Qed.
Lemma lem2434964 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2434965 : term109 = term43.
Proof. exact (EQ_MP (@lem2434964) (@lem940073)). Qed.
Lemma lem2434966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434967 : term107 = term42.
Proof. exact (MK_COMB (@lem2434966) (@lem2434965)). Qed.
Lemma lem2434968 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434969 : term112 = term97.
Proof. exact (MK_COMB (@lem2434968) (@lem2434967)). Qed.
Lemma lem2434970 : term101 = term97.
Proof. exact (TRANS (@lem2434963) (@lem2434969)). Qed.
Lemma lem2434971 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2434972 : term223 = term215.
Proof. exact (MK_COMB (@lem2434971) (@lem2434970)). Qed.
Lemma lem2434973 : term692 = term685.
Proof. exact (MK_COMB (@lem2434972) (@lem2434960)). Qed.
Lemma lem2434974 : term685 = term693.
Proof. exact (@lem1367763 term43 term43). Qed.
Lemma lem2434975 : term694 = term695.
Proof. exact (@lem706885). Qed.
Lemma lem2434976 : (term694 = term695) = (term696 = term697).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term695). Qed.
Lemma lem2434977 : term696 = term697.
Proof. exact (EQ_MP (@lem2434976) (@lem2434975)). Qed.
Lemma lem2434978 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434979 : term698 = term699.
Proof. exact (MK_COMB (@lem2434978) (@lem2434977)). Qed.
Lemma lem2434980 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434981 : term693 = term688.
Proof. exact (MK_COMB (@lem2434980) (@lem2434979)). Qed.
Lemma lem2434982 : term685 = term688.
Proof. exact (TRANS (@lem2434974) (@lem2434981)). Qed.
Lemma lem2434983 : term692 = term688.
Proof. exact (TRANS (@lem2434973) (@lem2434982)). Qed.
Lemma lem2434984 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2434985 : term700 = term701.
Proof. exact (MK_COMB (@lem2434984) (@lem2434983)). Qed.
Lemma lem2434986 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2434987 : term702 = term703.
Proof. exact (MK_COMB (@lem2434985) (@lem2434986)). Qed.
Lemma lem2434989 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2434990 : term703 = term704.
Proof. exact (@lem2434989 term697 term43). Qed.
Lemma lem2434991 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2434992 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2434993 : term706 = term697.
Proof. exact (EQ_MP (@lem2434992) (@lem2434991)). Qed.
Lemma lem2434994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2434995 : term707 = term699.
Proof. exact (MK_COMB (@lem2434994) (@lem2434993)). Qed.
Lemma lem2434996 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2434997 : term704 = term688.
Proof. exact (MK_COMB (@lem2434996) (@lem2434995)). Qed.
Lemma lem2434998 : term703 = term688.
Proof. exact (TRANS (@lem2434990) (@lem2434997)). Qed.
Lemma lem2434999 : term702 = term688.
Proof. exact (TRANS (@lem2434987) (@lem2434998)). Qed.
Lemma lem2435001 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435002 : term106 = term107.
Proof. exact (@lem2435001 term43 term43). Qed.
Lemma lem2435003 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435004 : term109 = term43.
Proof. exact (EQ_MP (@lem2435003) (@lem940073)). Qed.
Lemma lem2435005 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435006 : term107 = term42.
Proof. exact (MK_COMB (@lem2435005) (@lem2435004)). Qed.
Lemma lem2435007 : term106 = term42.
Proof. exact (TRANS (@lem2435002) (@lem2435006)). Qed.
Lemma lem2435008 : term701 = term701.
Proof. exact (eq_refl term701). Qed.
Lemma lem2435009 : term708 = term703.
Proof. exact (MK_COMB (@lem2435008) (@lem2435007)). Qed.
Lemma lem2435011 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2435012 : term703 = term704.
Proof. exact (@lem2435011 term697 term43). Qed.
Lemma lem2435013 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2435014 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2435015 : term706 = term697.
Proof. exact (EQ_MP (@lem2435014) (@lem2435013)). Qed.
Lemma lem2435016 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435017 : term707 = term699.
Proof. exact (MK_COMB (@lem2435016) (@lem2435015)). Qed.
Lemma lem2435018 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2435019 : term704 = term688.
Proof. exact (MK_COMB (@lem2435018) (@lem2435017)). Qed.
Lemma lem2435020 : term703 = term688.
Proof. exact (TRANS (@lem2435012) (@lem2435019)). Qed.
Lemma lem2435021 : term708 = term688.
Proof. exact (TRANS (@lem2435009) (@lem2435020)). Qed.
Lemma lem2435022 : term688 = term708.
Proof. exact (SYM (@lem2435021)). Qed.
Lemma lem2435023 : term702 = term708.
Proof. exact (TRANS (@lem2434999) (@lem2435022)). Qed.
Lemma lem2435024 : term686 = term709.
Proof. exact (@lem2434950 (@lem2435023)). Qed.
Lemma lem2435025 : term685 = term709.
Proof. exact (TRANS (@lem2434916) (@lem2435024)). Qed.
Lemma lem2435027 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2435028 : term709 = term688.
Proof. exact (@lem2435027 term688). Qed.
Lemma lem2435029 : term685 = term688.
Proof. exact (TRANS (@lem2435025) (@lem2435028)). Qed.
Lemma lem2435030 (x : int) : (term682 x) = term710.
Proof. exact (MK_COMB (@lem2434907 x) (@lem2435029)). Qed.
Lemma lem2435031 (x : int) : (term681 x) = term710.
Proof. exact (TRANS (@lem2434799 x) (@lem2435030 x)). Qed.
Lemma lem2435032 : term710 = term688.
Proof. exact (@lem1982721 term688). Qed.
Lemma lem2435033 (x : int) : (term681 x) = term688.
Proof. exact (TRANS (@lem2435031 x) (@lem2435032)). Qed.
Lemma lem2435034 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435035 (x : int) : (term711 x) = term712.
Proof. exact (MK_COMB (@lem2435034) (@lem2435033 x)). Qed.
Lemma lem2435036 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435037 (x : int) : (term680 x) = term713.
Proof. exact (MK_COMB (@lem2435035 x) (@lem2435036)). Qed.
Lemma lem2435038 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : term713.
Proof. exact (EQ_MP (@lem2435037 x) (@lem2434798 y x' x h1)). Qed.
Lemma lem2435040 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2435041 : term713 = term714.
Proof. exact (@lem2435040 term54 term688). Qed.
Lemma lem2435043 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2435044 : term688 = term709.
Proof. exact (@lem2435043 term697). Qed.
Lemma lem2435046 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435047 : term54 = term170.
Proof. exact (@lem2435046 (NUMERAL 0)). Qed.
Lemma lem2435048 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2435049 : term74 = term244.
Proof. exact (MK_COMB (@lem2435048) (@lem2435047)). Qed.
Lemma lem2435050 : term714 = term715.
Proof. exact (MK_COMB (@lem2435049) (@lem2435044)). Qed.
Lemma lem2435051 : term716.
Proof. exact (@lem1980026 term54 term42 term688 term42). Qed.
Lemma lem2435053 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435054 : term184 = term190.
Proof. exact (@lem2435053 (NUMERAL 0) term43). Qed.
Lemma lem2435055 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435056 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435057 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435056 h1) (fun h1 : term190 = True => @lem2435055)). Qed.
Lemma lem2435058 : term190 = True.
Proof. exact (EQ_MP (@lem2435057) (@lem2435055)). Qed.
Lemma lem2435059 : term184 = True.
Proof. exact (TRANS (@lem2435054) (@lem2435058)). Qed.
Lemma lem2435060 : True = term184.
Proof. exact (SYM (@lem2435059)). Qed.
Lemma lem2435061 : term184.
Proof. exact (EQ_MP (@lem2435060) (@lem0)). Qed.
Lemma lem2435062 : term717.
Proof. exact (@lem2435051 (@lem2435061)). Qed.
Lemma lem2435064 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435065 : term184 = term190.
Proof. exact (@lem2435064 (NUMERAL 0) term43). Qed.
Lemma lem2435066 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435067 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435068 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435067 h1) (fun h1 : term190 = True => @lem2435066)). Qed.
Lemma lem2435069 : term190 = True.
Proof. exact (EQ_MP (@lem2435068) (@lem2435066)). Qed.
Lemma lem2435070 : term184 = True.
Proof. exact (TRANS (@lem2435065) (@lem2435069)). Qed.
Lemma lem2435071 : True = term184.
Proof. exact (SYM (@lem2435070)). Qed.
Lemma lem2435072 : term184.
Proof. exact (EQ_MP (@lem2435071) (@lem0)). Qed.
Lemma lem2435073 : term715 = term718.
Proof. exact (@lem2435062 (@lem2435072)). Qed.
Lemma lem2435075 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2435076 : term703 = term704.
Proof. exact (@lem2435075 term697 term43). Qed.
Lemma lem2435077 : term705 = term695.
Proof. exact (@lem996237 term695). Qed.
Lemma lem2435078 : (term705 = term695) = (term706 = term697).
Proof. exact (@lem1007663 term695 (BIT1 0) term695). Qed.
Lemma lem2435079 : term706 = term697.
Proof. exact (EQ_MP (@lem2435078) (@lem2435077)). Qed.
Lemma lem2435080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435081 : term707 = term699.
Proof. exact (MK_COMB (@lem2435080) (@lem2435079)). Qed.
Lemma lem2435082 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2435083 : term704 = term688.
Proof. exact (MK_COMB (@lem2435082) (@lem2435081)). Qed.
Lemma lem2435084 : term703 = term688.
Proof. exact (TRANS (@lem2435076) (@lem2435083)). Qed.
Lemma lem2435086 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435087 : term195 = term54.
Proof. exact (@lem2435086 term43). Qed.
Lemma lem2435088 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2435089 : term249 = term74.
Proof. exact (MK_COMB (@lem2435088) (@lem2435087)). Qed.
Lemma lem2435090 : term718 = term714.
Proof. exact (MK_COMB (@lem2435089) (@lem2435084)). Qed.
Lemma lem2435092 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2435093 : term714 = term719.
Proof. exact (@lem2435092 (NUMERAL 0) term697). Qed.
Lemma lem2435094 : term720 = term695.
Proof. exact (@lem912803). Qed.
Lemma lem2435095 (h1 : term720 = term695) : (term697 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term695 h1). Qed.
Lemma lem2435096 : (term720 = term695) = ((term697 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term720 = term695 => @lem2435095 h1) (fun h1 : (term697 = (NUMERAL 0)) = False => @lem2435094)). Qed.
Lemma lem2435097 : (term697 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2435096) (@lem2435094)). Qed.
Lemma lem2435098 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2435099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2435100 : term253 = (and True).
Proof. exact (MK_COMB (@lem2435099) (@lem2435098)). Qed.
Lemma lem2435101 : term719 = (True /\ False).
Proof. exact (MK_COMB (@lem2435100) (@lem2435097)). Qed.
Lemma lem2435103 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2435104 : term719 = False.
Proof. exact (TRANS (@lem2435101) (@lem2435103)). Qed.
Lemma lem2435105 : term714 = False.
Proof. exact (TRANS (@lem2435093) (@lem2435104)). Qed.
Lemma lem2435106 : term718 = False.
Proof. exact (TRANS (@lem2435090) (@lem2435105)). Qed.
Lemma lem2435107 : term715 = False.
Proof. exact (TRANS (@lem2435073) (@lem2435106)). Qed.
Lemma lem2435108 : term714 = False.
Proof. exact (TRANS (@lem2435050) (@lem2435107)). Qed.
Lemma lem2435109 : term713 = False.
Proof. exact (TRANS (@lem2435041) (@lem2435108)). Qed.
Lemma lem2435110 (y : int) (x' : int) (x : int) (h1 : term630 y x' x) : False.
Proof. exact (EQ_MP (@lem2435109) (@lem2435038 y x' x h1)). Qed.
Lemma lem2435111 (y : int) (x' : int) (x : int) (h1 : term633 y x' x) : False.
Proof. exact (or_elim (@lem2434162 y x' x h1) (fun h0 : term627 y x' x => @lem2434636 y x' x h0) (fun h0 : term630 y x' x => @lem2435110 y x' x h0)). Qed.
Lemma lem2435112 (y : int) (x' : int) (x : int) (h1 : term635 y x' x) : False.
Proof. exact (or_elim (@lem2433211 y x' x h1) (fun h0 : term623 y x' x => @lem2434161 y x' x h0) (fun h0 : term633 y x' x => @lem2435111 y x' x h0)). Qed.
Lemma lem2435113 (y : int) (x : int) (x' : int) (h1 : term666 y x x') : term666 y x x'.
Proof. exact (h1). Qed.
Lemma lem2435114 (y : int) (x : int) (x' : int) (h1 : term654 y x x') : term654 y x x'.
Proof. exact (h1). Qed.
Lemma lem2435115 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term648 y x x'.
Proof. exact (h1). Qed.
Lemma lem2435116 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term646 x x'.
Proof. exact (proj2 (@lem2435115 y x x' h1)). Qed.
Lemma lem2435118 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term645 x'.
Proof. exact (proj2 (@lem2435116 y x x' h1)). Qed.
Lemma lem2435120 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term644 x'.
Proof. exact (proj2 (@lem2435118 y x x' h1)). Qed.
Lemma lem2435121 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term494 x'.
Proof. exact (proj1 (@lem2435118 y x x' h1)). Qed.
Lemma lem2435122 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term642 x'.
Proof. exact (proj2 (@lem2435120 y x x' h1)). Qed.
Lemma lem2435125 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2435126 : term183 = term184.
Proof. exact (@lem2435125 term54 term42). Qed.
Lemma lem2435128 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435129 : term42 = term94.
Proof. exact (@lem2435128 term43). Qed.
Lemma lem2435131 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435132 : term54 = term170.
Proof. exact (@lem2435131 (NUMERAL 0)). Qed.
Lemma lem2435133 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435134 : term185 = term186.
Proof. exact (MK_COMB (@lem2435133) (@lem2435132)). Qed.
Lemma lem2435135 : term184 = term187.
Proof. exact (MK_COMB (@lem2435134) (@lem2435129)). Qed.
Lemma lem2435136 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2435138 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435139 : term184 = term190.
Proof. exact (@lem2435138 (NUMERAL 0) term43). Qed.
Lemma lem2435140 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435141 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435142 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435141 h1) (fun h1 : term190 = True => @lem2435140)). Qed.
Lemma lem2435143 : term190 = True.
Proof. exact (EQ_MP (@lem2435142) (@lem2435140)). Qed.
Lemma lem2435144 : term184 = True.
Proof. exact (TRANS (@lem2435139) (@lem2435143)). Qed.
Lemma lem2435145 : True = term184.
Proof. exact (SYM (@lem2435144)). Qed.
Lemma lem2435146 : term184.
Proof. exact (EQ_MP (@lem2435145) (@lem0)). Qed.
Lemma lem2435147 : term192.
Proof. exact (@lem2435136 (@lem2435146)). Qed.
Lemma lem2435149 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435150 : term184 = term190.
Proof. exact (@lem2435149 (NUMERAL 0) term43). Qed.
Lemma lem2435151 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435152 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435153 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435152 h1) (fun h1 : term190 = True => @lem2435151)). Qed.
Lemma lem2435154 : term190 = True.
Proof. exact (EQ_MP (@lem2435153) (@lem2435151)). Qed.
Lemma lem2435155 : term184 = True.
Proof. exact (TRANS (@lem2435150) (@lem2435154)). Qed.
Lemma lem2435156 : True = term184.
Proof. exact (SYM (@lem2435155)). Qed.
Lemma lem2435157 : term184.
Proof. exact (EQ_MP (@lem2435156) (@lem0)). Qed.
Lemma lem2435158 : term187 = term193.
Proof. exact (@lem2435147 (@lem2435157)). Qed.
Lemma lem2435160 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435161 : term106 = term107.
Proof. exact (@lem2435160 term43 term43). Qed.
Lemma lem2435162 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435163 : term109 = term43.
Proof. exact (EQ_MP (@lem2435162) (@lem940073)). Qed.
Lemma lem2435164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435165 : term107 = term42.
Proof. exact (MK_COMB (@lem2435164) (@lem2435163)). Qed.
Lemma lem2435166 : term106 = term42.
Proof. exact (TRANS (@lem2435161) (@lem2435165)). Qed.
Lemma lem2435168 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435169 : term195 = term54.
Proof. exact (@lem2435168 term43). Qed.
Lemma lem2435170 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435171 : term196 = term185.
Proof. exact (MK_COMB (@lem2435170) (@lem2435169)). Qed.
Lemma lem2435172 : term193 = term184.
Proof. exact (MK_COMB (@lem2435171) (@lem2435166)). Qed.
Lemma lem2435174 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435175 : term184 = term190.
Proof. exact (@lem2435174 (NUMERAL 0) term43). Qed.
Lemma lem2435176 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435177 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435178 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435177 h1) (fun h1 : term190 = True => @lem2435176)). Qed.
Lemma lem2435179 : term190 = True.
Proof. exact (EQ_MP (@lem2435178) (@lem2435176)). Qed.
Lemma lem2435180 : term184 = True.
Proof. exact (TRANS (@lem2435175) (@lem2435179)). Qed.
Lemma lem2435181 : term193 = True.
Proof. exact (TRANS (@lem2435172) (@lem2435180)). Qed.
Lemma lem2435182 : term187 = True.
Proof. exact (TRANS (@lem2435158) (@lem2435181)). Qed.
Lemma lem2435183 : term184 = True.
Proof. exact (TRANS (@lem2435135) (@lem2435182)). Qed.
Lemma lem2435184 : term183 = True.
Proof. exact (TRANS (@lem2435126) (@lem2435183)). Qed.
Lemma lem2435185 : True = term183.
Proof. exact (SYM (@lem2435184)). Qed.
Lemma lem2435186 : term183.
Proof. exact (EQ_MP (@lem2435185) (@lem0)). Qed.
Lemma lem2435187 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term721 x'.
Proof. exact (conj (@lem2435186) (@lem2435122 y x x' h1)). Qed.
Lemma lem2435189 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2435190 (x' : int) : term722 x'.
Proof. exact (@lem2435189 term42 (real_of_int x')). Qed.
Lemma lem2435191 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term641 x'.
Proof. exact (@lem2435190 x' (@lem2435187 y x x' h1)). Qed.
Lemma lem2435192 (x' : int) : (term144 x') = (real_of_int x').
Proof. exact (@lem1982733 (real_of_int x')). Qed.
Lemma lem2435193 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435194 (x' : int) : (term639 x') = (term640 x').
Proof. exact (MK_COMB (@lem2435193) (@lem2435192 x')). Qed.
Lemma lem2435195 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435196 (x' : int) : (term641 x') = (term642 x').
Proof. exact (MK_COMB (@lem2435194 x') (@lem2435195)). Qed.
Lemma lem2435197 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term642 x'.
Proof. exact (EQ_MP (@lem2435196 x') (@lem2435191 y x x' h1)). Qed.
Lemma lem2435199 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2435200 : term183 = term184.
Proof. exact (@lem2435199 term54 term42). Qed.
Lemma lem2435202 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435203 : term42 = term94.
Proof. exact (@lem2435202 term43). Qed.
Lemma lem2435205 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435206 : term54 = term170.
Proof. exact (@lem2435205 (NUMERAL 0)). Qed.
Lemma lem2435207 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435208 : term185 = term186.
Proof. exact (MK_COMB (@lem2435207) (@lem2435206)). Qed.
Lemma lem2435209 : term184 = term187.
Proof. exact (MK_COMB (@lem2435208) (@lem2435203)). Qed.
Lemma lem2435210 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2435212 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435213 : term184 = term190.
Proof. exact (@lem2435212 (NUMERAL 0) term43). Qed.
Lemma lem2435214 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435215 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435216 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435215 h1) (fun h1 : term190 = True => @lem2435214)). Qed.
Lemma lem2435217 : term190 = True.
Proof. exact (EQ_MP (@lem2435216) (@lem2435214)). Qed.
Lemma lem2435218 : term184 = True.
Proof. exact (TRANS (@lem2435213) (@lem2435217)). Qed.
Lemma lem2435219 : True = term184.
Proof. exact (SYM (@lem2435218)). Qed.
Lemma lem2435220 : term184.
Proof. exact (EQ_MP (@lem2435219) (@lem0)). Qed.
Lemma lem2435221 : term192.
Proof. exact (@lem2435210 (@lem2435220)). Qed.
Lemma lem2435223 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435224 : term184 = term190.
Proof. exact (@lem2435223 (NUMERAL 0) term43). Qed.
Lemma lem2435225 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435226 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435227 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435226 h1) (fun h1 : term190 = True => @lem2435225)). Qed.
Lemma lem2435228 : term190 = True.
Proof. exact (EQ_MP (@lem2435227) (@lem2435225)). Qed.
Lemma lem2435229 : term184 = True.
Proof. exact (TRANS (@lem2435224) (@lem2435228)). Qed.
Lemma lem2435230 : True = term184.
Proof. exact (SYM (@lem2435229)). Qed.
Lemma lem2435231 : term184.
Proof. exact (EQ_MP (@lem2435230) (@lem0)). Qed.
Lemma lem2435232 : term187 = term193.
Proof. exact (@lem2435221 (@lem2435231)). Qed.
Lemma lem2435234 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435235 : term106 = term107.
Proof. exact (@lem2435234 term43 term43). Qed.
Lemma lem2435236 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435237 : term109 = term43.
Proof. exact (EQ_MP (@lem2435236) (@lem940073)). Qed.
Lemma lem2435238 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435239 : term107 = term42.
Proof. exact (MK_COMB (@lem2435238) (@lem2435237)). Qed.
Lemma lem2435240 : term106 = term42.
Proof. exact (TRANS (@lem2435235) (@lem2435239)). Qed.
Lemma lem2435242 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435243 : term195 = term54.
Proof. exact (@lem2435242 term43). Qed.
Lemma lem2435244 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435245 : term196 = term185.
Proof. exact (MK_COMB (@lem2435244) (@lem2435243)). Qed.
Lemma lem2435246 : term193 = term184.
Proof. exact (MK_COMB (@lem2435245) (@lem2435240)). Qed.
Lemma lem2435248 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435249 : term184 = term190.
Proof. exact (@lem2435248 (NUMERAL 0) term43). Qed.
Lemma lem2435250 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435251 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435252 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435251 h1) (fun h1 : term190 = True => @lem2435250)). Qed.
Lemma lem2435253 : term190 = True.
Proof. exact (EQ_MP (@lem2435252) (@lem2435250)). Qed.
Lemma lem2435254 : term184 = True.
Proof. exact (TRANS (@lem2435249) (@lem2435253)). Qed.
Lemma lem2435255 : term193 = True.
Proof. exact (TRANS (@lem2435246) (@lem2435254)). Qed.
Lemma lem2435256 : term187 = True.
Proof. exact (TRANS (@lem2435232) (@lem2435255)). Qed.
Lemma lem2435257 : term184 = True.
Proof. exact (TRANS (@lem2435209) (@lem2435256)). Qed.
Lemma lem2435258 : term183 = True.
Proof. exact (TRANS (@lem2435200) (@lem2435257)). Qed.
Lemma lem2435259 : True = term183.
Proof. exact (SYM (@lem2435258)). Qed.
Lemma lem2435260 : term183.
Proof. exact (EQ_MP (@lem2435259) (@lem0)). Qed.
Lemma lem2435261 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term674 x'.
Proof. exact (conj (@lem2435260) (@lem2435121 y x x' h1)). Qed.
Lemma lem2435263 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2435264 (x' : int) : term675 x'.
Proof. exact (@lem2435263 term42 (term490 x')). Qed.
Lemma lem2435265 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term676 x'.
Proof. exact (@lem2435264 x' (@lem2435261 y x x' h1)). Qed.
Lemma lem2435266 (x' : int) : (term677 x') = (term490 x').
Proof. exact (@lem1982733 (term490 x')). Qed.
Lemma lem2435267 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435268 (x' : int) : (term678 x') = (term493 x').
Proof. exact (MK_COMB (@lem2435267) (@lem2435266 x')). Qed.
Lemma lem2435269 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435270 (x' : int) : (term676 x') = (term494 x').
Proof. exact (MK_COMB (@lem2435268 x') (@lem2435269)). Qed.
Lemma lem2435271 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term494 x'.
Proof. exact (EQ_MP (@lem2435270 x') (@lem2435265 y x x' h1)). Qed.
Lemma lem2435272 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term723 x'.
Proof. exact (conj (@lem2435271 y x x' h1) (@lem2435197 y x x' h1)). Qed.
Lemma lem2435274 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2435275 (x' : int) : term724 x'.
Proof. exact (@lem2435274 (term490 x') (real_of_int x')). Qed.
Lemma lem2435276 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term725 x'.
Proof. exact (@lem2435275 x' (@lem2435272 y x x' h1)). Qed.
Lemma lem2435277 (x' : int) : (term726 x') = (term727 x').
Proof. exact (@lem1982759 (term121 x') (real_of_int x') term97). Qed.
Lemma lem2435278 (x' : int) : (term683 x') = (term236 x').
Proof. exact (@lem1982713 term97 (real_of_int x')). Qed.
Lemma lem2435280 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435281 : term42 = term94.
Proof. exact (@lem2435280 term43). Qed.
Lemma lem2435283 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2435284 : term97 = term98.
Proof. exact (@lem2435283 term43). Qed.
Lemma lem2435285 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2435286 : term215 = term216.
Proof. exact (MK_COMB (@lem2435285) (@lem2435284)). Qed.
Lemma lem2435287 : term217 = term218.
Proof. exact (MK_COMB (@lem2435286) (@lem2435281)). Qed.
Lemma lem2435288 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2435290 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435291 : term184 = term190.
Proof. exact (@lem2435290 (NUMERAL 0) term43). Qed.
Lemma lem2435292 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435293 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435294 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435293 h1) (fun h1 : term190 = True => @lem2435292)). Qed.
Lemma lem2435295 : term190 = True.
Proof. exact (EQ_MP (@lem2435294) (@lem2435292)). Qed.
Lemma lem2435296 : term184 = True.
Proof. exact (TRANS (@lem2435291) (@lem2435295)). Qed.
Lemma lem2435297 : True = term184.
Proof. exact (SYM (@lem2435296)). Qed.
Lemma lem2435298 : term184.
Proof. exact (EQ_MP (@lem2435297) (@lem0)). Qed.
Lemma lem2435299 : term220.
Proof. exact (@lem2435288 (@lem2435298)). Qed.
Lemma lem2435301 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435302 : term184 = term190.
Proof. exact (@lem2435301 (NUMERAL 0) term43). Qed.
Lemma lem2435303 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435304 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435305 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435304 h1) (fun h1 : term190 = True => @lem2435303)). Qed.
Lemma lem2435306 : term190 = True.
Proof. exact (EQ_MP (@lem2435305) (@lem2435303)). Qed.
Lemma lem2435307 : term184 = True.
Proof. exact (TRANS (@lem2435302) (@lem2435306)). Qed.
Lemma lem2435308 : True = term184.
Proof. exact (SYM (@lem2435307)). Qed.
Lemma lem2435309 : term184.
Proof. exact (EQ_MP (@lem2435308) (@lem0)). Qed.
Lemma lem2435310 : term221.
Proof. exact (@lem2435299 (@lem2435309)). Qed.
Lemma lem2435312 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435313 : term184 = term190.
Proof. exact (@lem2435312 (NUMERAL 0) term43). Qed.
Lemma lem2435314 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435315 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435316 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435315 h1) (fun h1 : term190 = True => @lem2435314)). Qed.
Lemma lem2435317 : term190 = True.
Proof. exact (EQ_MP (@lem2435316) (@lem2435314)). Qed.
Lemma lem2435318 : term184 = True.
Proof. exact (TRANS (@lem2435313) (@lem2435317)). Qed.
Lemma lem2435319 : True = term184.
Proof. exact (SYM (@lem2435318)). Qed.
Lemma lem2435320 : term184.
Proof. exact (EQ_MP (@lem2435319) (@lem0)). Qed.
Lemma lem2435321 : term222.
Proof. exact (@lem2435310 (@lem2435320)). Qed.
Lemma lem2435323 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435324 : term106 = term107.
Proof. exact (@lem2435323 term43 term43). Qed.
Lemma lem2435325 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435326 : term109 = term43.
Proof. exact (EQ_MP (@lem2435325) (@lem940073)). Qed.
Lemma lem2435327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435328 : term107 = term42.
Proof. exact (MK_COMB (@lem2435327) (@lem2435326)). Qed.
Lemma lem2435329 : term106 = term42.
Proof. exact (TRANS (@lem2435324) (@lem2435328)). Qed.
Lemma lem2435331 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2435332 : term101 = term112.
Proof. exact (@lem2435331 term43 term43). Qed.
Lemma lem2435333 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435334 : term109 = term43.
Proof. exact (EQ_MP (@lem2435333) (@lem940073)). Qed.
Lemma lem2435335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435336 : term107 = term42.
Proof. exact (MK_COMB (@lem2435335) (@lem2435334)). Qed.
Lemma lem2435337 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2435338 : term112 = term97.
Proof. exact (MK_COMB (@lem2435337) (@lem2435336)). Qed.
Lemma lem2435339 : term101 = term97.
Proof. exact (TRANS (@lem2435332) (@lem2435338)). Qed.
Lemma lem2435340 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2435341 : term223 = term215.
Proof. exact (MK_COMB (@lem2435340) (@lem2435339)). Qed.
Lemma lem2435342 : term224 = term217.
Proof. exact (MK_COMB (@lem2435341) (@lem2435329)). Qed.
Lemma lem2435344 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2435345 : term217 = term54.
Proof. exact (@lem2435344 term43). Qed.
Lemma lem2435346 : term224 = term54.
Proof. exact (TRANS (@lem2435342) (@lem2435345)). Qed.
Lemma lem2435347 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2435348 : term226 = term227.
Proof. exact (MK_COMB (@lem2435347) (@lem2435346)). Qed.
Lemma lem2435349 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2435350 : term228 = term195.
Proof. exact (MK_COMB (@lem2435348) (@lem2435349)). Qed.
Lemma lem2435352 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435353 : term195 = term54.
Proof. exact (@lem2435352 term43). Qed.
Lemma lem2435354 : term228 = term54.
Proof. exact (TRANS (@lem2435350) (@lem2435353)). Qed.
Lemma lem2435356 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435357 : term106 = term107.
Proof. exact (@lem2435356 term43 term43). Qed.
Lemma lem2435358 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435359 : term109 = term43.
Proof. exact (EQ_MP (@lem2435358) (@lem940073)). Qed.
Lemma lem2435360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435361 : term107 = term42.
Proof. exact (MK_COMB (@lem2435360) (@lem2435359)). Qed.
Lemma lem2435362 : term106 = term42.
Proof. exact (TRANS (@lem2435357) (@lem2435361)). Qed.
Lemma lem2435363 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2435364 : term229 = term195.
Proof. exact (MK_COMB (@lem2435363) (@lem2435362)). Qed.
Lemma lem2435366 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435367 : term195 = term54.
Proof. exact (@lem2435366 term43). Qed.
Lemma lem2435368 : term229 = term54.
Proof. exact (TRANS (@lem2435364) (@lem2435367)). Qed.
Lemma lem2435369 : term54 = term229.
Proof. exact (SYM (@lem2435368)). Qed.
Lemma lem2435370 : term228 = term229.
Proof. exact (TRANS (@lem2435354) (@lem2435369)). Qed.
Lemma lem2435371 : term218 = term170.
Proof. exact (@lem2435321 (@lem2435370)). Qed.
Lemma lem2435372 : term217 = term170.
Proof. exact (TRANS (@lem2435287) (@lem2435371)). Qed.
Lemma lem2435374 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2435375 : term170 = term54.
Proof. exact (@lem2435374 term54). Qed.
Lemma lem2435376 : term217 = term54.
Proof. exact (TRANS (@lem2435372) (@lem2435375)). Qed.
Lemma lem2435377 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2435378 : term230 = term227.
Proof. exact (MK_COMB (@lem2435377) (@lem2435376)). Qed.
Lemma lem2435379 (x' : int) : (real_of_int x') = (real_of_int x').
Proof. exact (eq_refl (real_of_int x')). Qed.
Lemma lem2435380 (x' : int) : (term236 x') = (term237 x').
Proof. exact (MK_COMB (@lem2435378) (@lem2435379 x')). Qed.
Lemma lem2435381 (x' : int) : (term683 x') = (term237 x').
Proof. exact (TRANS (@lem2435278 x') (@lem2435380 x')). Qed.
Lemma lem2435382 (x' : int) : (term237 x') = term54.
Proof. exact (@lem1982719 (real_of_int x')). Qed.
Lemma lem2435383 (x' : int) : (term683 x') = term54.
Proof. exact (TRANS (@lem2435381 x') (@lem2435382 x')). Qed.
Lemma lem2435384 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2435385 (x' : int) : (term684 x') = term148.
Proof. exact (MK_COMB (@lem2435384) (@lem2435383 x')). Qed.
Lemma lem2435386 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem2435387 (x' : int) : (term727 x') = term239.
Proof. exact (MK_COMB (@lem2435385 x') (@lem2435386)). Qed.
Lemma lem2435388 (x' : int) : (term726 x') = term239.
Proof. exact (TRANS (@lem2435277 x') (@lem2435387 x')). Qed.
Lemma lem2435389 : term239 = term97.
Proof. exact (@lem1982721 term97). Qed.
Lemma lem2435390 (x' : int) : (term726 x') = term97.
Proof. exact (TRANS (@lem2435388 x') (@lem2435389)). Qed.
Lemma lem2435391 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435392 (x' : int) : (term728 x') = term241.
Proof. exact (MK_COMB (@lem2435391) (@lem2435390 x')). Qed.
Lemma lem2435393 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435394 (x' : int) : (term725 x') = term242.
Proof. exact (MK_COMB (@lem2435392 x') (@lem2435393)). Qed.
Lemma lem2435395 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : term242.
Proof. exact (EQ_MP (@lem2435394 x') (@lem2435276 y x x' h1)). Qed.
Lemma lem2435397 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2435398 : term242 = term243.
Proof. exact (@lem2435397 term54 term97). Qed.
Lemma lem2435400 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2435401 : term97 = term98.
Proof. exact (@lem2435400 term43). Qed.
Lemma lem2435403 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435404 : term54 = term170.
Proof. exact (@lem2435403 (NUMERAL 0)). Qed.
Lemma lem2435405 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2435406 : term74 = term244.
Proof. exact (MK_COMB (@lem2435405) (@lem2435404)). Qed.
Lemma lem2435407 : term243 = term245.
Proof. exact (MK_COMB (@lem2435406) (@lem2435401)). Qed.
Lemma lem2435408 : term246.
Proof. exact (@lem1980026 term54 term42 term97 term42). Qed.
Lemma lem2435410 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435411 : term184 = term190.
Proof. exact (@lem2435410 (NUMERAL 0) term43). Qed.
Lemma lem2435412 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435413 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435414 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435413 h1) (fun h1 : term190 = True => @lem2435412)). Qed.
Lemma lem2435415 : term190 = True.
Proof. exact (EQ_MP (@lem2435414) (@lem2435412)). Qed.
Lemma lem2435416 : term184 = True.
Proof. exact (TRANS (@lem2435411) (@lem2435415)). Qed.
Lemma lem2435417 : True = term184.
Proof. exact (SYM (@lem2435416)). Qed.
Lemma lem2435418 : term184.
Proof. exact (EQ_MP (@lem2435417) (@lem0)). Qed.
Lemma lem2435419 : term247.
Proof. exact (@lem2435408 (@lem2435418)). Qed.
Lemma lem2435421 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435422 : term184 = term190.
Proof. exact (@lem2435421 (NUMERAL 0) term43). Qed.
Lemma lem2435423 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435424 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435425 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435424 h1) (fun h1 : term190 = True => @lem2435423)). Qed.
Lemma lem2435426 : term190 = True.
Proof. exact (EQ_MP (@lem2435425) (@lem2435423)). Qed.
Lemma lem2435427 : term184 = True.
Proof. exact (TRANS (@lem2435422) (@lem2435426)). Qed.
Lemma lem2435428 : True = term184.
Proof. exact (SYM (@lem2435427)). Qed.
Lemma lem2435429 : term184.
Proof. exact (EQ_MP (@lem2435428) (@lem0)). Qed.
Lemma lem2435430 : term245 = term248.
Proof. exact (@lem2435419 (@lem2435429)). Qed.
Lemma lem2435432 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2435433 : term101 = term112.
Proof. exact (@lem2435432 term43 term43). Qed.
Lemma lem2435434 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435435 : term109 = term43.
Proof. exact (EQ_MP (@lem2435434) (@lem940073)). Qed.
Lemma lem2435436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435437 : term107 = term42.
Proof. exact (MK_COMB (@lem2435436) (@lem2435435)). Qed.
Lemma lem2435438 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2435439 : term112 = term97.
Proof. exact (MK_COMB (@lem2435438) (@lem2435437)). Qed.
Lemma lem2435440 : term101 = term97.
Proof. exact (TRANS (@lem2435433) (@lem2435439)). Qed.
Lemma lem2435442 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435443 : term195 = term54.
Proof. exact (@lem2435442 term43). Qed.
Lemma lem2435444 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2435445 : term249 = term74.
Proof. exact (MK_COMB (@lem2435444) (@lem2435443)). Qed.
Lemma lem2435446 : term248 = term243.
Proof. exact (MK_COMB (@lem2435445) (@lem2435440)). Qed.
Lemma lem2435448 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2435449 : term243 = term252.
Proof. exact (@lem2435448 (NUMERAL 0) term43). Qed.
Lemma lem2435450 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435451 (h1 : term191 = (BIT1 0)) : (term43 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2435452 : (term191 = (BIT1 0)) = ((term43 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435451 h1) (fun h1 : (term43 = (NUMERAL 0)) = False => @lem2435450)). Qed.
Lemma lem2435453 : (term43 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2435452) (@lem2435450)). Qed.
Lemma lem2435454 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2435455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2435456 : term253 = (and True).
Proof. exact (MK_COMB (@lem2435455) (@lem2435454)). Qed.
Lemma lem2435457 : term252 = (True /\ False).
Proof. exact (MK_COMB (@lem2435456) (@lem2435453)). Qed.
Lemma lem2435459 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2435460 : term252 = False.
Proof. exact (TRANS (@lem2435457) (@lem2435459)). Qed.
Lemma lem2435461 : term243 = False.
Proof. exact (TRANS (@lem2435449) (@lem2435460)). Qed.
Lemma lem2435462 : term248 = False.
Proof. exact (TRANS (@lem2435446) (@lem2435461)). Qed.
Lemma lem2435463 : term245 = False.
Proof. exact (TRANS (@lem2435430) (@lem2435462)). Qed.
Lemma lem2435464 : term243 = False.
Proof. exact (TRANS (@lem2435407) (@lem2435463)). Qed.
Lemma lem2435465 : term242 = False.
Proof. exact (TRANS (@lem2435398) (@lem2435464)). Qed.
Lemma lem2435466 (y : int) (x : int) (x' : int) (h1 : term648 y x x') : False.
Proof. exact (EQ_MP (@lem2435465) (@lem2435395 y x x' h1)). Qed.
Lemma lem2435467 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term651 y x x'.
Proof. exact (h1). Qed.
Lemma lem2435468 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term649 x x'.
Proof. exact (proj2 (@lem2435467 y x x' h1)). Qed.
Lemma lem2435470 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term645 x'.
Proof. exact (proj2 (@lem2435468 y x x' h1)). Qed.
Lemma lem2435472 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term644 x'.
Proof. exact (proj2 (@lem2435470 y x x' h1)). Qed.
Lemma lem2435473 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term494 x'.
Proof. exact (proj1 (@lem2435470 y x x' h1)). Qed.
Lemma lem2435474 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term642 x'.
Proof. exact (proj2 (@lem2435472 y x x' h1)). Qed.
Lemma lem2435477 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2435478 : term183 = term184.
Proof. exact (@lem2435477 term54 term42). Qed.
Lemma lem2435480 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435481 : term42 = term94.
Proof. exact (@lem2435480 term43). Qed.
Lemma lem2435483 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435484 : term54 = term170.
Proof. exact (@lem2435483 (NUMERAL 0)). Qed.
Lemma lem2435485 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435486 : term185 = term186.
Proof. exact (MK_COMB (@lem2435485) (@lem2435484)). Qed.
Lemma lem2435487 : term184 = term187.
Proof. exact (MK_COMB (@lem2435486) (@lem2435481)). Qed.
Lemma lem2435488 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2435490 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435491 : term184 = term190.
Proof. exact (@lem2435490 (NUMERAL 0) term43). Qed.
Lemma lem2435492 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435493 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435494 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435493 h1) (fun h1 : term190 = True => @lem2435492)). Qed.
Lemma lem2435495 : term190 = True.
Proof. exact (EQ_MP (@lem2435494) (@lem2435492)). Qed.
Lemma lem2435496 : term184 = True.
Proof. exact (TRANS (@lem2435491) (@lem2435495)). Qed.
Lemma lem2435497 : True = term184.
Proof. exact (SYM (@lem2435496)). Qed.
Lemma lem2435498 : term184.
Proof. exact (EQ_MP (@lem2435497) (@lem0)). Qed.
Lemma lem2435499 : term192.
Proof. exact (@lem2435488 (@lem2435498)). Qed.
Lemma lem2435501 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435502 : term184 = term190.
Proof. exact (@lem2435501 (NUMERAL 0) term43). Qed.
Lemma lem2435503 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435504 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435505 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435504 h1) (fun h1 : term190 = True => @lem2435503)). Qed.
Lemma lem2435506 : term190 = True.
Proof. exact (EQ_MP (@lem2435505) (@lem2435503)). Qed.
Lemma lem2435507 : term184 = True.
Proof. exact (TRANS (@lem2435502) (@lem2435506)). Qed.
Lemma lem2435508 : True = term184.
Proof. exact (SYM (@lem2435507)). Qed.
Lemma lem2435509 : term184.
Proof. exact (EQ_MP (@lem2435508) (@lem0)). Qed.
Lemma lem2435510 : term187 = term193.
Proof. exact (@lem2435499 (@lem2435509)). Qed.
Lemma lem2435512 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435513 : term106 = term107.
Proof. exact (@lem2435512 term43 term43). Qed.
Lemma lem2435514 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435515 : term109 = term43.
Proof. exact (EQ_MP (@lem2435514) (@lem940073)). Qed.
Lemma lem2435516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435517 : term107 = term42.
Proof. exact (MK_COMB (@lem2435516) (@lem2435515)). Qed.
Lemma lem2435518 : term106 = term42.
Proof. exact (TRANS (@lem2435513) (@lem2435517)). Qed.
Lemma lem2435520 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435521 : term195 = term54.
Proof. exact (@lem2435520 term43). Qed.
Lemma lem2435522 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435523 : term196 = term185.
Proof. exact (MK_COMB (@lem2435522) (@lem2435521)). Qed.
Lemma lem2435524 : term193 = term184.
Proof. exact (MK_COMB (@lem2435523) (@lem2435518)). Qed.
Lemma lem2435526 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435527 : term184 = term190.
Proof. exact (@lem2435526 (NUMERAL 0) term43). Qed.
Lemma lem2435528 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435529 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435530 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435529 h1) (fun h1 : term190 = True => @lem2435528)). Qed.
Lemma lem2435531 : term190 = True.
Proof. exact (EQ_MP (@lem2435530) (@lem2435528)). Qed.
Lemma lem2435532 : term184 = True.
Proof. exact (TRANS (@lem2435527) (@lem2435531)). Qed.
Lemma lem2435533 : term193 = True.
Proof. exact (TRANS (@lem2435524) (@lem2435532)). Qed.
Lemma lem2435534 : term187 = True.
Proof. exact (TRANS (@lem2435510) (@lem2435533)). Qed.
Lemma lem2435535 : term184 = True.
Proof. exact (TRANS (@lem2435487) (@lem2435534)). Qed.
Lemma lem2435536 : term183 = True.
Proof. exact (TRANS (@lem2435478) (@lem2435535)). Qed.
Lemma lem2435537 : True = term183.
Proof. exact (SYM (@lem2435536)). Qed.
Lemma lem2435538 : term183.
Proof. exact (EQ_MP (@lem2435537) (@lem0)). Qed.
Lemma lem2435539 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term721 x'.
Proof. exact (conj (@lem2435538) (@lem2435474 y x x' h1)). Qed.
Lemma lem2435541 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2435542 (x' : int) : term722 x'.
Proof. exact (@lem2435541 term42 (real_of_int x')). Qed.
Lemma lem2435543 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term641 x'.
Proof. exact (@lem2435542 x' (@lem2435539 y x x' h1)). Qed.
Lemma lem2435544 (x' : int) : (term144 x') = (real_of_int x').
Proof. exact (@lem1982733 (real_of_int x')). Qed.
Lemma lem2435545 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435546 (x' : int) : (term639 x') = (term640 x').
Proof. exact (MK_COMB (@lem2435545) (@lem2435544 x')). Qed.
Lemma lem2435547 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435548 (x' : int) : (term641 x') = (term642 x').
Proof. exact (MK_COMB (@lem2435546 x') (@lem2435547)). Qed.
Lemma lem2435549 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term642 x'.
Proof. exact (EQ_MP (@lem2435548 x') (@lem2435543 y x x' h1)). Qed.
Lemma lem2435551 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2435552 : term183 = term184.
Proof. exact (@lem2435551 term54 term42). Qed.
Lemma lem2435554 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435555 : term42 = term94.
Proof. exact (@lem2435554 term43). Qed.
Lemma lem2435557 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435558 : term54 = term170.
Proof. exact (@lem2435557 (NUMERAL 0)). Qed.
Lemma lem2435559 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435560 : term185 = term186.
Proof. exact (MK_COMB (@lem2435559) (@lem2435558)). Qed.
Lemma lem2435561 : term184 = term187.
Proof. exact (MK_COMB (@lem2435560) (@lem2435555)). Qed.
Lemma lem2435562 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2435564 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435565 : term184 = term190.
Proof. exact (@lem2435564 (NUMERAL 0) term43). Qed.
Lemma lem2435566 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435567 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435568 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435567 h1) (fun h1 : term190 = True => @lem2435566)). Qed.
Lemma lem2435569 : term190 = True.
Proof. exact (EQ_MP (@lem2435568) (@lem2435566)). Qed.
Lemma lem2435570 : term184 = True.
Proof. exact (TRANS (@lem2435565) (@lem2435569)). Qed.
Lemma lem2435571 : True = term184.
Proof. exact (SYM (@lem2435570)). Qed.
Lemma lem2435572 : term184.
Proof. exact (EQ_MP (@lem2435571) (@lem0)). Qed.
Lemma lem2435573 : term192.
Proof. exact (@lem2435562 (@lem2435572)). Qed.
Lemma lem2435575 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435576 : term184 = term190.
Proof. exact (@lem2435575 (NUMERAL 0) term43). Qed.
Lemma lem2435577 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435578 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435579 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435578 h1) (fun h1 : term190 = True => @lem2435577)). Qed.
Lemma lem2435580 : term190 = True.
Proof. exact (EQ_MP (@lem2435579) (@lem2435577)). Qed.
Lemma lem2435581 : term184 = True.
Proof. exact (TRANS (@lem2435576) (@lem2435580)). Qed.
Lemma lem2435582 : True = term184.
Proof. exact (SYM (@lem2435581)). Qed.
Lemma lem2435583 : term184.
Proof. exact (EQ_MP (@lem2435582) (@lem0)). Qed.
Lemma lem2435584 : term187 = term193.
Proof. exact (@lem2435573 (@lem2435583)). Qed.
Lemma lem2435586 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435587 : term106 = term107.
Proof. exact (@lem2435586 term43 term43). Qed.
Lemma lem2435588 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435589 : term109 = term43.
Proof. exact (EQ_MP (@lem2435588) (@lem940073)). Qed.
Lemma lem2435590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435591 : term107 = term42.
Proof. exact (MK_COMB (@lem2435590) (@lem2435589)). Qed.
Lemma lem2435592 : term106 = term42.
Proof. exact (TRANS (@lem2435587) (@lem2435591)). Qed.
Lemma lem2435594 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435595 : term195 = term54.
Proof. exact (@lem2435594 term43). Qed.
Lemma lem2435596 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435597 : term196 = term185.
Proof. exact (MK_COMB (@lem2435596) (@lem2435595)). Qed.
Lemma lem2435598 : term193 = term184.
Proof. exact (MK_COMB (@lem2435597) (@lem2435592)). Qed.
Lemma lem2435600 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435601 : term184 = term190.
Proof. exact (@lem2435600 (NUMERAL 0) term43). Qed.
Lemma lem2435602 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435603 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435604 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435603 h1) (fun h1 : term190 = True => @lem2435602)). Qed.
Lemma lem2435605 : term190 = True.
Proof. exact (EQ_MP (@lem2435604) (@lem2435602)). Qed.
Lemma lem2435606 : term184 = True.
Proof. exact (TRANS (@lem2435601) (@lem2435605)). Qed.
Lemma lem2435607 : term193 = True.
Proof. exact (TRANS (@lem2435598) (@lem2435606)). Qed.
Lemma lem2435608 : term187 = True.
Proof. exact (TRANS (@lem2435584) (@lem2435607)). Qed.
Lemma lem2435609 : term184 = True.
Proof. exact (TRANS (@lem2435561) (@lem2435608)). Qed.
Lemma lem2435610 : term183 = True.
Proof. exact (TRANS (@lem2435552) (@lem2435609)). Qed.
Lemma lem2435611 : True = term183.
Proof. exact (SYM (@lem2435610)). Qed.
Lemma lem2435612 : term183.
Proof. exact (EQ_MP (@lem2435611) (@lem0)). Qed.
Lemma lem2435613 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term674 x'.
Proof. exact (conj (@lem2435612) (@lem2435473 y x x' h1)). Qed.
Lemma lem2435615 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2435616 (x' : int) : term675 x'.
Proof. exact (@lem2435615 term42 (term490 x')). Qed.
Lemma lem2435617 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term676 x'.
Proof. exact (@lem2435616 x' (@lem2435613 y x x' h1)). Qed.
Lemma lem2435618 (x' : int) : (term677 x') = (term490 x').
Proof. exact (@lem1982733 (term490 x')). Qed.
Lemma lem2435619 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435620 (x' : int) : (term678 x') = (term493 x').
Proof. exact (MK_COMB (@lem2435619) (@lem2435618 x')). Qed.
Lemma lem2435621 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435622 (x' : int) : (term676 x') = (term494 x').
Proof. exact (MK_COMB (@lem2435620 x') (@lem2435621)). Qed.
Lemma lem2435623 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term494 x'.
Proof. exact (EQ_MP (@lem2435622 x') (@lem2435617 y x x' h1)). Qed.
Lemma lem2435624 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term723 x'.
Proof. exact (conj (@lem2435623 y x x' h1) (@lem2435549 y x x' h1)). Qed.
Lemma lem2435626 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2435627 (x' : int) : term724 x'.
Proof. exact (@lem2435626 (term490 x') (real_of_int x')). Qed.
Lemma lem2435628 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term725 x'.
Proof. exact (@lem2435627 x' (@lem2435624 y x x' h1)). Qed.
Lemma lem2435629 (x' : int) : (term726 x') = (term727 x').
Proof. exact (@lem1982759 (term121 x') (real_of_int x') term97). Qed.
Lemma lem2435630 (x' : int) : (term683 x') = (term236 x').
Proof. exact (@lem1982713 term97 (real_of_int x')). Qed.
Lemma lem2435632 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435633 : term42 = term94.
Proof. exact (@lem2435632 term43). Qed.
Lemma lem2435635 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2435636 : term97 = term98.
Proof. exact (@lem2435635 term43). Qed.
Lemma lem2435637 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2435638 : term215 = term216.
Proof. exact (MK_COMB (@lem2435637) (@lem2435636)). Qed.
Lemma lem2435639 : term217 = term218.
Proof. exact (MK_COMB (@lem2435638) (@lem2435633)). Qed.
Lemma lem2435640 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2435642 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435643 : term184 = term190.
Proof. exact (@lem2435642 (NUMERAL 0) term43). Qed.
Lemma lem2435644 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435645 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435646 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435645 h1) (fun h1 : term190 = True => @lem2435644)). Qed.
Lemma lem2435647 : term190 = True.
Proof. exact (EQ_MP (@lem2435646) (@lem2435644)). Qed.
Lemma lem2435648 : term184 = True.
Proof. exact (TRANS (@lem2435643) (@lem2435647)). Qed.
Lemma lem2435649 : True = term184.
Proof. exact (SYM (@lem2435648)). Qed.
Lemma lem2435650 : term184.
Proof. exact (EQ_MP (@lem2435649) (@lem0)). Qed.
Lemma lem2435651 : term220.
Proof. exact (@lem2435640 (@lem2435650)). Qed.
Lemma lem2435653 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435654 : term184 = term190.
Proof. exact (@lem2435653 (NUMERAL 0) term43). Qed.
Lemma lem2435655 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435656 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435657 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435656 h1) (fun h1 : term190 = True => @lem2435655)). Qed.
Lemma lem2435658 : term190 = True.
Proof. exact (EQ_MP (@lem2435657) (@lem2435655)). Qed.
Lemma lem2435659 : term184 = True.
Proof. exact (TRANS (@lem2435654) (@lem2435658)). Qed.
Lemma lem2435660 : True = term184.
Proof. exact (SYM (@lem2435659)). Qed.
Lemma lem2435661 : term184.
Proof. exact (EQ_MP (@lem2435660) (@lem0)). Qed.
Lemma lem2435662 : term221.
Proof. exact (@lem2435651 (@lem2435661)). Qed.
Lemma lem2435664 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435665 : term184 = term190.
Proof. exact (@lem2435664 (NUMERAL 0) term43). Qed.
Lemma lem2435666 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435667 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435668 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435667 h1) (fun h1 : term190 = True => @lem2435666)). Qed.
Lemma lem2435669 : term190 = True.
Proof. exact (EQ_MP (@lem2435668) (@lem2435666)). Qed.
Lemma lem2435670 : term184 = True.
Proof. exact (TRANS (@lem2435665) (@lem2435669)). Qed.
Lemma lem2435671 : True = term184.
Proof. exact (SYM (@lem2435670)). Qed.
Lemma lem2435672 : term184.
Proof. exact (EQ_MP (@lem2435671) (@lem0)). Qed.
Lemma lem2435673 : term222.
Proof. exact (@lem2435662 (@lem2435672)). Qed.
Lemma lem2435675 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435676 : term106 = term107.
Proof. exact (@lem2435675 term43 term43). Qed.
Lemma lem2435677 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435678 : term109 = term43.
Proof. exact (EQ_MP (@lem2435677) (@lem940073)). Qed.
Lemma lem2435679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435680 : term107 = term42.
Proof. exact (MK_COMB (@lem2435679) (@lem2435678)). Qed.
Lemma lem2435681 : term106 = term42.
Proof. exact (TRANS (@lem2435676) (@lem2435680)). Qed.
Lemma lem2435683 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2435684 : term101 = term112.
Proof. exact (@lem2435683 term43 term43). Qed.
Lemma lem2435685 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435686 : term109 = term43.
Proof. exact (EQ_MP (@lem2435685) (@lem940073)). Qed.
Lemma lem2435687 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435688 : term107 = term42.
Proof. exact (MK_COMB (@lem2435687) (@lem2435686)). Qed.
Lemma lem2435689 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2435690 : term112 = term97.
Proof. exact (MK_COMB (@lem2435689) (@lem2435688)). Qed.
Lemma lem2435691 : term101 = term97.
Proof. exact (TRANS (@lem2435684) (@lem2435690)). Qed.
Lemma lem2435692 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2435693 : term223 = term215.
Proof. exact (MK_COMB (@lem2435692) (@lem2435691)). Qed.
Lemma lem2435694 : term224 = term217.
Proof. exact (MK_COMB (@lem2435693) (@lem2435681)). Qed.
Lemma lem2435696 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2435697 : term217 = term54.
Proof. exact (@lem2435696 term43). Qed.
Lemma lem2435698 : term224 = term54.
Proof. exact (TRANS (@lem2435694) (@lem2435697)). Qed.
Lemma lem2435699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2435700 : term226 = term227.
Proof. exact (MK_COMB (@lem2435699) (@lem2435698)). Qed.
Lemma lem2435701 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2435702 : term228 = term195.
Proof. exact (MK_COMB (@lem2435700) (@lem2435701)). Qed.
Lemma lem2435704 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435705 : term195 = term54.
Proof. exact (@lem2435704 term43). Qed.
Lemma lem2435706 : term228 = term54.
Proof. exact (TRANS (@lem2435702) (@lem2435705)). Qed.
Lemma lem2435708 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435709 : term106 = term107.
Proof. exact (@lem2435708 term43 term43). Qed.
Lemma lem2435710 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435711 : term109 = term43.
Proof. exact (EQ_MP (@lem2435710) (@lem940073)). Qed.
Lemma lem2435712 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435713 : term107 = term42.
Proof. exact (MK_COMB (@lem2435712) (@lem2435711)). Qed.
Lemma lem2435714 : term106 = term42.
Proof. exact (TRANS (@lem2435709) (@lem2435713)). Qed.
Lemma lem2435715 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2435716 : term229 = term195.
Proof. exact (MK_COMB (@lem2435715) (@lem2435714)). Qed.
Lemma lem2435718 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435719 : term195 = term54.
Proof. exact (@lem2435718 term43). Qed.
Lemma lem2435720 : term229 = term54.
Proof. exact (TRANS (@lem2435716) (@lem2435719)). Qed.
Lemma lem2435721 : term54 = term229.
Proof. exact (SYM (@lem2435720)). Qed.
Lemma lem2435722 : term228 = term229.
Proof. exact (TRANS (@lem2435706) (@lem2435721)). Qed.
Lemma lem2435723 : term218 = term170.
Proof. exact (@lem2435673 (@lem2435722)). Qed.
Lemma lem2435724 : term217 = term170.
Proof. exact (TRANS (@lem2435639) (@lem2435723)). Qed.
Lemma lem2435726 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2435727 : term170 = term54.
Proof. exact (@lem2435726 term54). Qed.
Lemma lem2435728 : term217 = term54.
Proof. exact (TRANS (@lem2435724) (@lem2435727)). Qed.
Lemma lem2435729 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2435730 : term230 = term227.
Proof. exact (MK_COMB (@lem2435729) (@lem2435728)). Qed.
Lemma lem2435731 (x' : int) : (real_of_int x') = (real_of_int x').
Proof. exact (eq_refl (real_of_int x')). Qed.
Lemma lem2435732 (x' : int) : (term236 x') = (term237 x').
Proof. exact (MK_COMB (@lem2435730) (@lem2435731 x')). Qed.
Lemma lem2435733 (x' : int) : (term683 x') = (term237 x').
Proof. exact (TRANS (@lem2435630 x') (@lem2435732 x')). Qed.
Lemma lem2435734 (x' : int) : (term237 x') = term54.
Proof. exact (@lem1982719 (real_of_int x')). Qed.
Lemma lem2435735 (x' : int) : (term683 x') = term54.
Proof. exact (TRANS (@lem2435733 x') (@lem2435734 x')). Qed.
Lemma lem2435736 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2435737 (x' : int) : (term684 x') = term148.
Proof. exact (MK_COMB (@lem2435736) (@lem2435735 x')). Qed.
Lemma lem2435738 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem2435739 (x' : int) : (term727 x') = term239.
Proof. exact (MK_COMB (@lem2435737 x') (@lem2435738)). Qed.
Lemma lem2435740 (x' : int) : (term726 x') = term239.
Proof. exact (TRANS (@lem2435629 x') (@lem2435739 x')). Qed.
Lemma lem2435741 : term239 = term97.
Proof. exact (@lem1982721 term97). Qed.
Lemma lem2435742 (x' : int) : (term726 x') = term97.
Proof. exact (TRANS (@lem2435740 x') (@lem2435741)). Qed.
Lemma lem2435743 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435744 (x' : int) : (term728 x') = term241.
Proof. exact (MK_COMB (@lem2435743) (@lem2435742 x')). Qed.
Lemma lem2435745 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435746 (x' : int) : (term725 x') = term242.
Proof. exact (MK_COMB (@lem2435744 x') (@lem2435745)). Qed.
Lemma lem2435747 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : term242.
Proof. exact (EQ_MP (@lem2435746 x') (@lem2435628 y x x' h1)). Qed.
Lemma lem2435749 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2435750 : term242 = term243.
Proof. exact (@lem2435749 term54 term97). Qed.
Lemma lem2435752 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2435753 : term97 = term98.
Proof. exact (@lem2435752 term43). Qed.
Lemma lem2435755 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435756 : term54 = term170.
Proof. exact (@lem2435755 (NUMERAL 0)). Qed.
Lemma lem2435757 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2435758 : term74 = term244.
Proof. exact (MK_COMB (@lem2435757) (@lem2435756)). Qed.
Lemma lem2435759 : term243 = term245.
Proof. exact (MK_COMB (@lem2435758) (@lem2435753)). Qed.
Lemma lem2435760 : term246.
Proof. exact (@lem1980026 term54 term42 term97 term42). Qed.
Lemma lem2435762 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435763 : term184 = term190.
Proof. exact (@lem2435762 (NUMERAL 0) term43). Qed.
Lemma lem2435764 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435765 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435766 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435765 h1) (fun h1 : term190 = True => @lem2435764)). Qed.
Lemma lem2435767 : term190 = True.
Proof. exact (EQ_MP (@lem2435766) (@lem2435764)). Qed.
Lemma lem2435768 : term184 = True.
Proof. exact (TRANS (@lem2435763) (@lem2435767)). Qed.
Lemma lem2435769 : True = term184.
Proof. exact (SYM (@lem2435768)). Qed.
Lemma lem2435770 : term184.
Proof. exact (EQ_MP (@lem2435769) (@lem0)). Qed.
Lemma lem2435771 : term247.
Proof. exact (@lem2435760 (@lem2435770)). Qed.
Lemma lem2435773 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435774 : term184 = term190.
Proof. exact (@lem2435773 (NUMERAL 0) term43). Qed.
Lemma lem2435775 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435776 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435777 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435776 h1) (fun h1 : term190 = True => @lem2435775)). Qed.
Lemma lem2435778 : term190 = True.
Proof. exact (EQ_MP (@lem2435777) (@lem2435775)). Qed.
Lemma lem2435779 : term184 = True.
Proof. exact (TRANS (@lem2435774) (@lem2435778)). Qed.
Lemma lem2435780 : True = term184.
Proof. exact (SYM (@lem2435779)). Qed.
Lemma lem2435781 : term184.
Proof. exact (EQ_MP (@lem2435780) (@lem0)). Qed.
Lemma lem2435782 : term245 = term248.
Proof. exact (@lem2435771 (@lem2435781)). Qed.
Lemma lem2435784 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2435785 : term101 = term112.
Proof. exact (@lem2435784 term43 term43). Qed.
Lemma lem2435786 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435787 : term109 = term43.
Proof. exact (EQ_MP (@lem2435786) (@lem940073)). Qed.
Lemma lem2435788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435789 : term107 = term42.
Proof. exact (MK_COMB (@lem2435788) (@lem2435787)). Qed.
Lemma lem2435790 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2435791 : term112 = term97.
Proof. exact (MK_COMB (@lem2435790) (@lem2435789)). Qed.
Lemma lem2435792 : term101 = term97.
Proof. exact (TRANS (@lem2435785) (@lem2435791)). Qed.
Lemma lem2435794 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435795 : term195 = term54.
Proof. exact (@lem2435794 term43). Qed.
Lemma lem2435796 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2435797 : term249 = term74.
Proof. exact (MK_COMB (@lem2435796) (@lem2435795)). Qed.
Lemma lem2435798 : term248 = term243.
Proof. exact (MK_COMB (@lem2435797) (@lem2435792)). Qed.
Lemma lem2435800 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2435801 : term243 = term252.
Proof. exact (@lem2435800 (NUMERAL 0) term43). Qed.
Lemma lem2435802 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435803 (h1 : term191 = (BIT1 0)) : (term43 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2435804 : (term191 = (BIT1 0)) = ((term43 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435803 h1) (fun h1 : (term43 = (NUMERAL 0)) = False => @lem2435802)). Qed.
Lemma lem2435805 : (term43 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2435804) (@lem2435802)). Qed.
Lemma lem2435806 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2435807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2435808 : term253 = (and True).
Proof. exact (MK_COMB (@lem2435807) (@lem2435806)). Qed.
Lemma lem2435809 : term252 = (True /\ False).
Proof. exact (MK_COMB (@lem2435808) (@lem2435805)). Qed.
Lemma lem2435811 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2435812 : term252 = False.
Proof. exact (TRANS (@lem2435809) (@lem2435811)). Qed.
Lemma lem2435813 : term243 = False.
Proof. exact (TRANS (@lem2435801) (@lem2435812)). Qed.
Lemma lem2435814 : term248 = False.
Proof. exact (TRANS (@lem2435798) (@lem2435813)). Qed.
Lemma lem2435815 : term245 = False.
Proof. exact (TRANS (@lem2435782) (@lem2435814)). Qed.
Lemma lem2435816 : term243 = False.
Proof. exact (TRANS (@lem2435759) (@lem2435815)). Qed.
Lemma lem2435817 : term242 = False.
Proof. exact (TRANS (@lem2435750) (@lem2435816)). Qed.
Lemma lem2435818 (y : int) (x : int) (x' : int) (h1 : term651 y x x') : False.
Proof. exact (EQ_MP (@lem2435817) (@lem2435747 y x x' h1)). Qed.
Lemma lem2435819 (y : int) (x : int) (x' : int) (h1 : term654 y x x') : False.
Proof. exact (or_elim (@lem2435114 y x x' h1) (fun h0 : term648 y x x' => @lem2435466 y x x' h0) (fun h0 : term651 y x x' => @lem2435818 y x x' h0)). Qed.
Lemma lem2435820 (y : int) (x : int) (x' : int) (h1 : term664 y x x') : term664 y x x'.
Proof. exact (h1). Qed.
Lemma lem2435821 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term658 y x x'.
Proof. exact (h1). Qed.
Lemma lem2435822 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term656 x x'.
Proof. exact (proj2 (@lem2435821 y x x' h1)). Qed.
Lemma lem2435824 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term655 x'.
Proof. exact (proj2 (@lem2435822 y x x' h1)). Qed.
Lemma lem2435826 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term644 x'.
Proof. exact (proj2 (@lem2435824 y x x' h1)). Qed.
Lemma lem2435827 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term499 x'.
Proof. exact (proj1 (@lem2435824 y x x' h1)). Qed.
Lemma lem2435829 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term729 x'.
Proof. exact (proj1 (@lem2435826 y x x' h1)). Qed.
Lemma lem2435831 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2435832 : term183 = term184.
Proof. exact (@lem2435831 term54 term42). Qed.
Lemma lem2435834 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435835 : term42 = term94.
Proof. exact (@lem2435834 term43). Qed.
Lemma lem2435837 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435838 : term54 = term170.
Proof. exact (@lem2435837 (NUMERAL 0)). Qed.
Lemma lem2435839 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435840 : term185 = term186.
Proof. exact (MK_COMB (@lem2435839) (@lem2435838)). Qed.
Lemma lem2435841 : term184 = term187.
Proof. exact (MK_COMB (@lem2435840) (@lem2435835)). Qed.
Lemma lem2435842 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2435844 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435845 : term184 = term190.
Proof. exact (@lem2435844 (NUMERAL 0) term43). Qed.
Lemma lem2435846 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435847 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435848 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435847 h1) (fun h1 : term190 = True => @lem2435846)). Qed.
Lemma lem2435849 : term190 = True.
Proof. exact (EQ_MP (@lem2435848) (@lem2435846)). Qed.
Lemma lem2435850 : term184 = True.
Proof. exact (TRANS (@lem2435845) (@lem2435849)). Qed.
Lemma lem2435851 : True = term184.
Proof. exact (SYM (@lem2435850)). Qed.
Lemma lem2435852 : term184.
Proof. exact (EQ_MP (@lem2435851) (@lem0)). Qed.
Lemma lem2435853 : term192.
Proof. exact (@lem2435842 (@lem2435852)). Qed.
Lemma lem2435855 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435856 : term184 = term190.
Proof. exact (@lem2435855 (NUMERAL 0) term43). Qed.
Lemma lem2435857 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435858 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435859 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435858 h1) (fun h1 : term190 = True => @lem2435857)). Qed.
Lemma lem2435860 : term190 = True.
Proof. exact (EQ_MP (@lem2435859) (@lem2435857)). Qed.
Lemma lem2435861 : term184 = True.
Proof. exact (TRANS (@lem2435856) (@lem2435860)). Qed.
Lemma lem2435862 : True = term184.
Proof. exact (SYM (@lem2435861)). Qed.
Lemma lem2435863 : term184.
Proof. exact (EQ_MP (@lem2435862) (@lem0)). Qed.
Lemma lem2435864 : term187 = term193.
Proof. exact (@lem2435853 (@lem2435863)). Qed.
Lemma lem2435866 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435867 : term106 = term107.
Proof. exact (@lem2435866 term43 term43). Qed.
Lemma lem2435868 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435869 : term109 = term43.
Proof. exact (EQ_MP (@lem2435868) (@lem940073)). Qed.
Lemma lem2435870 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435871 : term107 = term42.
Proof. exact (MK_COMB (@lem2435870) (@lem2435869)). Qed.
Lemma lem2435872 : term106 = term42.
Proof. exact (TRANS (@lem2435867) (@lem2435871)). Qed.
Lemma lem2435874 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435875 : term195 = term54.
Proof. exact (@lem2435874 term43). Qed.
Lemma lem2435876 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435877 : term196 = term185.
Proof. exact (MK_COMB (@lem2435876) (@lem2435875)). Qed.
Lemma lem2435878 : term193 = term184.
Proof. exact (MK_COMB (@lem2435877) (@lem2435872)). Qed.
Lemma lem2435880 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435881 : term184 = term190.
Proof. exact (@lem2435880 (NUMERAL 0) term43). Qed.
Lemma lem2435882 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435883 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435884 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435883 h1) (fun h1 : term190 = True => @lem2435882)). Qed.
Lemma lem2435885 : term190 = True.
Proof. exact (EQ_MP (@lem2435884) (@lem2435882)). Qed.
Lemma lem2435886 : term184 = True.
Proof. exact (TRANS (@lem2435881) (@lem2435885)). Qed.
Lemma lem2435887 : term193 = True.
Proof. exact (TRANS (@lem2435878) (@lem2435886)). Qed.
Lemma lem2435888 : term187 = True.
Proof. exact (TRANS (@lem2435864) (@lem2435887)). Qed.
Lemma lem2435889 : term184 = True.
Proof. exact (TRANS (@lem2435841) (@lem2435888)). Qed.
Lemma lem2435890 : term183 = True.
Proof. exact (TRANS (@lem2435832) (@lem2435889)). Qed.
Lemma lem2435891 : True = term183.
Proof. exact (SYM (@lem2435890)). Qed.
Lemma lem2435892 : term183.
Proof. exact (EQ_MP (@lem2435891) (@lem0)). Qed.
Lemma lem2435893 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term669 x'.
Proof. exact (conj (@lem2435892) (@lem2435827 y x x' h1)). Qed.
Lemma lem2435895 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2435896 (x' : int) : term670 x'.
Proof. exact (@lem2435895 term42 (term117 x')). Qed.
Lemma lem2435897 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term671 x'.
Proof. exact (@lem2435896 x' (@lem2435893 y x x' h1)). Qed.
Lemma lem2435898 (x' : int) : (term672 x') = (term117 x').
Proof. exact (@lem1982733 (term117 x')). Qed.
Lemma lem2435899 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435900 (x' : int) : (term673 x') = (term498 x').
Proof. exact (MK_COMB (@lem2435899) (@lem2435898 x')). Qed.
Lemma lem2435901 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435902 (x' : int) : (term671 x') = (term499 x').
Proof. exact (MK_COMB (@lem2435900 x') (@lem2435901)). Qed.
Lemma lem2435903 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term499 x'.
Proof. exact (EQ_MP (@lem2435902 x') (@lem2435897 y x x' h1)). Qed.
Lemma lem2435905 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2435906 : term183 = term184.
Proof. exact (@lem2435905 term54 term42). Qed.
Lemma lem2435908 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435909 : term42 = term94.
Proof. exact (@lem2435908 term43). Qed.
Lemma lem2435911 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435912 : term54 = term170.
Proof. exact (@lem2435911 (NUMERAL 0)). Qed.
Lemma lem2435913 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435914 : term185 = term186.
Proof. exact (MK_COMB (@lem2435913) (@lem2435912)). Qed.
Lemma lem2435915 : term184 = term187.
Proof. exact (MK_COMB (@lem2435914) (@lem2435909)). Qed.
Lemma lem2435916 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2435918 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435919 : term184 = term190.
Proof. exact (@lem2435918 (NUMERAL 0) term43). Qed.
Lemma lem2435920 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435921 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435922 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435921 h1) (fun h1 : term190 = True => @lem2435920)). Qed.
Lemma lem2435923 : term190 = True.
Proof. exact (EQ_MP (@lem2435922) (@lem2435920)). Qed.
Lemma lem2435924 : term184 = True.
Proof. exact (TRANS (@lem2435919) (@lem2435923)). Qed.
Lemma lem2435925 : True = term184.
Proof. exact (SYM (@lem2435924)). Qed.
Lemma lem2435926 : term184.
Proof. exact (EQ_MP (@lem2435925) (@lem0)). Qed.
Lemma lem2435927 : term192.
Proof. exact (@lem2435916 (@lem2435926)). Qed.
Lemma lem2435929 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435930 : term184 = term190.
Proof. exact (@lem2435929 (NUMERAL 0) term43). Qed.
Lemma lem2435931 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435932 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435933 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435932 h1) (fun h1 : term190 = True => @lem2435931)). Qed.
Lemma lem2435934 : term190 = True.
Proof. exact (EQ_MP (@lem2435933) (@lem2435931)). Qed.
Lemma lem2435935 : term184 = True.
Proof. exact (TRANS (@lem2435930) (@lem2435934)). Qed.
Lemma lem2435936 : True = term184.
Proof. exact (SYM (@lem2435935)). Qed.
Lemma lem2435937 : term184.
Proof. exact (EQ_MP (@lem2435936) (@lem0)). Qed.
Lemma lem2435938 : term187 = term193.
Proof. exact (@lem2435927 (@lem2435937)). Qed.
Lemma lem2435940 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2435941 : term106 = term107.
Proof. exact (@lem2435940 term43 term43). Qed.
Lemma lem2435942 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2435943 : term109 = term43.
Proof. exact (EQ_MP (@lem2435942) (@lem940073)). Qed.
Lemma lem2435944 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2435945 : term107 = term42.
Proof. exact (MK_COMB (@lem2435944) (@lem2435943)). Qed.
Lemma lem2435946 : term106 = term42.
Proof. exact (TRANS (@lem2435941) (@lem2435945)). Qed.
Lemma lem2435948 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2435949 : term195 = term54.
Proof. exact (@lem2435948 term43). Qed.
Lemma lem2435950 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2435951 : term196 = term185.
Proof. exact (MK_COMB (@lem2435950) (@lem2435949)). Qed.
Lemma lem2435952 : term193 = term184.
Proof. exact (MK_COMB (@lem2435951) (@lem2435946)). Qed.
Lemma lem2435954 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435955 : term184 = term190.
Proof. exact (@lem2435954 (NUMERAL 0) term43). Qed.
Lemma lem2435956 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435957 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2435958 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435957 h1) (fun h1 : term190 = True => @lem2435956)). Qed.
Lemma lem2435959 : term190 = True.
Proof. exact (EQ_MP (@lem2435958) (@lem2435956)). Qed.
Lemma lem2435960 : term184 = True.
Proof. exact (TRANS (@lem2435955) (@lem2435959)). Qed.
Lemma lem2435961 : term193 = True.
Proof. exact (TRANS (@lem2435952) (@lem2435960)). Qed.
Lemma lem2435962 : term187 = True.
Proof. exact (TRANS (@lem2435938) (@lem2435961)). Qed.
Lemma lem2435963 : term184 = True.
Proof. exact (TRANS (@lem2435915) (@lem2435962)). Qed.
Lemma lem2435964 : term183 = True.
Proof. exact (TRANS (@lem2435906) (@lem2435963)). Qed.
Lemma lem2435965 : True = term183.
Proof. exact (SYM (@lem2435964)). Qed.
Lemma lem2435966 : term183.
Proof. exact (EQ_MP (@lem2435965) (@lem0)). Qed.
Lemma lem2435967 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term730 x'.
Proof. exact (conj (@lem2435966) (@lem2435829 y x x' h1)). Qed.
Lemma lem2435969 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2435970 (x' : int) : term731 x'.
Proof. exact (@lem2435969 term42 (term121 x')). Qed.
Lemma lem2435971 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term732 x'.
Proof. exact (@lem2435970 x' (@lem2435967 y x x' h1)). Qed.
Lemma lem2435972 (x' : int) : (term733 x') = (term121 x').
Proof. exact (@lem1982733 (term121 x')). Qed.
Lemma lem2435973 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2435974 (x' : int) : (term734 x') = (term735 x').
Proof. exact (MK_COMB (@lem2435973) (@lem2435972 x')). Qed.
Lemma lem2435975 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2435976 (x' : int) : (term732 x') = (term729 x').
Proof. exact (MK_COMB (@lem2435974 x') (@lem2435975)). Qed.
Lemma lem2435977 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term729 x'.
Proof. exact (EQ_MP (@lem2435976 x') (@lem2435971 y x x' h1)). Qed.
Lemma lem2435978 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term736 x'.
Proof. exact (conj (@lem2435977 y x x' h1) (@lem2435903 y x x' h1)). Qed.
Lemma lem2435980 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2435981 (x' : int) : term737 x'.
Proof. exact (@lem2435980 (term121 x') (term117 x')). Qed.
Lemma lem2435982 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term738 x'.
Proof. exact (@lem2435981 x' (@lem2435978 y x x' h1)). Qed.
Lemma lem2435983 (x' : int) : (term739 x') = (term727 x').
Proof. exact (@lem1982763 (term121 x') (real_of_int x') term97). Qed.
Lemma lem2435984 (x' : int) : (term683 x') = (term236 x').
Proof. exact (@lem1982713 term97 (real_of_int x')). Qed.
Lemma lem2435986 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2435987 : term42 = term94.
Proof. exact (@lem2435986 term43). Qed.
Lemma lem2435989 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2435990 : term97 = term98.
Proof. exact (@lem2435989 term43). Qed.
Lemma lem2435991 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2435992 : term215 = term216.
Proof. exact (MK_COMB (@lem2435991) (@lem2435990)). Qed.
Lemma lem2435993 : term217 = term218.
Proof. exact (MK_COMB (@lem2435992) (@lem2435987)). Qed.
Lemma lem2435994 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2435996 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2435997 : term184 = term190.
Proof. exact (@lem2435996 (NUMERAL 0) term43). Qed.
Lemma lem2435998 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2435999 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436000 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2435999 h1) (fun h1 : term190 = True => @lem2435998)). Qed.
Lemma lem2436001 : term190 = True.
Proof. exact (EQ_MP (@lem2436000) (@lem2435998)). Qed.
Lemma lem2436002 : term184 = True.
Proof. exact (TRANS (@lem2435997) (@lem2436001)). Qed.
Lemma lem2436003 : True = term184.
Proof. exact (SYM (@lem2436002)). Qed.
Lemma lem2436004 : term184.
Proof. exact (EQ_MP (@lem2436003) (@lem0)). Qed.
Lemma lem2436005 : term220.
Proof. exact (@lem2435994 (@lem2436004)). Qed.
Lemma lem2436007 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436008 : term184 = term190.
Proof. exact (@lem2436007 (NUMERAL 0) term43). Qed.
Lemma lem2436009 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436010 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436011 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436010 h1) (fun h1 : term190 = True => @lem2436009)). Qed.
Lemma lem2436012 : term190 = True.
Proof. exact (EQ_MP (@lem2436011) (@lem2436009)). Qed.
Lemma lem2436013 : term184 = True.
Proof. exact (TRANS (@lem2436008) (@lem2436012)). Qed.
Lemma lem2436014 : True = term184.
Proof. exact (SYM (@lem2436013)). Qed.
Lemma lem2436015 : term184.
Proof. exact (EQ_MP (@lem2436014) (@lem0)). Qed.
Lemma lem2436016 : term221.
Proof. exact (@lem2436005 (@lem2436015)). Qed.
Lemma lem2436018 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436019 : term184 = term190.
Proof. exact (@lem2436018 (NUMERAL 0) term43). Qed.
Lemma lem2436020 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436021 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436022 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436021 h1) (fun h1 : term190 = True => @lem2436020)). Qed.
Lemma lem2436023 : term190 = True.
Proof. exact (EQ_MP (@lem2436022) (@lem2436020)). Qed.
Lemma lem2436024 : term184 = True.
Proof. exact (TRANS (@lem2436019) (@lem2436023)). Qed.
Lemma lem2436025 : True = term184.
Proof. exact (SYM (@lem2436024)). Qed.
Lemma lem2436026 : term184.
Proof. exact (EQ_MP (@lem2436025) (@lem0)). Qed.
Lemma lem2436027 : term222.
Proof. exact (@lem2436016 (@lem2436026)). Qed.
Lemma lem2436029 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2436030 : term106 = term107.
Proof. exact (@lem2436029 term43 term43). Qed.
Lemma lem2436031 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436032 : term109 = term43.
Proof. exact (EQ_MP (@lem2436031) (@lem940073)). Qed.
Lemma lem2436033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436034 : term107 = term42.
Proof. exact (MK_COMB (@lem2436033) (@lem2436032)). Qed.
Lemma lem2436035 : term106 = term42.
Proof. exact (TRANS (@lem2436030) (@lem2436034)). Qed.
Lemma lem2436037 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2436038 : term101 = term112.
Proof. exact (@lem2436037 term43 term43). Qed.
Lemma lem2436039 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436040 : term109 = term43.
Proof. exact (EQ_MP (@lem2436039) (@lem940073)). Qed.
Lemma lem2436041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436042 : term107 = term42.
Proof. exact (MK_COMB (@lem2436041) (@lem2436040)). Qed.
Lemma lem2436043 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2436044 : term112 = term97.
Proof. exact (MK_COMB (@lem2436043) (@lem2436042)). Qed.
Lemma lem2436045 : term101 = term97.
Proof. exact (TRANS (@lem2436038) (@lem2436044)). Qed.
Lemma lem2436046 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2436047 : term223 = term215.
Proof. exact (MK_COMB (@lem2436046) (@lem2436045)). Qed.
Lemma lem2436048 : term224 = term217.
Proof. exact (MK_COMB (@lem2436047) (@lem2436035)). Qed.
Lemma lem2436050 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2436051 : term217 = term54.
Proof. exact (@lem2436050 term43). Qed.
Lemma lem2436052 : term224 = term54.
Proof. exact (TRANS (@lem2436048) (@lem2436051)). Qed.
Lemma lem2436053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2436054 : term226 = term227.
Proof. exact (MK_COMB (@lem2436053) (@lem2436052)). Qed.
Lemma lem2436055 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2436056 : term228 = term195.
Proof. exact (MK_COMB (@lem2436054) (@lem2436055)). Qed.
Lemma lem2436058 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2436059 : term195 = term54.
Proof. exact (@lem2436058 term43). Qed.
Lemma lem2436060 : term228 = term54.
Proof. exact (TRANS (@lem2436056) (@lem2436059)). Qed.
Lemma lem2436062 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2436063 : term106 = term107.
Proof. exact (@lem2436062 term43 term43). Qed.
Lemma lem2436064 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436065 : term109 = term43.
Proof. exact (EQ_MP (@lem2436064) (@lem940073)). Qed.
Lemma lem2436066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436067 : term107 = term42.
Proof. exact (MK_COMB (@lem2436066) (@lem2436065)). Qed.
Lemma lem2436068 : term106 = term42.
Proof. exact (TRANS (@lem2436063) (@lem2436067)). Qed.
Lemma lem2436069 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2436070 : term229 = term195.
Proof. exact (MK_COMB (@lem2436069) (@lem2436068)). Qed.
Lemma lem2436072 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2436073 : term195 = term54.
Proof. exact (@lem2436072 term43). Qed.
Lemma lem2436074 : term229 = term54.
Proof. exact (TRANS (@lem2436070) (@lem2436073)). Qed.
Lemma lem2436075 : term54 = term229.
Proof. exact (SYM (@lem2436074)). Qed.
Lemma lem2436076 : term228 = term229.
Proof. exact (TRANS (@lem2436060) (@lem2436075)). Qed.
Lemma lem2436077 : term218 = term170.
Proof. exact (@lem2436027 (@lem2436076)). Qed.
Lemma lem2436078 : term217 = term170.
Proof. exact (TRANS (@lem2435993) (@lem2436077)). Qed.
Lemma lem2436080 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2436081 : term170 = term54.
Proof. exact (@lem2436080 term54). Qed.
Lemma lem2436082 : term217 = term54.
Proof. exact (TRANS (@lem2436078) (@lem2436081)). Qed.
Lemma lem2436083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2436084 : term230 = term227.
Proof. exact (MK_COMB (@lem2436083) (@lem2436082)). Qed.
Lemma lem2436085 (x' : int) : (real_of_int x') = (real_of_int x').
Proof. exact (eq_refl (real_of_int x')). Qed.
Lemma lem2436086 (x' : int) : (term236 x') = (term237 x').
Proof. exact (MK_COMB (@lem2436084) (@lem2436085 x')). Qed.
Lemma lem2436087 (x' : int) : (term683 x') = (term237 x').
Proof. exact (TRANS (@lem2435984 x') (@lem2436086 x')). Qed.
Lemma lem2436088 (x' : int) : (term237 x') = term54.
Proof. exact (@lem1982719 (real_of_int x')). Qed.
Lemma lem2436089 (x' : int) : (term683 x') = term54.
Proof. exact (TRANS (@lem2436087 x') (@lem2436088 x')). Qed.
Lemma lem2436090 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2436091 (x' : int) : (term684 x') = term148.
Proof. exact (MK_COMB (@lem2436090) (@lem2436089 x')). Qed.
Lemma lem2436092 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem2436093 (x' : int) : (term727 x') = term239.
Proof. exact (MK_COMB (@lem2436091 x') (@lem2436092)). Qed.
Lemma lem2436094 (x' : int) : (term739 x') = term239.
Proof. exact (TRANS (@lem2435983 x') (@lem2436093 x')). Qed.
Lemma lem2436095 : term239 = term97.
Proof. exact (@lem1982721 term97). Qed.
Lemma lem2436096 (x' : int) : (term739 x') = term97.
Proof. exact (TRANS (@lem2436094 x') (@lem2436095)). Qed.
Lemma lem2436097 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2436098 (x' : int) : (term740 x') = term241.
Proof. exact (MK_COMB (@lem2436097) (@lem2436096 x')). Qed.
Lemma lem2436099 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2436100 (x' : int) : (term738 x') = term242.
Proof. exact (MK_COMB (@lem2436098 x') (@lem2436099)). Qed.
Lemma lem2436101 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : term242.
Proof. exact (EQ_MP (@lem2436100 x') (@lem2435982 y x x' h1)). Qed.
Lemma lem2436103 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2436104 : term242 = term243.
Proof. exact (@lem2436103 term54 term97). Qed.
Lemma lem2436106 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2436107 : term97 = term98.
Proof. exact (@lem2436106 term43). Qed.
Lemma lem2436109 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2436110 : term54 = term170.
Proof. exact (@lem2436109 (NUMERAL 0)). Qed.
Lemma lem2436111 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2436112 : term74 = term244.
Proof. exact (MK_COMB (@lem2436111) (@lem2436110)). Qed.
Lemma lem2436113 : term243 = term245.
Proof. exact (MK_COMB (@lem2436112) (@lem2436107)). Qed.
Lemma lem2436114 : term246.
Proof. exact (@lem1980026 term54 term42 term97 term42). Qed.
Lemma lem2436116 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436117 : term184 = term190.
Proof. exact (@lem2436116 (NUMERAL 0) term43). Qed.
Lemma lem2436118 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436119 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436120 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436119 h1) (fun h1 : term190 = True => @lem2436118)). Qed.
Lemma lem2436121 : term190 = True.
Proof. exact (EQ_MP (@lem2436120) (@lem2436118)). Qed.
Lemma lem2436122 : term184 = True.
Proof. exact (TRANS (@lem2436117) (@lem2436121)). Qed.
Lemma lem2436123 : True = term184.
Proof. exact (SYM (@lem2436122)). Qed.
Lemma lem2436124 : term184.
Proof. exact (EQ_MP (@lem2436123) (@lem0)). Qed.
Lemma lem2436125 : term247.
Proof. exact (@lem2436114 (@lem2436124)). Qed.
Lemma lem2436127 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436128 : term184 = term190.
Proof. exact (@lem2436127 (NUMERAL 0) term43). Qed.
Lemma lem2436129 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436130 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436131 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436130 h1) (fun h1 : term190 = True => @lem2436129)). Qed.
Lemma lem2436132 : term190 = True.
Proof. exact (EQ_MP (@lem2436131) (@lem2436129)). Qed.
Lemma lem2436133 : term184 = True.
Proof. exact (TRANS (@lem2436128) (@lem2436132)). Qed.
Lemma lem2436134 : True = term184.
Proof. exact (SYM (@lem2436133)). Qed.
Lemma lem2436135 : term184.
Proof. exact (EQ_MP (@lem2436134) (@lem0)). Qed.
Lemma lem2436136 : term245 = term248.
Proof. exact (@lem2436125 (@lem2436135)). Qed.
Lemma lem2436138 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2436139 : term101 = term112.
Proof. exact (@lem2436138 term43 term43). Qed.
Lemma lem2436140 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436141 : term109 = term43.
Proof. exact (EQ_MP (@lem2436140) (@lem940073)). Qed.
Lemma lem2436142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436143 : term107 = term42.
Proof. exact (MK_COMB (@lem2436142) (@lem2436141)). Qed.
Lemma lem2436144 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2436145 : term112 = term97.
Proof. exact (MK_COMB (@lem2436144) (@lem2436143)). Qed.
Lemma lem2436146 : term101 = term97.
Proof. exact (TRANS (@lem2436139) (@lem2436145)). Qed.
Lemma lem2436148 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2436149 : term195 = term54.
Proof. exact (@lem2436148 term43). Qed.
Lemma lem2436150 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2436151 : term249 = term74.
Proof. exact (MK_COMB (@lem2436150) (@lem2436149)). Qed.
Lemma lem2436152 : term248 = term243.
Proof. exact (MK_COMB (@lem2436151) (@lem2436146)). Qed.
Lemma lem2436154 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2436155 : term243 = term252.
Proof. exact (@lem2436154 (NUMERAL 0) term43). Qed.
Lemma lem2436156 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436157 (h1 : term191 = (BIT1 0)) : (term43 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2436158 : (term191 = (BIT1 0)) = ((term43 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436157 h1) (fun h1 : (term43 = (NUMERAL 0)) = False => @lem2436156)). Qed.
Lemma lem2436159 : (term43 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2436158) (@lem2436156)). Qed.
Lemma lem2436160 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2436161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2436162 : term253 = (and True).
Proof. exact (MK_COMB (@lem2436161) (@lem2436160)). Qed.
Lemma lem2436163 : term252 = (True /\ False).
Proof. exact (MK_COMB (@lem2436162) (@lem2436159)). Qed.
Lemma lem2436165 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2436166 : term252 = False.
Proof. exact (TRANS (@lem2436163) (@lem2436165)). Qed.
Lemma lem2436167 : term243 = False.
Proof. exact (TRANS (@lem2436155) (@lem2436166)). Qed.
Lemma lem2436168 : term248 = False.
Proof. exact (TRANS (@lem2436152) (@lem2436167)). Qed.
Lemma lem2436169 : term245 = False.
Proof. exact (TRANS (@lem2436136) (@lem2436168)). Qed.
Lemma lem2436170 : term243 = False.
Proof. exact (TRANS (@lem2436113) (@lem2436169)). Qed.
Lemma lem2436171 : term242 = False.
Proof. exact (TRANS (@lem2436104) (@lem2436170)). Qed.
Lemma lem2436172 (y : int) (x : int) (x' : int) (h1 : term658 y x x') : False.
Proof. exact (EQ_MP (@lem2436171) (@lem2436101 y x x' h1)). Qed.
Lemma lem2436173 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term661 y x x'.
Proof. exact (h1). Qed.
Lemma lem2436174 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term659 x x'.
Proof. exact (proj2 (@lem2436173 y x x' h1)). Qed.
Lemma lem2436176 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term655 x'.
Proof. exact (proj2 (@lem2436174 y x x' h1)). Qed.
Lemma lem2436178 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term644 x'.
Proof. exact (proj2 (@lem2436176 y x x' h1)). Qed.
Lemma lem2436179 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term499 x'.
Proof. exact (proj1 (@lem2436176 y x x' h1)). Qed.
Lemma lem2436181 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term729 x'.
Proof. exact (proj1 (@lem2436178 y x x' h1)). Qed.
Lemma lem2436183 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2436184 : term183 = term184.
Proof. exact (@lem2436183 term54 term42). Qed.
Lemma lem2436186 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2436187 : term42 = term94.
Proof. exact (@lem2436186 term43). Qed.
Lemma lem2436189 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2436190 : term54 = term170.
Proof. exact (@lem2436189 (NUMERAL 0)). Qed.
Lemma lem2436191 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2436192 : term185 = term186.
Proof. exact (MK_COMB (@lem2436191) (@lem2436190)). Qed.
Lemma lem2436193 : term184 = term187.
Proof. exact (MK_COMB (@lem2436192) (@lem2436187)). Qed.
Lemma lem2436194 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2436196 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436197 : term184 = term190.
Proof. exact (@lem2436196 (NUMERAL 0) term43). Qed.
Lemma lem2436198 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436199 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436200 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436199 h1) (fun h1 : term190 = True => @lem2436198)). Qed.
Lemma lem2436201 : term190 = True.
Proof. exact (EQ_MP (@lem2436200) (@lem2436198)). Qed.
Lemma lem2436202 : term184 = True.
Proof. exact (TRANS (@lem2436197) (@lem2436201)). Qed.
Lemma lem2436203 : True = term184.
Proof. exact (SYM (@lem2436202)). Qed.
Lemma lem2436204 : term184.
Proof. exact (EQ_MP (@lem2436203) (@lem0)). Qed.
Lemma lem2436205 : term192.
Proof. exact (@lem2436194 (@lem2436204)). Qed.
Lemma lem2436207 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436208 : term184 = term190.
Proof. exact (@lem2436207 (NUMERAL 0) term43). Qed.
Lemma lem2436209 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436210 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436211 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436210 h1) (fun h1 : term190 = True => @lem2436209)). Qed.
Lemma lem2436212 : term190 = True.
Proof. exact (EQ_MP (@lem2436211) (@lem2436209)). Qed.
Lemma lem2436213 : term184 = True.
Proof. exact (TRANS (@lem2436208) (@lem2436212)). Qed.
Lemma lem2436214 : True = term184.
Proof. exact (SYM (@lem2436213)). Qed.
Lemma lem2436215 : term184.
Proof. exact (EQ_MP (@lem2436214) (@lem0)). Qed.
Lemma lem2436216 : term187 = term193.
Proof. exact (@lem2436205 (@lem2436215)). Qed.
Lemma lem2436218 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2436219 : term106 = term107.
Proof. exact (@lem2436218 term43 term43). Qed.
Lemma lem2436220 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436221 : term109 = term43.
Proof. exact (EQ_MP (@lem2436220) (@lem940073)). Qed.
Lemma lem2436222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436223 : term107 = term42.
Proof. exact (MK_COMB (@lem2436222) (@lem2436221)). Qed.
Lemma lem2436224 : term106 = term42.
Proof. exact (TRANS (@lem2436219) (@lem2436223)). Qed.
Lemma lem2436226 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2436227 : term195 = term54.
Proof. exact (@lem2436226 term43). Qed.
Lemma lem2436228 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2436229 : term196 = term185.
Proof. exact (MK_COMB (@lem2436228) (@lem2436227)). Qed.
Lemma lem2436230 : term193 = term184.
Proof. exact (MK_COMB (@lem2436229) (@lem2436224)). Qed.
Lemma lem2436232 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436233 : term184 = term190.
Proof. exact (@lem2436232 (NUMERAL 0) term43). Qed.
Lemma lem2436234 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436235 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436236 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436235 h1) (fun h1 : term190 = True => @lem2436234)). Qed.
Lemma lem2436237 : term190 = True.
Proof. exact (EQ_MP (@lem2436236) (@lem2436234)). Qed.
Lemma lem2436238 : term184 = True.
Proof. exact (TRANS (@lem2436233) (@lem2436237)). Qed.
Lemma lem2436239 : term193 = True.
Proof. exact (TRANS (@lem2436230) (@lem2436238)). Qed.
Lemma lem2436240 : term187 = True.
Proof. exact (TRANS (@lem2436216) (@lem2436239)). Qed.
Lemma lem2436241 : term184 = True.
Proof. exact (TRANS (@lem2436193) (@lem2436240)). Qed.
Lemma lem2436242 : term183 = True.
Proof. exact (TRANS (@lem2436184) (@lem2436241)). Qed.
Lemma lem2436243 : True = term183.
Proof. exact (SYM (@lem2436242)). Qed.
Lemma lem2436244 : term183.
Proof. exact (EQ_MP (@lem2436243) (@lem0)). Qed.
Lemma lem2436245 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term669 x'.
Proof. exact (conj (@lem2436244) (@lem2436179 y x x' h1)). Qed.
Lemma lem2436247 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2436248 (x' : int) : term670 x'.
Proof. exact (@lem2436247 term42 (term117 x')). Qed.
Lemma lem2436249 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term671 x'.
Proof. exact (@lem2436248 x' (@lem2436245 y x x' h1)). Qed.
Lemma lem2436250 (x' : int) : (term672 x') = (term117 x').
Proof. exact (@lem1982733 (term117 x')). Qed.
Lemma lem2436251 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2436252 (x' : int) : (term673 x') = (term498 x').
Proof. exact (MK_COMB (@lem2436251) (@lem2436250 x')). Qed.
Lemma lem2436253 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2436254 (x' : int) : (term671 x') = (term499 x').
Proof. exact (MK_COMB (@lem2436252 x') (@lem2436253)). Qed.
Lemma lem2436255 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term499 x'.
Proof. exact (EQ_MP (@lem2436254 x') (@lem2436249 y x x' h1)). Qed.
Lemma lem2436257 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2436258 : term183 = term184.
Proof. exact (@lem2436257 term54 term42). Qed.
Lemma lem2436260 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2436261 : term42 = term94.
Proof. exact (@lem2436260 term43). Qed.
Lemma lem2436263 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2436264 : term54 = term170.
Proof. exact (@lem2436263 (NUMERAL 0)). Qed.
Lemma lem2436265 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2436266 : term185 = term186.
Proof. exact (MK_COMB (@lem2436265) (@lem2436264)). Qed.
Lemma lem2436267 : term184 = term187.
Proof. exact (MK_COMB (@lem2436266) (@lem2436261)). Qed.
Lemma lem2436268 : term188.
Proof. exact (@lem1980255 term54 term42 term42 term42). Qed.
Lemma lem2436270 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436271 : term184 = term190.
Proof. exact (@lem2436270 (NUMERAL 0) term43). Qed.
Lemma lem2436272 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436273 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436274 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436273 h1) (fun h1 : term190 = True => @lem2436272)). Qed.
Lemma lem2436275 : term190 = True.
Proof. exact (EQ_MP (@lem2436274) (@lem2436272)). Qed.
Lemma lem2436276 : term184 = True.
Proof. exact (TRANS (@lem2436271) (@lem2436275)). Qed.
Lemma lem2436277 : True = term184.
Proof. exact (SYM (@lem2436276)). Qed.
Lemma lem2436278 : term184.
Proof. exact (EQ_MP (@lem2436277) (@lem0)). Qed.
Lemma lem2436279 : term192.
Proof. exact (@lem2436268 (@lem2436278)). Qed.
Lemma lem2436281 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436282 : term184 = term190.
Proof. exact (@lem2436281 (NUMERAL 0) term43). Qed.
Lemma lem2436283 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436284 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436285 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436284 h1) (fun h1 : term190 = True => @lem2436283)). Qed.
Lemma lem2436286 : term190 = True.
Proof. exact (EQ_MP (@lem2436285) (@lem2436283)). Qed.
Lemma lem2436287 : term184 = True.
Proof. exact (TRANS (@lem2436282) (@lem2436286)). Qed.
Lemma lem2436288 : True = term184.
Proof. exact (SYM (@lem2436287)). Qed.
Lemma lem2436289 : term184.
Proof. exact (EQ_MP (@lem2436288) (@lem0)). Qed.
Lemma lem2436290 : term187 = term193.
Proof. exact (@lem2436279 (@lem2436289)). Qed.
Lemma lem2436292 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2436293 : term106 = term107.
Proof. exact (@lem2436292 term43 term43). Qed.
Lemma lem2436294 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436295 : term109 = term43.
Proof. exact (EQ_MP (@lem2436294) (@lem940073)). Qed.
Lemma lem2436296 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436297 : term107 = term42.
Proof. exact (MK_COMB (@lem2436296) (@lem2436295)). Qed.
Lemma lem2436298 : term106 = term42.
Proof. exact (TRANS (@lem2436293) (@lem2436297)). Qed.
Lemma lem2436300 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2436301 : term195 = term54.
Proof. exact (@lem2436300 term43). Qed.
Lemma lem2436302 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2436303 : term196 = term185.
Proof. exact (MK_COMB (@lem2436302) (@lem2436301)). Qed.
Lemma lem2436304 : term193 = term184.
Proof. exact (MK_COMB (@lem2436303) (@lem2436298)). Qed.
Lemma lem2436306 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436307 : term184 = term190.
Proof. exact (@lem2436306 (NUMERAL 0) term43). Qed.
Lemma lem2436308 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436309 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436310 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436309 h1) (fun h1 : term190 = True => @lem2436308)). Qed.
Lemma lem2436311 : term190 = True.
Proof. exact (EQ_MP (@lem2436310) (@lem2436308)). Qed.
Lemma lem2436312 : term184 = True.
Proof. exact (TRANS (@lem2436307) (@lem2436311)). Qed.
Lemma lem2436313 : term193 = True.
Proof. exact (TRANS (@lem2436304) (@lem2436312)). Qed.
Lemma lem2436314 : term187 = True.
Proof. exact (TRANS (@lem2436290) (@lem2436313)). Qed.
Lemma lem2436315 : term184 = True.
Proof. exact (TRANS (@lem2436267) (@lem2436314)). Qed.
Lemma lem2436316 : term183 = True.
Proof. exact (TRANS (@lem2436258) (@lem2436315)). Qed.
Lemma lem2436317 : True = term183.
Proof. exact (SYM (@lem2436316)). Qed.
Lemma lem2436318 : term183.
Proof. exact (EQ_MP (@lem2436317) (@lem0)). Qed.
Lemma lem2436319 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term730 x'.
Proof. exact (conj (@lem2436318) (@lem2436181 y x x' h1)). Qed.
Lemma lem2436321 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2436322 (x' : int) : term731 x'.
Proof. exact (@lem2436321 term42 (term121 x')). Qed.
Lemma lem2436323 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term732 x'.
Proof. exact (@lem2436322 x' (@lem2436319 y x x' h1)). Qed.
Lemma lem2436324 (x' : int) : (term733 x') = (term121 x').
Proof. exact (@lem1982733 (term121 x')). Qed.
Lemma lem2436325 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2436326 (x' : int) : (term734 x') = (term735 x').
Proof. exact (MK_COMB (@lem2436325) (@lem2436324 x')). Qed.
Lemma lem2436327 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2436328 (x' : int) : (term732 x') = (term729 x').
Proof. exact (MK_COMB (@lem2436326 x') (@lem2436327)). Qed.
Lemma lem2436329 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term729 x'.
Proof. exact (EQ_MP (@lem2436328 x') (@lem2436323 y x x' h1)). Qed.
Lemma lem2436330 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term736 x'.
Proof. exact (conj (@lem2436329 y x x' h1) (@lem2436255 y x x' h1)). Qed.
Lemma lem2436332 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2436333 (x' : int) : term737 x'.
Proof. exact (@lem2436332 (term121 x') (term117 x')). Qed.
Lemma lem2436334 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term738 x'.
Proof. exact (@lem2436333 x' (@lem2436330 y x x' h1)). Qed.
Lemma lem2436335 (x' : int) : (term739 x') = (term727 x').
Proof. exact (@lem1982763 (term121 x') (real_of_int x') term97). Qed.
Lemma lem2436336 (x' : int) : (term683 x') = (term236 x').
Proof. exact (@lem1982713 term97 (real_of_int x')). Qed.
Lemma lem2436338 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2436339 : term42 = term94.
Proof. exact (@lem2436338 term43). Qed.
Lemma lem2436341 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2436342 : term97 = term98.
Proof. exact (@lem2436341 term43). Qed.
Lemma lem2436343 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2436344 : term215 = term216.
Proof. exact (MK_COMB (@lem2436343) (@lem2436342)). Qed.
Lemma lem2436345 : term217 = term218.
Proof. exact (MK_COMB (@lem2436344) (@lem2436339)). Qed.
Lemma lem2436346 : term219.
Proof. exact (@lem1981473 term97 term42 term42 term42 term54 term42). Qed.
Lemma lem2436348 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436349 : term184 = term190.
Proof. exact (@lem2436348 (NUMERAL 0) term43). Qed.
Lemma lem2436350 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436351 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436352 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436351 h1) (fun h1 : term190 = True => @lem2436350)). Qed.
Lemma lem2436353 : term190 = True.
Proof. exact (EQ_MP (@lem2436352) (@lem2436350)). Qed.
Lemma lem2436354 : term184 = True.
Proof. exact (TRANS (@lem2436349) (@lem2436353)). Qed.
Lemma lem2436355 : True = term184.
Proof. exact (SYM (@lem2436354)). Qed.
Lemma lem2436356 : term184.
Proof. exact (EQ_MP (@lem2436355) (@lem0)). Qed.
Lemma lem2436357 : term220.
Proof. exact (@lem2436346 (@lem2436356)). Qed.
Lemma lem2436359 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436360 : term184 = term190.
Proof. exact (@lem2436359 (NUMERAL 0) term43). Qed.
Lemma lem2436361 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436362 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436363 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436362 h1) (fun h1 : term190 = True => @lem2436361)). Qed.
Lemma lem2436364 : term190 = True.
Proof. exact (EQ_MP (@lem2436363) (@lem2436361)). Qed.
Lemma lem2436365 : term184 = True.
Proof. exact (TRANS (@lem2436360) (@lem2436364)). Qed.
Lemma lem2436366 : True = term184.
Proof. exact (SYM (@lem2436365)). Qed.
Lemma lem2436367 : term184.
Proof. exact (EQ_MP (@lem2436366) (@lem0)). Qed.
Lemma lem2436368 : term221.
Proof. exact (@lem2436357 (@lem2436367)). Qed.
Lemma lem2436370 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436371 : term184 = term190.
Proof. exact (@lem2436370 (NUMERAL 0) term43). Qed.
Lemma lem2436372 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436373 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436374 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436373 h1) (fun h1 : term190 = True => @lem2436372)). Qed.
Lemma lem2436375 : term190 = True.
Proof. exact (EQ_MP (@lem2436374) (@lem2436372)). Qed.
Lemma lem2436376 : term184 = True.
Proof. exact (TRANS (@lem2436371) (@lem2436375)). Qed.
Lemma lem2436377 : True = term184.
Proof. exact (SYM (@lem2436376)). Qed.
Lemma lem2436378 : term184.
Proof. exact (EQ_MP (@lem2436377) (@lem0)). Qed.
Lemma lem2436379 : term222.
Proof. exact (@lem2436368 (@lem2436378)). Qed.
Lemma lem2436381 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2436382 : term106 = term107.
Proof. exact (@lem2436381 term43 term43). Qed.
Lemma lem2436383 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436384 : term109 = term43.
Proof. exact (EQ_MP (@lem2436383) (@lem940073)). Qed.
Lemma lem2436385 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436386 : term107 = term42.
Proof. exact (MK_COMB (@lem2436385) (@lem2436384)). Qed.
Lemma lem2436387 : term106 = term42.
Proof. exact (TRANS (@lem2436382) (@lem2436386)). Qed.
Lemma lem2436389 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2436390 : term101 = term112.
Proof. exact (@lem2436389 term43 term43). Qed.
Lemma lem2436391 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436392 : term109 = term43.
Proof. exact (EQ_MP (@lem2436391) (@lem940073)). Qed.
Lemma lem2436393 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436394 : term107 = term42.
Proof. exact (MK_COMB (@lem2436393) (@lem2436392)). Qed.
Lemma lem2436395 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2436396 : term112 = term97.
Proof. exact (MK_COMB (@lem2436395) (@lem2436394)). Qed.
Lemma lem2436397 : term101 = term97.
Proof. exact (TRANS (@lem2436390) (@lem2436396)). Qed.
Lemma lem2436398 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2436399 : term223 = term215.
Proof. exact (MK_COMB (@lem2436398) (@lem2436397)). Qed.
Lemma lem2436400 : term224 = term217.
Proof. exact (MK_COMB (@lem2436399) (@lem2436387)). Qed.
Lemma lem2436402 (m : nat) : (term225 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2436403 : term217 = term54.
Proof. exact (@lem2436402 term43). Qed.
Lemma lem2436404 : term224 = term54.
Proof. exact (TRANS (@lem2436400) (@lem2436403)). Qed.
Lemma lem2436405 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2436406 : term226 = term227.
Proof. exact (MK_COMB (@lem2436405) (@lem2436404)). Qed.
Lemma lem2436407 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem2436408 : term228 = term195.
Proof. exact (MK_COMB (@lem2436406) (@lem2436407)). Qed.
Lemma lem2436410 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2436411 : term195 = term54.
Proof. exact (@lem2436410 term43). Qed.
Lemma lem2436412 : term228 = term54.
Proof. exact (TRANS (@lem2436408) (@lem2436411)). Qed.
Lemma lem2436414 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2436415 : term106 = term107.
Proof. exact (@lem2436414 term43 term43). Qed.
Lemma lem2436416 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436417 : term109 = term43.
Proof. exact (EQ_MP (@lem2436416) (@lem940073)). Qed.
Lemma lem2436418 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436419 : term107 = term42.
Proof. exact (MK_COMB (@lem2436418) (@lem2436417)). Qed.
Lemma lem2436420 : term106 = term42.
Proof. exact (TRANS (@lem2436415) (@lem2436419)). Qed.
Lemma lem2436421 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2436422 : term229 = term195.
Proof. exact (MK_COMB (@lem2436421) (@lem2436420)). Qed.
Lemma lem2436424 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2436425 : term195 = term54.
Proof. exact (@lem2436424 term43). Qed.
Lemma lem2436426 : term229 = term54.
Proof. exact (TRANS (@lem2436422) (@lem2436425)). Qed.
Lemma lem2436427 : term54 = term229.
Proof. exact (SYM (@lem2436426)). Qed.
Lemma lem2436428 : term228 = term229.
Proof. exact (TRANS (@lem2436412) (@lem2436427)). Qed.
Lemma lem2436429 : term218 = term170.
Proof. exact (@lem2436379 (@lem2436428)). Qed.
Lemma lem2436430 : term217 = term170.
Proof. exact (TRANS (@lem2436345) (@lem2436429)). Qed.
Lemma lem2436432 (x : real) : (term115 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2436433 : term170 = term54.
Proof. exact (@lem2436432 term54). Qed.
Lemma lem2436434 : term217 = term54.
Proof. exact (TRANS (@lem2436430) (@lem2436433)). Qed.
Lemma lem2436435 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2436436 : term230 = term227.
Proof. exact (MK_COMB (@lem2436435) (@lem2436434)). Qed.
Lemma lem2436437 (x' : int) : (real_of_int x') = (real_of_int x').
Proof. exact (eq_refl (real_of_int x')). Qed.
Lemma lem2436438 (x' : int) : (term236 x') = (term237 x').
Proof. exact (MK_COMB (@lem2436436) (@lem2436437 x')). Qed.
Lemma lem2436439 (x' : int) : (term683 x') = (term237 x').
Proof. exact (TRANS (@lem2436336 x') (@lem2436438 x')). Qed.
Lemma lem2436440 (x' : int) : (term237 x') = term54.
Proof. exact (@lem1982719 (real_of_int x')). Qed.
Lemma lem2436441 (x' : int) : (term683 x') = term54.
Proof. exact (TRANS (@lem2436439 x') (@lem2436440 x')). Qed.
Lemma lem2436442 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2436443 (x' : int) : (term684 x') = term148.
Proof. exact (MK_COMB (@lem2436442) (@lem2436441 x')). Qed.
Lemma lem2436444 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem2436445 (x' : int) : (term727 x') = term239.
Proof. exact (MK_COMB (@lem2436443 x') (@lem2436444)). Qed.
Lemma lem2436446 (x' : int) : (term739 x') = term239.
Proof. exact (TRANS (@lem2436335 x') (@lem2436445 x')). Qed.
Lemma lem2436447 : term239 = term97.
Proof. exact (@lem1982721 term97). Qed.
Lemma lem2436448 (x' : int) : (term739 x') = term97.
Proof. exact (TRANS (@lem2436446 x') (@lem2436447)). Qed.
Lemma lem2436449 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2436450 (x' : int) : (term740 x') = term241.
Proof. exact (MK_COMB (@lem2436449) (@lem2436448 x')). Qed.
Lemma lem2436451 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem2436452 (x' : int) : (term738 x') = term242.
Proof. exact (MK_COMB (@lem2436450 x') (@lem2436451)). Qed.
Lemma lem2436453 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : term242.
Proof. exact (EQ_MP (@lem2436452 x') (@lem2436334 y x x' h1)). Qed.
Lemma lem2436455 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2436456 : term242 = term243.
Proof. exact (@lem2436455 term54 term97). Qed.
Lemma lem2436458 (x : nat) : (term95 x) = (term96 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2436459 : term97 = term98.
Proof. exact (@lem2436458 term43). Qed.
Lemma lem2436461 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2436462 : term54 = term170.
Proof. exact (@lem2436461 (NUMERAL 0)). Qed.
Lemma lem2436463 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2436464 : term74 = term244.
Proof. exact (MK_COMB (@lem2436463) (@lem2436462)). Qed.
Lemma lem2436465 : term243 = term245.
Proof. exact (MK_COMB (@lem2436464) (@lem2436459)). Qed.
Lemma lem2436466 : term246.
Proof. exact (@lem1980026 term54 term42 term97 term42). Qed.
Lemma lem2436468 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436469 : term184 = term190.
Proof. exact (@lem2436468 (NUMERAL 0) term43). Qed.
Lemma lem2436470 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436471 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436472 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436471 h1) (fun h1 : term190 = True => @lem2436470)). Qed.
Lemma lem2436473 : term190 = True.
Proof. exact (EQ_MP (@lem2436472) (@lem2436470)). Qed.
Lemma lem2436474 : term184 = True.
Proof. exact (TRANS (@lem2436469) (@lem2436473)). Qed.
Lemma lem2436475 : True = term184.
Proof. exact (SYM (@lem2436474)). Qed.
Lemma lem2436476 : term184.
Proof. exact (EQ_MP (@lem2436475) (@lem0)). Qed.
Lemma lem2436477 : term247.
Proof. exact (@lem2436466 (@lem2436476)). Qed.
Lemma lem2436479 (m : nat) (n : nat) : (term189 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2436480 : term184 = term190.
Proof. exact (@lem2436479 (NUMERAL 0) term43). Qed.
Lemma lem2436481 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436482 (h1 : term191 = (BIT1 0)) : term190 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2436483 : (term191 = (BIT1 0)) = (term190 = True).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436482 h1) (fun h1 : term190 = True => @lem2436481)). Qed.
Lemma lem2436484 : term190 = True.
Proof. exact (EQ_MP (@lem2436483) (@lem2436481)). Qed.
Lemma lem2436485 : term184 = True.
Proof. exact (TRANS (@lem2436480) (@lem2436484)). Qed.
Lemma lem2436486 : True = term184.
Proof. exact (SYM (@lem2436485)). Qed.
Lemma lem2436487 : term184.
Proof. exact (EQ_MP (@lem2436486) (@lem0)). Qed.
Lemma lem2436488 : term245 = term248.
Proof. exact (@lem2436477 (@lem2436487)). Qed.
Lemma lem2436490 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2436491 : term101 = term112.
Proof. exact (@lem2436490 term43 term43). Qed.
Lemma lem2436492 : (term108 = (BIT1 0)) = (term109 = term43).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2436493 : term109 = term43.
Proof. exact (EQ_MP (@lem2436492) (@lem940073)). Qed.
Lemma lem2436494 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2436495 : term107 = term42.
Proof. exact (MK_COMB (@lem2436494) (@lem2436493)). Qed.
Lemma lem2436496 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2436497 : term112 = term97.
Proof. exact (MK_COMB (@lem2436496) (@lem2436495)). Qed.
Lemma lem2436498 : term101 = term97.
Proof. exact (TRANS (@lem2436491) (@lem2436497)). Qed.
Lemma lem2436500 (x : nat) : (term194 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2436501 : term195 = term54.
Proof. exact (@lem2436500 term43). Qed.
Lemma lem2436502 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2436503 : term249 = term74.
Proof. exact (MK_COMB (@lem2436502) (@lem2436501)). Qed.
Lemma lem2436504 : term248 = term243.
Proof. exact (MK_COMB (@lem2436503) (@lem2436498)). Qed.
Lemma lem2436506 (m : nat) (n : nat) : (term250 m n) = (term251 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2436507 : term243 = term252.
Proof. exact (@lem2436506 (NUMERAL 0) term43). Qed.
Lemma lem2436508 : term191 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2436509 (h1 : term191 = (BIT1 0)) : (term43 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2436510 : (term191 = (BIT1 0)) = ((term43 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term191 = (BIT1 0) => @lem2436509 h1) (fun h1 : (term43 = (NUMERAL 0)) = False => @lem2436508)). Qed.
Lemma lem2436511 : (term43 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2436510) (@lem2436508)). Qed.
Lemma lem2436512 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2436513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2436514 : term253 = (and True).
Proof. exact (MK_COMB (@lem2436513) (@lem2436512)). Qed.
Lemma lem2436515 : term252 = (True /\ False).
Proof. exact (MK_COMB (@lem2436514) (@lem2436511)). Qed.
Lemma lem2436517 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2436518 : term252 = False.
Proof. exact (TRANS (@lem2436515) (@lem2436517)). Qed.
Lemma lem2436519 : term243 = False.
Proof. exact (TRANS (@lem2436507) (@lem2436518)). Qed.
Lemma lem2436520 : term248 = False.
Proof. exact (TRANS (@lem2436504) (@lem2436519)). Qed.
Lemma lem2436521 : term245 = False.
Proof. exact (TRANS (@lem2436488) (@lem2436520)). Qed.
Lemma lem2436522 : term243 = False.
Proof. exact (TRANS (@lem2436465) (@lem2436521)). Qed.
Lemma lem2436523 : term242 = False.
Proof. exact (TRANS (@lem2436456) (@lem2436522)). Qed.
Lemma lem2436524 (y : int) (x : int) (x' : int) (h1 : term661 y x x') : False.
Proof. exact (EQ_MP (@lem2436523) (@lem2436453 y x x' h1)). Qed.
Lemma lem2436525 (y : int) (x : int) (x' : int) (h1 : term664 y x x') : False.
Proof. exact (or_elim (@lem2435820 y x x' h1) (fun h0 : term658 y x x' => @lem2436172 y x x' h0) (fun h0 : term661 y x x' => @lem2436524 y x x' h0)). Qed.
Lemma lem2436526 (y : int) (x : int) (x' : int) (h1 : term666 y x x') : False.
Proof. exact (or_elim (@lem2435113 y x x' h1) (fun h0 : term654 y x x' => @lem2435819 y x x' h0) (fun h0 : term664 y x x' => @lem2436525 y x x' h0)). Qed.
Lemma lem2436527 (y : int) (x : int) (x' : int) (h1 : term668 y x x') : False.
Proof. exact (or_elim (@lem2433210 y x x' h1) (fun h0 : term635 y x' x => @lem2435112 y x' x h0) (fun h0 : term666 y x x' => @lem2436526 y x x' h0)). Qed.
Lemma lem2436528 (y : int) (x : int) (x' : int) (h1 : term599 y x x') : term599 y x x'.
Proof. exact (h1). Qed.
Lemma lem2436529 (y : int) (x : int) (x' : int) (h1 : term599 y x x') : term668 y x x'.
Proof. exact (EQ_MP (@lem2433209 y x x') (@lem2436528 y x x' h1)). Qed.
Lemma lem2436530 (y : int) (x : int) (x' : int) (h1 : term599 y x x') : (term668 y x x') = False.
Proof. exact (prop_ext (fun h2 : term668 y x x' => @lem2436527 y x x' h2) (fun h2 : False => @lem2436529 y x x' h1)). Qed.
Lemma lem2436531 (y : int) (x : int) (x' : int) (h1 : term599 y x x') : False.
Proof. exact (EQ_MP (@lem2436530 y x x' h1) (@lem2436529 y x x' h1)). Qed.
Lemma lem2436532 (y : int) (x : int) (x' : int) (h1 : term478 y x x') : term478 y x x'.
Proof. exact (h1). Qed.
Lemma lem2436533 (y : int) (x : int) (x' : int) (h1 : term478 y x x') : term599 y x x'.
Proof. exact (EQ_MP (@lem2432844 y x x') (@lem2436532 y x x' h1)). Qed.
Lemma lem2436534 (y : int) (x : int) (x' : int) (h1 : term478 y x x') : (term599 y x x') = False.
Proof. exact (prop_ext (fun h2 : term599 y x x' => @lem2436531 y x x' h2) (fun h2 : False => @lem2436533 y x x' h1)). Qed.
Lemma lem2436535 (y : int) (x : int) (x' : int) (h1 : term478 y x x') : False.
Proof. exact (EQ_MP (@lem2436534 y x x' h1) (@lem2436533 y x x' h1)). Qed.
Lemma lem2436536 (y : int) (x : int) (x' : int) : term741 y x x'.
Proof. exact (fun h0 : term478 y x x' => @lem2436535 y x x' h0). Qed.
Lemma lem2436537 (y : int) (x : int) (x' : int) : term742 y x x'.
Proof. exact (@lem1386578 (term743 y x x')). Qed.
Lemma lem2436540 (y : int) (x : int) (x' : int) : term743 y x x'.
Proof. exact (@lem2436537 y x x' (@lem2436536 y x x')). Qed.
Lemma lem2436541 (y : int) (x : int) (x' : int) : (term477 y x x') = (term411 y x x').
Proof. exact (SYM (@lem2432087 y x x')). Qed.
Lemma lem2436542 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2436543 (y : int) (x : int) (x' : int) : (term743 y x x') = (term393 y x x').
Proof. exact (MK_COMB (@lem2436542) (@lem2436541 y x x')). Qed.
Lemma lem2436544 (y : int) (x : int) (x' : int) : term393 y x x'.
Proof. exact (EQ_MP (@lem2436543 y x x') (@lem2436540 y x x')). Qed.
Lemma lem2436545 (y : int) (x : int) (x' : int) : term394 y x x'.
Proof. exact (EQ_MP (@lem2431839 y x x') (@lem2436544 y x x')). Qed.
Lemma lem2436546 (y : int) (x : int) (x' : int) : (term394 y x x') = ((term394 y x x') = True).
Proof. exact (@lem7 (term394 y x x')). Qed.
Lemma lem2436547 (y : int) (x : int) (x' : int) : (term394 y x x') = True.
Proof. exact (EQ_MP (@lem2436546 y x x') (@lem2436545 y x x')). Qed.
Lemma lem2436548 (y : int) (x : int) (x' : int) : True = (term394 y x x').
Proof. exact (SYM (@lem2436547 y x x')). Qed.
Lemma lem2436549 (y : int) (x : int) (x' : int) : term394 y x x'.
Proof. exact (EQ_MP (@lem2436548 y x x') (@lem0)). Qed.
Lemma lem2436550 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : term412 x x'.
Proof. exact (@lem2436549 y x x' (@lem2431832 y x x' h1)). Qed.
Lemma lem2436551 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : y = (int_mul x x')) : term407 x x'.
Proof. exact (@lem2436550 y x x' h2 (@lem2431835 x h1)). Qed.
Lemma lem2436552 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : term390 x') (h3 : y = (int_mul x x')) : term403 x x'.
Proof. exact (@lem2436551 y x x' h1 h3 (@lem2431834 x' h2)). Qed.
Lemma lem2436553 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : term390 x') (h3 : y = (int_mul x x')) : term379 x x'.
Proof. exact (@lem2431838 x x' (@lem2436552 y x x' h1 h2 h3)). Qed.
Lemma lem2436554 (x : int) (x' : int) (h1 : term389 x x') : term390 x'.
Proof. exact (proj2 (@lem2431833 x x' h1)). Qed.
Lemma lem2436555 (x : int) (x' : int) (h1 : term389 x x') : term390 x.
Proof. exact (proj1 (@lem2431833 x x' h1)). Qed.
Lemma lem2436556 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : term390 x') (h3 : y = (int_mul x x')) : (term390 x') = (term379 x x').
Proof. exact (prop_ext (fun h4 : term390 x' => @lem2436553 y x x' h1 h2 h3) (fun h4 : term379 x x' => @lem2431834 x' h2)). Qed.
Lemma lem2436557 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : term390 x') (h3 : y = (int_mul x x')) : term379 x x'.
Proof. exact (EQ_MP (@lem2436556 y x x' h1 h2 h3) (@lem2431834 x' h2)). Qed.
Lemma lem2436558 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : term390 x') (h3 : y = (int_mul x x')) : (term390 x) = (term379 x x').
Proof. exact (prop_ext (fun h4 : term390 x => @lem2436557 y x x' h1 h2 h3) (fun h4 : term379 x x' => @lem2431835 x h1)). Qed.
Lemma lem2436559 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : term390 x') (h3 : y = (int_mul x x')) : term379 x x'.
Proof. exact (EQ_MP (@lem2436558 y x x' h1 h2 h3) (@lem2431835 x h1)). Qed.
Lemma lem2436560 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : term389 x x') (h3 : y = (int_mul x x')) : (term390 x') = (term379 x x').
Proof. exact (prop_ext (fun h4 : term390 x' => @lem2436559 y x x' h1 h4 h3) (fun h4 : term379 x x' => @lem2436554 x x' h2)). Qed.
Lemma lem2436561 (y : int) (x : int) (x' : int) (h1 : term390 x) (h2 : term389 x x') (h3 : y = (int_mul x x')) : term379 x x'.
Proof. exact (EQ_MP (@lem2436560 y x x' h1 h2 h3) (@lem2436554 x x' h2)). Qed.
Lemma lem2436562 (y : int) (x : int) (x' : int) (h1 : term389 x x') (h2 : y = (int_mul x x')) : (term390 x) = (term379 x x').
Proof. exact (prop_ext (fun h3 : term390 x => @lem2436561 y x x' h3 h1 h2) (fun h3 : term379 x x' => @lem2436555 x x' h1)). Qed.
Lemma lem2436563 (y : int) (x : int) (x' : int) (h1 : term389 x x') (h2 : y = (int_mul x x')) : term379 x x'.
Proof. exact (EQ_MP (@lem2436562 y x x' h1 h2) (@lem2436555 x x' h1)). Qed.
Lemma lem2436564 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : term381 x x'.
Proof. exact (fun h0 : term389 x x' => @lem2436563 y x x' h0 h1). Qed.
Lemma lem2436565 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : (y = (int_mul x x')) = (term381 x x').
Proof. exact (prop_ext (fun h2 : y = (int_mul x x') => @lem2436564 y x x' h1) (fun h2 : term381 x x' => @lem2431832 y x x' h1)). Qed.
Lemma lem2436566 (y : int) (x : int) (x' : int) (h1 : y = (int_mul x x')) : term381 x x'.
Proof. exact (EQ_MP (@lem2436565 y x x' h1) (@lem2431832 y x x' h1)). Qed.
Lemma lem2436567 (y : int) (x : int) (x' : int) : term382 y x x'.
Proof. exact (fun h0 : y = (int_mul x x') => @lem2436566 y x x' h0). Qed.
Lemma lem2436572 (y : int) (x : int) : term384 y x.
Proof. exact (fun x' : int => @lem2436567 y x x'). Qed.
Lemma lem2436577 (x : int) : term386 x.
Proof. exact (fun y : int => @lem2436572 y x). Qed.
Lemma lem2436582 : term388.
Proof. exact (fun x : int => @lem2436577 x). Qed.
Lemma lem2436583 : term378.
Proof. exact (EQ_MP (@lem2431831) (@lem2436582)). Qed.
Lemma lem2436584 : term370.
Proof. exact (EQ_MP (@lem2431768) (@lem2436583)). Qed.
Lemma lem2436585 : term369.
Proof. exact (EQ_MP (@lem2431711) (@lem2436584)). Qed.
