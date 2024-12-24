Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267613_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1396812_spec.
Require Import thm1482703_spec.
Require Import thm1482981_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
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
Require Import thm1982717_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988293_spec.
Require Import thm1988318_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988338_spec.
Require Import thm1988348_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2259384 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2259401 (x : real) (n : nat) : (term0 x n) = (term1 x n).
Proof. exact (@lem17160 (x = (real_of_num n)) (x = (term2 n))). Qed.
Lemma lem2259407 (x : real) (n : nat) : (term3 x n) = (term3 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem2259409 (x : real) (n : nat) : (term4 x n) = (term4 x n).
Proof. exact (eq_refl (term4 x n)). Qed.
Lemma lem2259410 (x : real) (n : nat) : (term5 x n) = (term6 x n).
Proof. exact (MK_COMB (@lem2259409 x n) (@lem2259401 x n)). Qed.
Lemma lem2259411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259412 (x : real) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (MK_COMB (@lem2259411) (@lem2259410 x n)). Qed.
Lemma lem2259413 (x : real) (n : nat) : (term9 x n) = (term10 x n).
Proof. exact (MK_COMB (@lem2259412 x n) (@lem2259407 x n)). Qed.
Lemma lem2259414 (x : real) (n : nat) : (term11 x n) = (term9 x n).
Proof. exact (@lem17646 ((real_abs x) = (real_of_num n)) (term12 x n)). Qed.
Lemma lem2259444 (x : real) (n : nat) : (term11 x n) = (term10 x n).
Proof. exact (TRANS (@lem2259414 x n) (@lem2259413 x n)). Qed.
Lemma lem2259445 (x : real) (n : nat) : ((real_abs x) = (real_of_num n)) = ((term13 x n) = term14).
Proof. exact (@lem1988293 (real_abs x) (real_of_num n)). Qed.
Lemma lem2259460 (x : real) (n : nat) : (term13 x n) = (term15 x n).
Proof. exact (@lem1982792 (real_abs x) (real_of_num n)). Qed.
Lemma lem2259461 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2259462 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem2259461) (@lem2259460 x n)). Qed.
Lemma lem2259463 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259464 (x : real) (n : nat) : ((term13 x n) = term14) = ((term15 x n) = term14).
Proof. exact (MK_COMB (@lem2259462 x n) (@lem2259463)). Qed.
Lemma lem2259465 (x : real) (n : nat) : ((real_abs x) = (real_of_num n)) = ((term15 x n) = term14).
Proof. exact (TRANS (@lem2259445 x n) (@lem2259464 x n)). Qed.
Lemma lem2259466 (x : real) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (@lem1988318 x (real_of_num n)). Qed.
Lemma lem2259479 (x : real) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (@lem1982792 x (real_of_num n)). Qed.
Lemma lem2259480 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2259481 (x : real) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (MK_COMB (@lem2259480) (@lem2259479 x n)). Qed.
Lemma lem2259482 (x : real) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (@lem1982785 (term21 x n)). Qed.
Lemma lem2259483 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (@lem1982781 x term26 (term27 n)). Qed.
Lemma lem2259484 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2259486 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259487 : term26 = term31.
Proof. exact (@lem2259486 term32). Qed.
Lemma lem2259489 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259490 : term26 = term31.
Proof. exact (@lem2259489 term32). Qed.
Lemma lem2259491 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259492 : term33 = term34.
Proof. exact (MK_COMB (@lem2259491) (@lem2259490)). Qed.
Lemma lem2259493 : term35 = term36.
Proof. exact (MK_COMB (@lem2259492) (@lem2259487)). Qed.
Lemma lem2259494 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2259496 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2259497 : term41 = term42.
Proof. exact (@lem2259496 term32 term32). Qed.
Lemma lem2259498 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259499 : term44 = term32.
Proof. exact (EQ_MP (@lem2259498) (@lem940073)). Qed.
Lemma lem2259500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259501 : term42 = term38.
Proof. exact (MK_COMB (@lem2259500) (@lem2259499)). Qed.
Lemma lem2259502 : term41 = term38.
Proof. exact (TRANS (@lem2259497) (@lem2259501)). Qed.
Lemma lem2259504 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2259505 : term35 = term42.
Proof. exact (@lem2259504 term32 term32). Qed.
Lemma lem2259506 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259507 : term44 = term32.
Proof. exact (EQ_MP (@lem2259506) (@lem940073)). Qed.
Lemma lem2259508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259509 : term42 = term38.
Proof. exact (MK_COMB (@lem2259508) (@lem2259507)). Qed.
Lemma lem2259510 : term35 = term38.
Proof. exact (TRANS (@lem2259505) (@lem2259509)). Qed.
Lemma lem2259511 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2259512 : term46 = term47.
Proof. exact (MK_COMB (@lem2259511) (@lem2259510)). Qed.
Lemma lem2259513 : term37 = term48.
Proof. exact (MK_COMB (@lem2259512) (@lem2259502)). Qed.
Lemma lem2259514 : term36 = term48.
Proof. exact (TRANS (@lem2259494) (@lem2259513)). Qed.
Lemma lem2259515 : term35 = term48.
Proof. exact (TRANS (@lem2259493) (@lem2259514)). Qed.
Lemma lem2259517 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2259518 : term48 = term38.
Proof. exact (@lem2259517 term38). Qed.
Lemma lem2259519 : term35 = term38.
Proof. exact (TRANS (@lem2259515) (@lem2259518)). Qed.
Lemma lem2259520 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259521 : term50 = term51.
Proof. exact (MK_COMB (@lem2259520) (@lem2259519)). Qed.
Lemma lem2259522 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2259523 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2259521) (@lem2259522 n)). Qed.
Lemma lem2259524 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2259484 n) (@lem2259523 n)). Qed.
Lemma lem2259525 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2259526 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2259524 n) (@lem2259525 n)). Qed.
Lemma lem2259529 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2259530 (x : real) (n : nat) : (term25 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem2259529 x) (@lem2259526 n)). Qed.
Lemma lem2259531 (x : real) (n : nat) : (term24 x n) = (term54 x n).
Proof. exact (TRANS (@lem2259483 x n) (@lem2259530 x n)). Qed.
Lemma lem2259532 (x : real) (n : nat) : (term23 x n) = (term54 x n).
Proof. exact (TRANS (@lem2259482 x n) (@lem2259531 x n)). Qed.
Lemma lem2259533 (x : real) (n : nat) : (term55 x n) = (term55 x n).
Proof. exact (eq_refl (term55 x n)). Qed.
Lemma lem2259534 (x : real) (n : nat) : ((term22 x n) = (term23 x n)) = ((term22 x n) = (term54 x n)).
Proof. exact (MK_COMB (@lem2259533 x n) (@lem2259532 x n)). Qed.
Lemma lem2259535 (x : real) (n : nat) : (term22 x n) = (term54 x n).
Proof. exact (EQ_MP (@lem2259534 x n) (@lem2259481 x n)). Qed.
Lemma lem2259536 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2259537 (x : real) (n : nat) : (term56 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem2259536) (@lem2259535 x n)). Qed.
Lemma lem2259538 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259539 (x : real) (n : nat) : (term58 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem2259537 x n) (@lem2259538)). Qed.
Lemma lem2259540 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2259541 (x : real) (n : nat) : (term60 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem2259540) (@lem2259479 x n)). Qed.
Lemma lem2259542 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259543 (x : real) (n : nat) : (term62 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem2259541 x n) (@lem2259542)). Qed.
Lemma lem2259544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259545 (x : real) (n : nat) : (term64 x n) = (term65 x n).
Proof. exact (MK_COMB (@lem2259544) (@lem2259543 x n)). Qed.
Lemma lem2259546 (x : real) (n : nat) : (term19 x n) = (term66 x n).
Proof. exact (MK_COMB (@lem2259545 x n) (@lem2259539 x n)). Qed.
Lemma lem2259547 (x : real) (n : nat) : (term18 x n) = (term66 x n).
Proof. exact (TRANS (@lem2259466 x n) (@lem2259546 x n)). Qed.
Lemma lem2259548 (x : real) (n : nat) : (term67 x n) = (term68 x n).
Proof. exact (@lem1988318 x (term2 n)). Qed.
Lemma lem2259555 (n : nat) : (term2 n) = (term27 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2259558 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem2259559 (x : real) (n : nat) : (term69 x n) = (term70 x n).
Proof. exact (MK_COMB (@lem2259558 x) (@lem2259555 n)). Qed.
Lemma lem2259560 (x : real) (n : nat) : (term70 x n) = (term71 x n).
Proof. exact (@lem1982792 x (term27 n)). Qed.
Lemma lem2259561 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2259563 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259564 : term26 = term31.
Proof. exact (@lem2259563 term32). Qed.
Lemma lem2259566 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259567 : term26 = term31.
Proof. exact (@lem2259566 term32). Qed.
Lemma lem2259568 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259569 : term33 = term34.
Proof. exact (MK_COMB (@lem2259568) (@lem2259567)). Qed.
Lemma lem2259570 : term35 = term36.
Proof. exact (MK_COMB (@lem2259569) (@lem2259564)). Qed.
Lemma lem2259571 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2259573 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2259574 : term41 = term42.
Proof. exact (@lem2259573 term32 term32). Qed.
Lemma lem2259575 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259576 : term44 = term32.
Proof. exact (EQ_MP (@lem2259575) (@lem940073)). Qed.
Lemma lem2259577 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259578 : term42 = term38.
Proof. exact (MK_COMB (@lem2259577) (@lem2259576)). Qed.
Lemma lem2259579 : term41 = term38.
Proof. exact (TRANS (@lem2259574) (@lem2259578)). Qed.
Lemma lem2259581 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2259582 : term35 = term42.
Proof. exact (@lem2259581 term32 term32). Qed.
Lemma lem2259583 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259584 : term44 = term32.
Proof. exact (EQ_MP (@lem2259583) (@lem940073)). Qed.
Lemma lem2259585 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259586 : term42 = term38.
Proof. exact (MK_COMB (@lem2259585) (@lem2259584)). Qed.
Lemma lem2259587 : term35 = term38.
Proof. exact (TRANS (@lem2259582) (@lem2259586)). Qed.
Lemma lem2259588 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2259589 : term46 = term47.
Proof. exact (MK_COMB (@lem2259588) (@lem2259587)). Qed.
Lemma lem2259590 : term37 = term48.
Proof. exact (MK_COMB (@lem2259589) (@lem2259579)). Qed.
Lemma lem2259591 : term36 = term48.
Proof. exact (TRANS (@lem2259571) (@lem2259590)). Qed.
Lemma lem2259592 : term35 = term48.
Proof. exact (TRANS (@lem2259570) (@lem2259591)). Qed.
Lemma lem2259594 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2259595 : term48 = term38.
Proof. exact (@lem2259594 term38). Qed.
Lemma lem2259596 : term35 = term38.
Proof. exact (TRANS (@lem2259592) (@lem2259595)). Qed.
Lemma lem2259597 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259598 : term50 = term51.
Proof. exact (MK_COMB (@lem2259597) (@lem2259596)). Qed.
Lemma lem2259599 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2259600 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2259598) (@lem2259599 n)). Qed.
Lemma lem2259601 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2259561 n) (@lem2259600 n)). Qed.
Lemma lem2259602 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2259603 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2259601 n) (@lem2259602 n)). Qed.
Lemma lem2259604 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2259607 (x : real) (n : nat) : (term71 x n) = (term72 x n).
Proof. exact (MK_COMB (@lem2259604 x) (@lem2259603 n)). Qed.
Lemma lem2259608 (x : real) (n : nat) : (term70 x n) = (term72 x n).
Proof. exact (TRANS (@lem2259560 x n) (@lem2259607 x n)). Qed.
Lemma lem2259609 (x : real) (n : nat) : (term69 x n) = (term72 x n).
Proof. exact (TRANS (@lem2259559 x n) (@lem2259608 x n)). Qed.
Lemma lem2259610 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2259611 (x : real) (n : nat) : (term73 x n) = (term74 x n).
Proof. exact (MK_COMB (@lem2259610) (@lem2259609 x n)). Qed.
Lemma lem2259612 (x : real) (n : nat) : (term74 x n) = (term75 x n).
Proof. exact (@lem1982785 (term72 x n)). Qed.
Lemma lem2259619 (x : real) (n : nat) : (term75 x n) = (term76 x n).
Proof. exact (@lem1982781 x term26 (real_of_num n)). Qed.
Lemma lem2259620 (x : real) (n : nat) : (term74 x n) = (term76 x n).
Proof. exact (TRANS (@lem2259612 x n) (@lem2259619 x n)). Qed.
Lemma lem2259621 (x : real) (n : nat) : (term77 x n) = (term77 x n).
Proof. exact (eq_refl (term77 x n)). Qed.
Lemma lem2259622 (x : real) (n : nat) : ((term73 x n) = (term74 x n)) = ((term73 x n) = (term76 x n)).
Proof. exact (MK_COMB (@lem2259621 x n) (@lem2259620 x n)). Qed.
Lemma lem2259623 (x : real) (n : nat) : (term73 x n) = (term76 x n).
Proof. exact (EQ_MP (@lem2259622 x n) (@lem2259611 x n)). Qed.
Lemma lem2259624 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2259625 (x : real) (n : nat) : (term78 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem2259624) (@lem2259623 x n)). Qed.
Lemma lem2259626 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259627 (x : real) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2259625 x n) (@lem2259626)). Qed.
Lemma lem2259628 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2259629 (x : real) (n : nat) : (term82 x n) = (term83 x n).
Proof. exact (MK_COMB (@lem2259628) (@lem2259609 x n)). Qed.
Lemma lem2259630 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259631 (x : real) (n : nat) : (term84 x n) = (term85 x n).
Proof. exact (MK_COMB (@lem2259629 x n) (@lem2259630)). Qed.
Lemma lem2259632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259633 (x : real) (n : nat) : (term86 x n) = (term87 x n).
Proof. exact (MK_COMB (@lem2259632) (@lem2259631 x n)). Qed.
Lemma lem2259634 (x : real) (n : nat) : (term68 x n) = (term88 x n).
Proof. exact (MK_COMB (@lem2259633 x n) (@lem2259627 x n)). Qed.
Lemma lem2259635 (x : real) (n : nat) : (term67 x n) = (term88 x n).
Proof. exact (TRANS (@lem2259548 x n) (@lem2259634 x n)). Qed.
Lemma lem2259636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2259637 (x : real) (n : nat) : (term89 x n) = (term90 x n).
Proof. exact (MK_COMB (@lem2259636) (@lem2259547 x n)). Qed.
Lemma lem2259638 (x : real) (n : nat) : (term1 x n) = (term91 x n).
Proof. exact (MK_COMB (@lem2259637 x n) (@lem2259635 x n)). Qed.
Lemma lem2259639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2259640 (x : real) (n : nat) : (term4 x n) = (term92 x n).
Proof. exact (MK_COMB (@lem2259639) (@lem2259465 x n)). Qed.
Lemma lem2259641 (x : real) (n : nat) : (term6 x n) = (term93 x n).
Proof. exact (MK_COMB (@lem2259640 x n) (@lem2259638 x n)). Qed.
Lemma lem2259642 (x : real) (n : nat) : (term94 x n) = (term95 x n).
Proof. exact (@lem1988318 (real_abs x) (real_of_num n)). Qed.
Lemma lem2259657 (x : real) (n : nat) : (term13 x n) = (term15 x n).
Proof. exact (@lem1982792 (real_abs x) (real_of_num n)). Qed.
Lemma lem2259658 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2259659 (x : real) (n : nat) : (term96 x n) = (term97 x n).
Proof. exact (MK_COMB (@lem2259658) (@lem2259657 x n)). Qed.
Lemma lem2259660 (x : real) (n : nat) : (term97 x n) = (term98 x n).
Proof. exact (@lem1982785 (term15 x n)). Qed.
Lemma lem2259661 (x : real) (n : nat) : (term98 x n) = (term99 x n).
Proof. exact (@lem1982781 (real_abs x) term26 (term27 n)). Qed.
Lemma lem2259662 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2259664 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259665 : term26 = term31.
Proof. exact (@lem2259664 term32). Qed.
Lemma lem2259667 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259668 : term26 = term31.
Proof. exact (@lem2259667 term32). Qed.
Lemma lem2259669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259670 : term33 = term34.
Proof. exact (MK_COMB (@lem2259669) (@lem2259668)). Qed.
Lemma lem2259671 : term35 = term36.
Proof. exact (MK_COMB (@lem2259670) (@lem2259665)). Qed.
Lemma lem2259672 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2259674 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2259675 : term41 = term42.
Proof. exact (@lem2259674 term32 term32). Qed.
Lemma lem2259676 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259677 : term44 = term32.
Proof. exact (EQ_MP (@lem2259676) (@lem940073)). Qed.
Lemma lem2259678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259679 : term42 = term38.
Proof. exact (MK_COMB (@lem2259678) (@lem2259677)). Qed.
Lemma lem2259680 : term41 = term38.
Proof. exact (TRANS (@lem2259675) (@lem2259679)). Qed.
Lemma lem2259682 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2259683 : term35 = term42.
Proof. exact (@lem2259682 term32 term32). Qed.
Lemma lem2259684 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259685 : term44 = term32.
Proof. exact (EQ_MP (@lem2259684) (@lem940073)). Qed.
Lemma lem2259686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259687 : term42 = term38.
Proof. exact (MK_COMB (@lem2259686) (@lem2259685)). Qed.
Lemma lem2259688 : term35 = term38.
Proof. exact (TRANS (@lem2259683) (@lem2259687)). Qed.
Lemma lem2259689 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2259690 : term46 = term47.
Proof. exact (MK_COMB (@lem2259689) (@lem2259688)). Qed.
Lemma lem2259691 : term37 = term48.
Proof. exact (MK_COMB (@lem2259690) (@lem2259680)). Qed.
Lemma lem2259692 : term36 = term48.
Proof. exact (TRANS (@lem2259672) (@lem2259691)). Qed.
Lemma lem2259693 : term35 = term48.
Proof. exact (TRANS (@lem2259671) (@lem2259692)). Qed.
Lemma lem2259695 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2259696 : term48 = term38.
Proof. exact (@lem2259695 term38). Qed.
Lemma lem2259697 : term35 = term38.
Proof. exact (TRANS (@lem2259693) (@lem2259696)). Qed.
Lemma lem2259698 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259699 : term50 = term51.
Proof. exact (MK_COMB (@lem2259698) (@lem2259697)). Qed.
Lemma lem2259700 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2259701 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2259699) (@lem2259700 n)). Qed.
Lemma lem2259702 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2259662 n) (@lem2259701 n)). Qed.
Lemma lem2259703 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2259704 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2259702 n) (@lem2259703 n)). Qed.
Lemma lem2259707 (x : real) : (term100 x) = (term100 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem2259708 (x : real) (n : nat) : (term99 x n) = (term101 x n).
Proof. exact (MK_COMB (@lem2259707 x) (@lem2259704 n)). Qed.
Lemma lem2259709 (x : real) (n : nat) : (term98 x n) = (term101 x n).
Proof. exact (TRANS (@lem2259661 x n) (@lem2259708 x n)). Qed.
Lemma lem2259710 (x : real) (n : nat) : (term97 x n) = (term101 x n).
Proof. exact (TRANS (@lem2259660 x n) (@lem2259709 x n)). Qed.
Lemma lem2259711 (x : real) (n : nat) : (term102 x n) = (term102 x n).
Proof. exact (eq_refl (term102 x n)). Qed.
Lemma lem2259712 (x : real) (n : nat) : ((term96 x n) = (term97 x n)) = ((term96 x n) = (term101 x n)).
Proof. exact (MK_COMB (@lem2259711 x n) (@lem2259710 x n)). Qed.
Lemma lem2259713 (x : real) (n : nat) : (term96 x n) = (term101 x n).
Proof. exact (EQ_MP (@lem2259712 x n) (@lem2259659 x n)). Qed.
Lemma lem2259714 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2259715 (x : real) (n : nat) : (term103 x n) = (term104 x n).
Proof. exact (MK_COMB (@lem2259714) (@lem2259713 x n)). Qed.
Lemma lem2259716 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259717 (x : real) (n : nat) : (term105 x n) = (term106 x n).
Proof. exact (MK_COMB (@lem2259715 x n) (@lem2259716)). Qed.
Lemma lem2259718 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2259719 (x : real) (n : nat) : (term107 x n) = (term108 x n).
Proof. exact (MK_COMB (@lem2259718) (@lem2259657 x n)). Qed.
Lemma lem2259720 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259721 (x : real) (n : nat) : (term109 x n) = (term110 x n).
Proof. exact (MK_COMB (@lem2259719 x n) (@lem2259720)). Qed.
Lemma lem2259722 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259723 (x : real) (n : nat) : (term111 x n) = (term112 x n).
Proof. exact (MK_COMB (@lem2259722) (@lem2259721 x n)). Qed.
Lemma lem2259724 (x : real) (n : nat) : (term95 x n) = (term113 x n).
Proof. exact (MK_COMB (@lem2259723 x n) (@lem2259717 x n)). Qed.
Lemma lem2259725 (x : real) (n : nat) : (term94 x n) = (term113 x n).
Proof. exact (TRANS (@lem2259642 x n) (@lem2259724 x n)). Qed.
Lemma lem2259726 (x : real) (n : nat) : (x = (real_of_num n)) = ((term20 x n) = term14).
Proof. exact (@lem1988293 x (real_of_num n)). Qed.
Lemma lem2259739 (x : real) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (@lem1982792 x (real_of_num n)). Qed.
Lemma lem2259740 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2259741 (x : real) (n : nat) : (term114 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2259740) (@lem2259739 x n)). Qed.
Lemma lem2259742 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259743 (x : real) (n : nat) : ((term20 x n) = term14) = ((term21 x n) = term14).
Proof. exact (MK_COMB (@lem2259741 x n) (@lem2259742)). Qed.
Lemma lem2259744 (x : real) (n : nat) : (x = (real_of_num n)) = ((term21 x n) = term14).
Proof. exact (TRANS (@lem2259726 x n) (@lem2259743 x n)). Qed.
Lemma lem2259745 (x : real) (n : nat) : (x = (term2 n)) = ((term69 x n) = term14).
Proof. exact (@lem1988293 x (term2 n)). Qed.
Lemma lem2259752 (n : nat) : (term2 n) = (term27 n).
Proof. exact (@lem1982785 (real_of_num n)). Qed.
Lemma lem2259755 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem2259756 (x : real) (n : nat) : (term69 x n) = (term70 x n).
Proof. exact (MK_COMB (@lem2259755 x) (@lem2259752 n)). Qed.
Lemma lem2259757 (x : real) (n : nat) : (term70 x n) = (term71 x n).
Proof. exact (@lem1982792 x (term27 n)). Qed.
Lemma lem2259758 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2259760 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259761 : term26 = term31.
Proof. exact (@lem2259760 term32). Qed.
Lemma lem2259763 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259764 : term26 = term31.
Proof. exact (@lem2259763 term32). Qed.
Lemma lem2259765 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259766 : term33 = term34.
Proof. exact (MK_COMB (@lem2259765) (@lem2259764)). Qed.
Lemma lem2259767 : term35 = term36.
Proof. exact (MK_COMB (@lem2259766) (@lem2259761)). Qed.
Lemma lem2259768 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2259770 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2259771 : term41 = term42.
Proof. exact (@lem2259770 term32 term32). Qed.
Lemma lem2259772 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259773 : term44 = term32.
Proof. exact (EQ_MP (@lem2259772) (@lem940073)). Qed.
Lemma lem2259774 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259775 : term42 = term38.
Proof. exact (MK_COMB (@lem2259774) (@lem2259773)). Qed.
Lemma lem2259776 : term41 = term38.
Proof. exact (TRANS (@lem2259771) (@lem2259775)). Qed.
Lemma lem2259778 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2259779 : term35 = term42.
Proof. exact (@lem2259778 term32 term32). Qed.
Lemma lem2259780 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259781 : term44 = term32.
Proof. exact (EQ_MP (@lem2259780) (@lem940073)). Qed.
Lemma lem2259782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259783 : term42 = term38.
Proof. exact (MK_COMB (@lem2259782) (@lem2259781)). Qed.
Lemma lem2259784 : term35 = term38.
Proof. exact (TRANS (@lem2259779) (@lem2259783)). Qed.
Lemma lem2259785 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2259786 : term46 = term47.
Proof. exact (MK_COMB (@lem2259785) (@lem2259784)). Qed.
Lemma lem2259787 : term37 = term48.
Proof. exact (MK_COMB (@lem2259786) (@lem2259776)). Qed.
Lemma lem2259788 : term36 = term48.
Proof. exact (TRANS (@lem2259768) (@lem2259787)). Qed.
Lemma lem2259789 : term35 = term48.
Proof. exact (TRANS (@lem2259767) (@lem2259788)). Qed.
Lemma lem2259791 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2259792 : term48 = term38.
Proof. exact (@lem2259791 term38). Qed.
Lemma lem2259793 : term35 = term38.
Proof. exact (TRANS (@lem2259789) (@lem2259792)). Qed.
Lemma lem2259794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259795 : term50 = term51.
Proof. exact (MK_COMB (@lem2259794) (@lem2259793)). Qed.
Lemma lem2259796 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2259797 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2259795) (@lem2259796 n)). Qed.
Lemma lem2259798 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2259758 n) (@lem2259797 n)). Qed.
Lemma lem2259799 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2259800 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2259798 n) (@lem2259799 n)). Qed.
Lemma lem2259801 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2259804 (x : real) (n : nat) : (term71 x n) = (term72 x n).
Proof. exact (MK_COMB (@lem2259801 x) (@lem2259800 n)). Qed.
Lemma lem2259805 (x : real) (n : nat) : (term70 x n) = (term72 x n).
Proof. exact (TRANS (@lem2259757 x n) (@lem2259804 x n)). Qed.
Lemma lem2259806 (x : real) (n : nat) : (term69 x n) = (term72 x n).
Proof. exact (TRANS (@lem2259756 x n) (@lem2259805 x n)). Qed.
Lemma lem2259807 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2259808 (x : real) (n : nat) : (term116 x n) = (term117 x n).
Proof. exact (MK_COMB (@lem2259807) (@lem2259806 x n)). Qed.
Lemma lem2259809 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259810 (x : real) (n : nat) : ((term69 x n) = term14) = ((term72 x n) = term14).
Proof. exact (MK_COMB (@lem2259808 x n) (@lem2259809)). Qed.
Lemma lem2259811 (x : real) (n : nat) : (x = (term2 n)) = ((term72 x n) = term14).
Proof. exact (TRANS (@lem2259745 x n) (@lem2259810 x n)). Qed.
Lemma lem2259812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259813 (x : real) (n : nat) : (term118 x n) = (term119 x n).
Proof. exact (MK_COMB (@lem2259812) (@lem2259744 x n)). Qed.
Lemma lem2259814 (x : real) (n : nat) : (term12 x n) = (term120 x n).
Proof. exact (MK_COMB (@lem2259813 x n) (@lem2259811 x n)). Qed.
Lemma lem2259815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2259816 (x : real) (n : nat) : (term121 x n) = (term122 x n).
Proof. exact (MK_COMB (@lem2259815) (@lem2259725 x n)). Qed.
Lemma lem2259817 (x : real) (n : nat) : (term3 x n) = (term123 x n).
Proof. exact (MK_COMB (@lem2259816 x n) (@lem2259814 x n)). Qed.
Lemma lem2259818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259819 (x : real) (n : nat) : (term8 x n) = (term124 x n).
Proof. exact (MK_COMB (@lem2259818) (@lem2259641 x n)). Qed.
Lemma lem2259820 (x : real) (n : nat) : (term10 x n) = (term125 x n).
Proof. exact (MK_COMB (@lem2259819 x n) (@lem2259817 x n)). Qed.
Lemma lem2259827 (x : real) (n : nat) : (term11 x n) = (term125 x n).
Proof. exact (TRANS (@lem2259444 x n) (@lem2259820 x n)). Qed.
Lemma lem2259841 (x : real) (n : nat) : (term123 x n) = (term126 x n).
Proof. exact (@lem19158 ((term21 x n) = term14) (term113 x n) ((term72 x n) = term14)). Qed.
Lemma lem2259848 (x : real) (n : nat) : (term127 x n) = (term128 x n).
Proof. exact (@lem19367 (term110 x n) (term106 x n) ((term72 x n) = term14)). Qed.
Lemma lem2259855 (x : real) (n : nat) : (term129 x n) = (term130 x n).
Proof. exact (@lem19367 (term110 x n) (term106 x n) ((term21 x n) = term14)). Qed.
Lemma lem2259856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259857 (x : real) (n : nat) : (term131 x n) = (term132 x n).
Proof. exact (MK_COMB (@lem2259856) (@lem2259855 x n)). Qed.
Lemma lem2259858 (x : real) (n : nat) : (term126 x n) = (term133 x n).
Proof. exact (MK_COMB (@lem2259857 x n) (@lem2259848 x n)). Qed.
Lemma lem2259860 (x : real) (n : nat) : (term123 x n) = (term133 x n).
Proof. exact (TRANS (@lem2259841 x n) (@lem2259858 x n)). Qed.
Lemma lem2259874 (x : real) (n : nat) : (term91 x n) = (term134 x n).
Proof. exact (@lem19158 (term85 x n) (term66 x n) (term81 x n)). Qed.
Lemma lem2259881 (x : real) (n : nat) : (term135 x n) = (term136 x n).
Proof. exact (@lem19367 (term63 x n) (term59 x n) (term81 x n)). Qed.
Lemma lem2259888 (x : real) (n : nat) : (term137 x n) = (term138 x n).
Proof. exact (@lem19367 (term63 x n) (term59 x n) (term85 x n)). Qed.
Lemma lem2259889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259890 (x : real) (n : nat) : (term139 x n) = (term140 x n).
Proof. exact (MK_COMB (@lem2259889) (@lem2259888 x n)). Qed.
Lemma lem2259891 (x : real) (n : nat) : (term134 x n) = (term141 x n).
Proof. exact (MK_COMB (@lem2259890 x n) (@lem2259881 x n)). Qed.
Lemma lem2259893 (x : real) (n : nat) : (term91 x n) = (term141 x n).
Proof. exact (TRANS (@lem2259874 x n) (@lem2259891 x n)). Qed.
Lemma lem2259896 (x : real) (n : nat) : (term92 x n) = (term92 x n).
Proof. exact (eq_refl (term92 x n)). Qed.
Lemma lem2259897 (x : real) (n : nat) : (term93 x n) = (term142 x n).
Proof. exact (MK_COMB (@lem2259896 x n) (@lem2259893 x n)). Qed.
Lemma lem2259898 (x : real) (n : nat) : (term142 x n) = (term143 x n).
Proof. exact (@lem19158 (term138 x n) ((term15 x n) = term14) (term136 x n)). Qed.
Lemma lem2259905 (x : real) (n : nat) : (term144 x n) = (term145 x n).
Proof. exact (@lem19158 (term146 x n) ((term15 x n) = term14) (term147 x n)). Qed.
Lemma lem2259912 (x : real) (n : nat) : (term148 x n) = (term149 x n).
Proof. exact (@lem19158 (term150 x n) ((term15 x n) = term14) (term151 x n)). Qed.
Lemma lem2259913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259914 (x : real) (n : nat) : (term152 x n) = (term153 x n).
Proof. exact (MK_COMB (@lem2259913) (@lem2259912 x n)). Qed.
Lemma lem2259915 (x : real) (n : nat) : (term143 x n) = (term154 x n).
Proof. exact (MK_COMB (@lem2259914 x n) (@lem2259905 x n)). Qed.
Lemma lem2259916 (x : real) (n : nat) : (term142 x n) = (term154 x n).
Proof. exact (TRANS (@lem2259898 x n) (@lem2259915 x n)). Qed.
Lemma lem2259917 (x : real) (n : nat) : (term93 x n) = (term154 x n).
Proof. exact (TRANS (@lem2259897 x n) (@lem2259916 x n)). Qed.
Lemma lem2259918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259919 (x : real) (n : nat) : (term124 x n) = (term155 x n).
Proof. exact (MK_COMB (@lem2259918) (@lem2259917 x n)). Qed.
Lemma lem2259920 (x : real) (n : nat) : (term125 x n) = (term156 x n).
Proof. exact (MK_COMB (@lem2259919 x n) (@lem2259860 x n)). Qed.
Lemma lem2259921 (x : real) (n : nat) : (term11 x n) = (term156 x n).
Proof. exact (TRANS (@lem2259827 x n) (@lem2259920 x n)). Qed.
Lemma lem2259923 (x : real) (n : nat) : (term157 n x) = (term158 x n).
Proof. exact (eq_refl (term157 n x)). Qed.
Lemma lem2259924 (n : nat) (x : real) : (term158 x n) = (term157 n x).
Proof. exact (SYM (@lem2259923 x n)). Qed.
Lemma lem2259925 (n : nat) (x : real) : (term157 n x) = (term159 n x).
Proof. exact (@lem1482981 (term160 x n) x). Qed.
Lemma lem2259926 (n : nat) (x : real) : (term158 x n) = (term159 n x).
Proof. exact (TRANS (@lem2259924 n x) (@lem2259925 n x)). Qed.
Lemma lem2259927 (x : real) (n : nat) : (term161 n x) = (term162 x n).
Proof. exact (eq_refl (term161 n x)). Qed.
Lemma lem2259928 (x : real) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem2259929 (x : real) (n : nat) : (term164 n x) = (term165 x n).
Proof. exact (MK_COMB (@lem2259928 x) (@lem2259927 x n)). Qed.
Lemma lem2259930 (x : real) (n : nat) : (term166 n x) = (term167 x n).
Proof. exact (eq_refl (term166 n x)). Qed.
Lemma lem2259931 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem2259932 (x : real) (n : nat) : (term169 n x) = (term170 x n).
Proof. exact (MK_COMB (@lem2259931 x) (@lem2259930 x n)). Qed.
Lemma lem2259933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2259934 (x : real) (n : nat) : (term171 n x) = (term172 x n).
Proof. exact (MK_COMB (@lem2259933) (@lem2259932 x n)). Qed.
Lemma lem2259935 (x : real) (n : nat) : (term159 n x) = (term173 x n).
Proof. exact (MK_COMB (@lem2259934 x n) (@lem2259929 x n)). Qed.
Lemma lem2259936 (x : real) (n : nat) : (term174 x n) = (term174 x n).
Proof. exact (eq_refl (term174 x n)). Qed.
Lemma lem2259937 (x : real) (n : nat) : ((term158 x n) = (term159 n x)) = ((term158 x n) = (term173 x n)).
Proof. exact (MK_COMB (@lem2259936 x n) (@lem2259935 x n)). Qed.
Lemma lem2259938 (x : real) (n : nat) : (term158 x n) = (term173 x n).
Proof. exact (EQ_MP (@lem2259937 x n) (@lem2259926 n x)). Qed.
Lemma lem2259939 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1988291 x term14). Qed.
Lemma lem2259945 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1982792 x term14). Qed.
Lemma lem2259947 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2259948 : term14 = term180.
Proof. exact (@lem2259947 (NUMERAL 0)). Qed.
Lemma lem2259950 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2259951 : term26 = term31.
Proof. exact (@lem2259950 term32). Qed.
Lemma lem2259952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2259953 : term33 = term34.
Proof. exact (MK_COMB (@lem2259952) (@lem2259951)). Qed.
Lemma lem2259954 : term181 = term182.
Proof. exact (MK_COMB (@lem2259953) (@lem2259948)). Qed.
Lemma lem2259955 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2259957 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2259958 : term41 = term42.
Proof. exact (@lem2259957 term32 term32). Qed.
Lemma lem2259959 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2259960 : term44 = term32.
Proof. exact (EQ_MP (@lem2259959) (@lem940073)). Qed.
Lemma lem2259961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2259962 : term42 = term38.
Proof. exact (MK_COMB (@lem2259961) (@lem2259960)). Qed.
Lemma lem2259963 : term41 = term38.
Proof. exact (TRANS (@lem2259958) (@lem2259962)). Qed.
Lemma lem2259965 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2259966 : term181 = term14.
Proof. exact (@lem2259965 term32). Qed.
Lemma lem2259967 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2259968 : term185 = term186.
Proof. exact (MK_COMB (@lem2259967) (@lem2259966)). Qed.
Lemma lem2259969 : term183 = term180.
Proof. exact (MK_COMB (@lem2259968) (@lem2259963)). Qed.
Lemma lem2259970 : term182 = term180.
Proof. exact (TRANS (@lem2259955) (@lem2259969)). Qed.
Lemma lem2259971 : term181 = term180.
Proof. exact (TRANS (@lem2259954) (@lem2259970)). Qed.
Lemma lem2259973 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2259974 : term180 = term14.
Proof. exact (@lem2259973 term14). Qed.
Lemma lem2259975 : term181 = term14.
Proof. exact (TRANS (@lem2259971) (@lem2259974)). Qed.
Lemma lem2259976 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2259977 (x : real) : (term178 x) = (term187 x).
Proof. exact (MK_COMB (@lem2259976 x) (@lem2259975)). Qed.
Lemma lem2259978 (x : real) : (term187 x) = x.
Proof. exact (@lem1982723 x). Qed.
Lemma lem2259979 (x : real) : (term178 x) = x.
Proof. exact (TRANS (@lem2259977 x) (@lem2259978 x)). Qed.
Lemma lem2259981 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem2259945 x) (@lem2259979 x)). Qed.
Lemma lem2259982 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2259983 (x : real) : (term188 x) = (real_ge x).
Proof. exact (MK_COMB (@lem2259982) (@lem2259981 x)). Qed.
Lemma lem2259984 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2259985 (x : real) : (term176 x) = (term175 x).
Proof. exact (MK_COMB (@lem2259983 x) (@lem2259984)). Qed.
Lemma lem2259986 (x : real) : (term175 x) = (term175 x).
Proof. exact (TRANS (@lem2259939 x) (@lem2259985 x)). Qed.
Lemma lem2259987 (x : real) (n : nat) : ((term21 x n) = term14) = ((term189 x n) = term14).
Proof. exact (@lem1988293 (term21 x n) term14). Qed.
Lemma lem2260005 (x : real) (n : nat) : (term189 x n) = (term190 x n).
Proof. exact (@lem1982792 (term21 x n) term14). Qed.
Lemma lem2260007 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260008 : term14 = term180.
Proof. exact (@lem2260007 (NUMERAL 0)). Qed.
Lemma lem2260010 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260011 : term26 = term31.
Proof. exact (@lem2260010 term32). Qed.
Lemma lem2260012 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260013 : term33 = term34.
Proof. exact (MK_COMB (@lem2260012) (@lem2260011)). Qed.
Lemma lem2260014 : term181 = term182.
Proof. exact (MK_COMB (@lem2260013) (@lem2260008)). Qed.
Lemma lem2260015 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2260017 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260018 : term41 = term42.
Proof. exact (@lem2260017 term32 term32). Qed.
Lemma lem2260019 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260020 : term44 = term32.
Proof. exact (EQ_MP (@lem2260019) (@lem940073)). Qed.
Lemma lem2260021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260022 : term42 = term38.
Proof. exact (MK_COMB (@lem2260021) (@lem2260020)). Qed.
Lemma lem2260023 : term41 = term38.
Proof. exact (TRANS (@lem2260018) (@lem2260022)). Qed.
Lemma lem2260025 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2260026 : term181 = term14.
Proof. exact (@lem2260025 term32). Qed.
Lemma lem2260027 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2260028 : term185 = term186.
Proof. exact (MK_COMB (@lem2260027) (@lem2260026)). Qed.
Lemma lem2260029 : term183 = term180.
Proof. exact (MK_COMB (@lem2260028) (@lem2260023)). Qed.
Lemma lem2260030 : term182 = term180.
Proof. exact (TRANS (@lem2260015) (@lem2260029)). Qed.
Lemma lem2260031 : term181 = term180.
Proof. exact (TRANS (@lem2260014) (@lem2260030)). Qed.
Lemma lem2260033 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2260034 : term180 = term14.
Proof. exact (@lem2260033 term14). Qed.
Lemma lem2260035 : term181 = term14.
Proof. exact (TRANS (@lem2260031) (@lem2260034)). Qed.
Lemma lem2260036 (x : real) (n : nat) : (term191 x n) = (term191 x n).
Proof. exact (eq_refl (term191 x n)). Qed.
Lemma lem2260037 (x : real) (n : nat) : (term190 x n) = (term192 x n).
Proof. exact (MK_COMB (@lem2260036 x n) (@lem2260035)). Qed.
Lemma lem2260038 (x : real) (n : nat) : (term192 x n) = (term21 x n).
Proof. exact (@lem1982723 (term21 x n)). Qed.
Lemma lem2260039 (x : real) (n : nat) : (term190 x n) = (term21 x n).
Proof. exact (TRANS (@lem2260037 x n) (@lem2260038 x n)). Qed.
Lemma lem2260041 (x : real) (n : nat) : (term189 x n) = (term21 x n).
Proof. exact (TRANS (@lem2260005 x n) (@lem2260039 x n)). Qed.
Lemma lem2260042 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2260043 (x : real) (n : nat) : (term193 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2260042) (@lem2260041 x n)). Qed.
Lemma lem2260044 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260045 (x : real) (n : nat) : ((term189 x n) = term14) = ((term21 x n) = term14).
Proof. exact (MK_COMB (@lem2260043 x n) (@lem2260044)). Qed.
Lemma lem2260046 (x : real) (n : nat) : ((term21 x n) = term14) = ((term21 x n) = term14).
Proof. exact (TRANS (@lem2259987 x n) (@lem2260045 x n)). Qed.
Lemma lem2260047 (x : real) (n : nat) : (term63 x n) = (term194 x n).
Proof. exact (@lem1988289 (term21 x n) term14). Qed.
Lemma lem2260065 (x : real) (n : nat) : (term189 x n) = (term190 x n).
Proof. exact (@lem1982792 (term21 x n) term14). Qed.
Lemma lem2260067 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260068 : term14 = term180.
Proof. exact (@lem2260067 (NUMERAL 0)). Qed.
Lemma lem2260070 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260071 : term26 = term31.
Proof. exact (@lem2260070 term32). Qed.
Lemma lem2260072 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260073 : term33 = term34.
Proof. exact (MK_COMB (@lem2260072) (@lem2260071)). Qed.
Lemma lem2260074 : term181 = term182.
Proof. exact (MK_COMB (@lem2260073) (@lem2260068)). Qed.
Lemma lem2260075 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2260077 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260078 : term41 = term42.
Proof. exact (@lem2260077 term32 term32). Qed.
Lemma lem2260079 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260080 : term44 = term32.
Proof. exact (EQ_MP (@lem2260079) (@lem940073)). Qed.
Lemma lem2260081 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260082 : term42 = term38.
Proof. exact (MK_COMB (@lem2260081) (@lem2260080)). Qed.
Lemma lem2260083 : term41 = term38.
Proof. exact (TRANS (@lem2260078) (@lem2260082)). Qed.
Lemma lem2260085 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2260086 : term181 = term14.
Proof. exact (@lem2260085 term32). Qed.
Lemma lem2260087 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2260088 : term185 = term186.
Proof. exact (MK_COMB (@lem2260087) (@lem2260086)). Qed.
Lemma lem2260089 : term183 = term180.
Proof. exact (MK_COMB (@lem2260088) (@lem2260083)). Qed.
Lemma lem2260090 : term182 = term180.
Proof. exact (TRANS (@lem2260075) (@lem2260089)). Qed.
Lemma lem2260091 : term181 = term180.
Proof. exact (TRANS (@lem2260074) (@lem2260090)). Qed.
Lemma lem2260093 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2260094 : term180 = term14.
Proof. exact (@lem2260093 term14). Qed.
Lemma lem2260095 : term181 = term14.
Proof. exact (TRANS (@lem2260091) (@lem2260094)). Qed.
Lemma lem2260096 (x : real) (n : nat) : (term191 x n) = (term191 x n).
Proof. exact (eq_refl (term191 x n)). Qed.
Lemma lem2260097 (x : real) (n : nat) : (term190 x n) = (term192 x n).
Proof. exact (MK_COMB (@lem2260096 x n) (@lem2260095)). Qed.
Lemma lem2260098 (x : real) (n : nat) : (term192 x n) = (term21 x n).
Proof. exact (@lem1982723 (term21 x n)). Qed.
Lemma lem2260099 (x : real) (n : nat) : (term190 x n) = (term21 x n).
Proof. exact (TRANS (@lem2260097 x n) (@lem2260098 x n)). Qed.
Lemma lem2260101 (x : real) (n : nat) : (term189 x n) = (term21 x n).
Proof. exact (TRANS (@lem2260065 x n) (@lem2260099 x n)). Qed.
Lemma lem2260102 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260103 (x : real) (n : nat) : (term195 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem2260102) (@lem2260101 x n)). Qed.
Lemma lem2260104 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260105 (x : real) (n : nat) : (term194 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem2260103 x n) (@lem2260104)). Qed.
Lemma lem2260106 (x : real) (n : nat) : (term63 x n) = (term63 x n).
Proof. exact (TRANS (@lem2260047 x n) (@lem2260105 x n)). Qed.
Lemma lem2260107 (x : real) (n : nat) : (term85 x n) = (term196 x n).
Proof. exact (@lem1988289 (term72 x n) term14). Qed.
Lemma lem2260119 (x : real) (n : nat) : (term197 x n) = (term198 x n).
Proof. exact (@lem1982792 (term72 x n) term14). Qed.
Lemma lem2260121 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260122 : term14 = term180.
Proof. exact (@lem2260121 (NUMERAL 0)). Qed.
Lemma lem2260124 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260125 : term26 = term31.
Proof. exact (@lem2260124 term32). Qed.
Lemma lem2260126 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260127 : term33 = term34.
Proof. exact (MK_COMB (@lem2260126) (@lem2260125)). Qed.
Lemma lem2260128 : term181 = term182.
Proof. exact (MK_COMB (@lem2260127) (@lem2260122)). Qed.
Lemma lem2260129 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2260131 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260132 : term41 = term42.
Proof. exact (@lem2260131 term32 term32). Qed.
Lemma lem2260133 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260134 : term44 = term32.
Proof. exact (EQ_MP (@lem2260133) (@lem940073)). Qed.
Lemma lem2260135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260136 : term42 = term38.
Proof. exact (MK_COMB (@lem2260135) (@lem2260134)). Qed.
Lemma lem2260137 : term41 = term38.
Proof. exact (TRANS (@lem2260132) (@lem2260136)). Qed.
Lemma lem2260139 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2260140 : term181 = term14.
Proof. exact (@lem2260139 term32). Qed.
Lemma lem2260141 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2260142 : term185 = term186.
Proof. exact (MK_COMB (@lem2260141) (@lem2260140)). Qed.
Lemma lem2260143 : term183 = term180.
Proof. exact (MK_COMB (@lem2260142) (@lem2260137)). Qed.
Lemma lem2260144 : term182 = term180.
Proof. exact (TRANS (@lem2260129) (@lem2260143)). Qed.
Lemma lem2260145 : term181 = term180.
Proof. exact (TRANS (@lem2260128) (@lem2260144)). Qed.
Lemma lem2260147 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2260148 : term180 = term14.
Proof. exact (@lem2260147 term14). Qed.
Lemma lem2260149 : term181 = term14.
Proof. exact (TRANS (@lem2260145) (@lem2260148)). Qed.
Lemma lem2260150 (x : real) (n : nat) : (term199 x n) = (term199 x n).
Proof. exact (eq_refl (term199 x n)). Qed.
Lemma lem2260151 (x : real) (n : nat) : (term198 x n) = (term200 x n).
Proof. exact (MK_COMB (@lem2260150 x n) (@lem2260149)). Qed.
Lemma lem2260152 (x : real) (n : nat) : (term200 x n) = (term72 x n).
Proof. exact (@lem1982723 (term72 x n)). Qed.
Lemma lem2260153 (x : real) (n : nat) : (term198 x n) = (term72 x n).
Proof. exact (TRANS (@lem2260151 x n) (@lem2260152 x n)). Qed.
Lemma lem2260155 (x : real) (n : nat) : (term197 x n) = (term72 x n).
Proof. exact (TRANS (@lem2260119 x n) (@lem2260153 x n)). Qed.
Lemma lem2260156 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260157 (x : real) (n : nat) : (term201 x n) = (term83 x n).
Proof. exact (MK_COMB (@lem2260156) (@lem2260155 x n)). Qed.
Lemma lem2260158 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260159 (x : real) (n : nat) : (term196 x n) = (term85 x n).
Proof. exact (MK_COMB (@lem2260157 x n) (@lem2260158)). Qed.
Lemma lem2260160 (x : real) (n : nat) : (term85 x n) = (term85 x n).
Proof. exact (TRANS (@lem2260107 x n) (@lem2260159 x n)). Qed.
Lemma lem2260161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260162 (x : real) (n : nat) : (term202 x n) = (term202 x n).
Proof. exact (MK_COMB (@lem2260161) (@lem2260106 x n)). Qed.
Lemma lem2260163 (x : real) (n : nat) : (term150 x n) = (term150 x n).
Proof. exact (MK_COMB (@lem2260162 x n) (@lem2260160 x n)). Qed.
Lemma lem2260164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260165 (x : real) (n : nat) : (term203 x n) = (term203 x n).
Proof. exact (MK_COMB (@lem2260164) (@lem2260046 x n)). Qed.
Lemma lem2260166 (x : real) (n : nat) : (term167 x n) = (term167 x n).
Proof. exact (MK_COMB (@lem2260165 x n) (@lem2260163 x n)). Qed.
Lemma lem2260167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260168 (x : real) : (term168 x) = (term168 x).
Proof. exact (MK_COMB (@lem2260167) (@lem2259986 x)). Qed.
Lemma lem2260169 (x : real) (n : nat) : (term170 x n) = (term170 x n).
Proof. exact (MK_COMB (@lem2260168 x) (@lem2260166 x n)). Qed.
Lemma lem2260170 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1988289 term14 x). Qed.
Lemma lem2260176 (x : real) : (term206 x) = (term207 x).
Proof. exact (@lem1982792 term14 x). Qed.
Lemma lem2260181 (x : real) : (term207 x) = (term208 x).
Proof. exact (@lem1982721 (term208 x)). Qed.
Lemma lem2260183 (x : real) : (term206 x) = (term208 x).
Proof. exact (TRANS (@lem2260176 x) (@lem2260181 x)). Qed.
Lemma lem2260184 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260185 (x : real) : (term209 x) = (term210 x).
Proof. exact (MK_COMB (@lem2260184) (@lem2260183 x)). Qed.
Lemma lem2260186 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260187 (x : real) : (term205 x) = (term211 x).
Proof. exact (MK_COMB (@lem2260185 x) (@lem2260186)). Qed.
Lemma lem2260188 (x : real) : (term204 x) = (term211 x).
Proof. exact (TRANS (@lem2260170 x) (@lem2260187 x)). Qed.
Lemma lem2260189 (x : real) (n : nat) : ((term212 x n) = term14) = ((term213 x n) = term14).
Proof. exact (@lem1988293 (term212 x n) term14). Qed.
Lemma lem2260190 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260197 (n : nat) : (term27 n) = (term27 n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem2260204 (x : real) : (real_neg x) = (term208 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem2260205 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2260206 (x : real) : (term214 x) = (term53 x).
Proof. exact (MK_COMB (@lem2260205) (@lem2260204 x)). Qed.
Lemma lem2260209 (x : real) (n : nat) : (term212 x n) = (term76 x n).
Proof. exact (MK_COMB (@lem2260206 x) (@lem2260197 n)). Qed.
Lemma lem2260210 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2260211 (x : real) (n : nat) : (term215 x n) = (term216 x n).
Proof. exact (MK_COMB (@lem2260210) (@lem2260209 x n)). Qed.
Lemma lem2260212 (x : real) (n : nat) : (term213 x n) = (term217 x n).
Proof. exact (MK_COMB (@lem2260211 x n) (@lem2260190)). Qed.
Lemma lem2260213 (x : real) (n : nat) : (term217 x n) = (term218 x n).
Proof. exact (@lem1982792 (term76 x n) term14). Qed.
Lemma lem2260215 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260216 : term14 = term180.
Proof. exact (@lem2260215 (NUMERAL 0)). Qed.
Lemma lem2260218 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260219 : term26 = term31.
Proof. exact (@lem2260218 term32). Qed.
Lemma lem2260220 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260221 : term33 = term34.
Proof. exact (MK_COMB (@lem2260220) (@lem2260219)). Qed.
Lemma lem2260222 : term181 = term182.
Proof. exact (MK_COMB (@lem2260221) (@lem2260216)). Qed.
Lemma lem2260223 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2260225 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260226 : term41 = term42.
Proof. exact (@lem2260225 term32 term32). Qed.
Lemma lem2260227 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260228 : term44 = term32.
Proof. exact (EQ_MP (@lem2260227) (@lem940073)). Qed.
Lemma lem2260229 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260230 : term42 = term38.
Proof. exact (MK_COMB (@lem2260229) (@lem2260228)). Qed.
Lemma lem2260231 : term41 = term38.
Proof. exact (TRANS (@lem2260226) (@lem2260230)). Qed.
Lemma lem2260233 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2260234 : term181 = term14.
Proof. exact (@lem2260233 term32). Qed.
Lemma lem2260235 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2260236 : term185 = term186.
Proof. exact (MK_COMB (@lem2260235) (@lem2260234)). Qed.
Lemma lem2260237 : term183 = term180.
Proof. exact (MK_COMB (@lem2260236) (@lem2260231)). Qed.
Lemma lem2260238 : term182 = term180.
Proof. exact (TRANS (@lem2260223) (@lem2260237)). Qed.
Lemma lem2260239 : term181 = term180.
Proof. exact (TRANS (@lem2260222) (@lem2260238)). Qed.
Lemma lem2260241 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2260242 : term180 = term14.
Proof. exact (@lem2260241 term14). Qed.
Lemma lem2260243 : term181 = term14.
Proof. exact (TRANS (@lem2260239) (@lem2260242)). Qed.
Lemma lem2260244 (x : real) (n : nat) : (term219 x n) = (term219 x n).
Proof. exact (eq_refl (term219 x n)). Qed.
Lemma lem2260245 (x : real) (n : nat) : (term218 x n) = (term220 x n).
Proof. exact (MK_COMB (@lem2260244 x n) (@lem2260243)). Qed.
Lemma lem2260246 (x : real) (n : nat) : (term220 x n) = (term76 x n).
Proof. exact (@lem1982723 (term76 x n)). Qed.
Lemma lem2260247 (x : real) (n : nat) : (term218 x n) = (term76 x n).
Proof. exact (TRANS (@lem2260245 x n) (@lem2260246 x n)). Qed.
Lemma lem2260248 (x : real) (n : nat) : (term217 x n) = (term76 x n).
Proof. exact (TRANS (@lem2260213 x n) (@lem2260247 x n)). Qed.
Lemma lem2260249 (x : real) (n : nat) : (term213 x n) = (term76 x n).
Proof. exact (TRANS (@lem2260212 x n) (@lem2260248 x n)). Qed.
Lemma lem2260250 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2260251 (x : real) (n : nat) : (term221 x n) = (term222 x n).
Proof. exact (MK_COMB (@lem2260250) (@lem2260249 x n)). Qed.
Lemma lem2260252 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260253 (x : real) (n : nat) : ((term213 x n) = term14) = ((term76 x n) = term14).
Proof. exact (MK_COMB (@lem2260251 x n) (@lem2260252)). Qed.
Lemma lem2260254 (x : real) (n : nat) : ((term212 x n) = term14) = ((term76 x n) = term14).
Proof. exact (TRANS (@lem2260189 x n) (@lem2260253 x n)). Qed.
Lemma lem2260255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260256 (x : real) (n : nat) : (term202 x n) = (term202 x n).
Proof. exact (MK_COMB (@lem2260255) (@lem2260106 x n)). Qed.
Lemma lem2260257 (x : real) (n : nat) : (term150 x n) = (term150 x n).
Proof. exact (MK_COMB (@lem2260256 x n) (@lem2260160 x n)). Qed.
Lemma lem2260258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260259 (x : real) (n : nat) : (term223 x n) = (term224 x n).
Proof. exact (MK_COMB (@lem2260258) (@lem2260254 x n)). Qed.
Lemma lem2260260 (x : real) (n : nat) : (term162 x n) = (term225 x n).
Proof. exact (MK_COMB (@lem2260259 x n) (@lem2260257 x n)). Qed.
Lemma lem2260261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260262 (x : real) : (term163 x) = (term226 x).
Proof. exact (MK_COMB (@lem2260261) (@lem2260188 x)). Qed.
Lemma lem2260263 (x : real) (n : nat) : (term165 x n) = (term227 x n).
Proof. exact (MK_COMB (@lem2260262 x) (@lem2260260 x n)). Qed.
Lemma lem2260264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260265 (x : real) (n : nat) : (term172 x n) = (term172 x n).
Proof. exact (MK_COMB (@lem2260264) (@lem2260169 x n)). Qed.
Lemma lem2260266 (x : real) (n : nat) : (term173 x n) = (term228 x n).
Proof. exact (MK_COMB (@lem2260265 x n) (@lem2260263 x n)). Qed.
Lemma lem2260278 (x : real) (n : nat) : (term158 x n) = (term228 x n).
Proof. exact (TRANS (@lem2259938 x n) (@lem2260266 x n)). Qed.
Lemma lem2260280 (x : real) (n : nat) : (term229 n x) = (term230 x n).
Proof. exact (eq_refl (term229 n x)). Qed.
Lemma lem2260281 (n : nat) (x : real) : (term230 x n) = (term229 n x).
Proof. exact (SYM (@lem2260280 x n)). Qed.
Lemma lem2260282 (n : nat) (x : real) : (term229 n x) = (term231 n x).
Proof. exact (@lem1482981 (term232 x n) x). Qed.
Lemma lem2260283 (n : nat) (x : real) : (term230 x n) = (term231 n x).
Proof. exact (TRANS (@lem2260281 n x) (@lem2260282 n x)). Qed.
Lemma lem2260284 (x : real) (n : nat) : (term233 n x) = (term234 x n).
Proof. exact (eq_refl (term233 n x)). Qed.
Lemma lem2260285 (x : real) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem2260286 (x : real) (n : nat) : (term235 n x) = (term236 x n).
Proof. exact (MK_COMB (@lem2260285 x) (@lem2260284 x n)). Qed.
Lemma lem2260287 (x : real) (n : nat) : (term237 n x) = (term238 x n).
Proof. exact (eq_refl (term237 n x)). Qed.
Lemma lem2260288 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem2260289 (x : real) (n : nat) : (term239 n x) = (term240 x n).
Proof. exact (MK_COMB (@lem2260288 x) (@lem2260287 x n)). Qed.
Lemma lem2260290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260291 (x : real) (n : nat) : (term241 n x) = (term242 x n).
Proof. exact (MK_COMB (@lem2260290) (@lem2260289 x n)). Qed.
Lemma lem2260292 (x : real) (n : nat) : (term231 n x) = (term243 x n).
Proof. exact (MK_COMB (@lem2260291 x n) (@lem2260286 x n)). Qed.
Lemma lem2260293 (x : real) (n : nat) : (term244 x n) = (term244 x n).
Proof. exact (eq_refl (term244 x n)). Qed.
Lemma lem2260294 (x : real) (n : nat) : ((term230 x n) = (term231 n x)) = ((term230 x n) = (term243 x n)).
Proof. exact (MK_COMB (@lem2260293 x n) (@lem2260292 x n)). Qed.
Lemma lem2260295 (x : real) (n : nat) : (term230 x n) = (term243 x n).
Proof. exact (EQ_MP (@lem2260294 x n) (@lem2260283 n x)). Qed.
Lemma lem2260296 (x : real) (n : nat) : (term59 x n) = (term245 x n).
Proof. exact (@lem1988289 (term54 x n) term14). Qed.
Lemma lem2260314 (x : real) (n : nat) : (term246 x n) = (term247 x n).
Proof. exact (@lem1982792 (term54 x n) term14). Qed.
Lemma lem2260316 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260317 : term14 = term180.
Proof. exact (@lem2260316 (NUMERAL 0)). Qed.
Lemma lem2260319 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260320 : term26 = term31.
Proof. exact (@lem2260319 term32). Qed.
Lemma lem2260321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260322 : term33 = term34.
Proof. exact (MK_COMB (@lem2260321) (@lem2260320)). Qed.
Lemma lem2260323 : term181 = term182.
Proof. exact (MK_COMB (@lem2260322) (@lem2260317)). Qed.
Lemma lem2260324 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2260326 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260327 : term41 = term42.
Proof. exact (@lem2260326 term32 term32). Qed.
Lemma lem2260328 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260329 : term44 = term32.
Proof. exact (EQ_MP (@lem2260328) (@lem940073)). Qed.
Lemma lem2260330 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260331 : term42 = term38.
Proof. exact (MK_COMB (@lem2260330) (@lem2260329)). Qed.
Lemma lem2260332 : term41 = term38.
Proof. exact (TRANS (@lem2260327) (@lem2260331)). Qed.
Lemma lem2260334 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2260335 : term181 = term14.
Proof. exact (@lem2260334 term32). Qed.
Lemma lem2260336 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2260337 : term185 = term186.
Proof. exact (MK_COMB (@lem2260336) (@lem2260335)). Qed.
Lemma lem2260338 : term183 = term180.
Proof. exact (MK_COMB (@lem2260337) (@lem2260332)). Qed.
Lemma lem2260339 : term182 = term180.
Proof. exact (TRANS (@lem2260324) (@lem2260338)). Qed.
Lemma lem2260340 : term181 = term180.
Proof. exact (TRANS (@lem2260323) (@lem2260339)). Qed.
Lemma lem2260342 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2260343 : term180 = term14.
Proof. exact (@lem2260342 term14). Qed.
Lemma lem2260344 : term181 = term14.
Proof. exact (TRANS (@lem2260340) (@lem2260343)). Qed.
Lemma lem2260345 (x : real) (n : nat) : (term248 x n) = (term248 x n).
Proof. exact (eq_refl (term248 x n)). Qed.
Lemma lem2260346 (x : real) (n : nat) : (term247 x n) = (term249 x n).
Proof. exact (MK_COMB (@lem2260345 x n) (@lem2260344)). Qed.
Lemma lem2260347 (x : real) (n : nat) : (term249 x n) = (term54 x n).
Proof. exact (@lem1982723 (term54 x n)). Qed.
Lemma lem2260348 (x : real) (n : nat) : (term247 x n) = (term54 x n).
Proof. exact (TRANS (@lem2260346 x n) (@lem2260347 x n)). Qed.
Lemma lem2260350 (x : real) (n : nat) : (term246 x n) = (term54 x n).
Proof. exact (TRANS (@lem2260314 x n) (@lem2260348 x n)). Qed.
Lemma lem2260351 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260352 (x : real) (n : nat) : (term250 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem2260351) (@lem2260350 x n)). Qed.
Lemma lem2260353 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260354 (x : real) (n : nat) : (term245 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem2260352 x n) (@lem2260353)). Qed.
Lemma lem2260355 (x : real) (n : nat) : (term59 x n) = (term59 x n).
Proof. exact (TRANS (@lem2260296 x n) (@lem2260354 x n)). Qed.
Lemma lem2260356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260357 (x : real) (n : nat) : (term251 x n) = (term251 x n).
Proof. exact (MK_COMB (@lem2260356) (@lem2260355 x n)). Qed.
Lemma lem2260358 (x : real) (n : nat) : (term151 x n) = (term151 x n).
Proof. exact (MK_COMB (@lem2260357 x n) (@lem2260160 x n)). Qed.
Lemma lem2260359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260360 (x : real) (n : nat) : (term203 x n) = (term203 x n).
Proof. exact (MK_COMB (@lem2260359) (@lem2260046 x n)). Qed.
Lemma lem2260361 (x : real) (n : nat) : (term238 x n) = (term238 x n).
Proof. exact (MK_COMB (@lem2260360 x n) (@lem2260358 x n)). Qed.
Lemma lem2260362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260363 (x : real) : (term168 x) = (term168 x).
Proof. exact (MK_COMB (@lem2260362) (@lem2259986 x)). Qed.
Lemma lem2260364 (x : real) (n : nat) : (term240 x n) = (term240 x n).
Proof. exact (MK_COMB (@lem2260363 x) (@lem2260361 x n)). Qed.
Lemma lem2260365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260366 (x : real) (n : nat) : (term251 x n) = (term251 x n).
Proof. exact (MK_COMB (@lem2260365) (@lem2260355 x n)). Qed.
Lemma lem2260367 (x : real) (n : nat) : (term151 x n) = (term151 x n).
Proof. exact (MK_COMB (@lem2260366 x n) (@lem2260160 x n)). Qed.
Lemma lem2260368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260369 (x : real) (n : nat) : (term223 x n) = (term224 x n).
Proof. exact (MK_COMB (@lem2260368) (@lem2260254 x n)). Qed.
Lemma lem2260370 (x : real) (n : nat) : (term234 x n) = (term252 x n).
Proof. exact (MK_COMB (@lem2260369 x n) (@lem2260367 x n)). Qed.
Lemma lem2260371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260372 (x : real) : (term163 x) = (term226 x).
Proof. exact (MK_COMB (@lem2260371) (@lem2260188 x)). Qed.
Lemma lem2260373 (x : real) (n : nat) : (term236 x n) = (term253 x n).
Proof. exact (MK_COMB (@lem2260372 x) (@lem2260370 x n)). Qed.
Lemma lem2260374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260375 (x : real) (n : nat) : (term242 x n) = (term242 x n).
Proof. exact (MK_COMB (@lem2260374) (@lem2260364 x n)). Qed.
Lemma lem2260376 (x : real) (n : nat) : (term243 x n) = (term254 x n).
Proof. exact (MK_COMB (@lem2260375 x n) (@lem2260373 x n)). Qed.
Lemma lem2260388 (x : real) (n : nat) : (term230 x n) = (term254 x n).
Proof. exact (TRANS (@lem2260295 x n) (@lem2260376 x n)). Qed.
Lemma lem2260389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260390 (x : real) (n : nat) : (term255 x n) = (term256 x n).
Proof. exact (MK_COMB (@lem2260389) (@lem2260278 x n)). Qed.
Lemma lem2260391 (x : real) (n : nat) : (term149 x n) = (term257 x n).
Proof. exact (MK_COMB (@lem2260390 x n) (@lem2260388 x n)). Qed.
Lemma lem2260393 (x : real) (n : nat) : (term258 n x) = (term259 x n).
Proof. exact (eq_refl (term258 n x)). Qed.
Lemma lem2260394 (n : nat) (x : real) : (term259 x n) = (term258 n x).
Proof. exact (SYM (@lem2260393 x n)). Qed.
Lemma lem2260395 (n : nat) (x : real) : (term258 n x) = (term260 n x).
Proof. exact (@lem1482981 (term261 x n) x). Qed.
Lemma lem2260396 (n : nat) (x : real) : (term259 x n) = (term260 n x).
Proof. exact (TRANS (@lem2260394 n x) (@lem2260395 n x)). Qed.
Lemma lem2260397 (x : real) (n : nat) : (term262 n x) = (term263 x n).
Proof. exact (eq_refl (term262 n x)). Qed.
Lemma lem2260398 (x : real) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem2260399 (x : real) (n : nat) : (term264 n x) = (term265 x n).
Proof. exact (MK_COMB (@lem2260398 x) (@lem2260397 x n)). Qed.
Lemma lem2260400 (x : real) (n : nat) : (term266 n x) = (term267 x n).
Proof. exact (eq_refl (term266 n x)). Qed.
Lemma lem2260401 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem2260402 (x : real) (n : nat) : (term268 n x) = (term269 x n).
Proof. exact (MK_COMB (@lem2260401 x) (@lem2260400 x n)). Qed.
Lemma lem2260403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260404 (x : real) (n : nat) : (term270 n x) = (term271 x n).
Proof. exact (MK_COMB (@lem2260403) (@lem2260402 x n)). Qed.
Lemma lem2260405 (x : real) (n : nat) : (term260 n x) = (term272 x n).
Proof. exact (MK_COMB (@lem2260404 x n) (@lem2260399 x n)). Qed.
Lemma lem2260406 (x : real) (n : nat) : (term273 x n) = (term273 x n).
Proof. exact (eq_refl (term273 x n)). Qed.
Lemma lem2260407 (x : real) (n : nat) : ((term259 x n) = (term260 n x)) = ((term259 x n) = (term272 x n)).
Proof. exact (MK_COMB (@lem2260406 x n) (@lem2260405 x n)). Qed.
Lemma lem2260408 (x : real) (n : nat) : (term259 x n) = (term272 x n).
Proof. exact (EQ_MP (@lem2260407 x n) (@lem2260396 n x)). Qed.
Lemma lem2260409 (x : real) (n : nat) : (term81 x n) = (term274 x n).
Proof. exact (@lem1988289 (term76 x n) term14). Qed.
Lemma lem2260433 (x : real) (n : nat) : (term217 x n) = (term218 x n).
Proof. exact (@lem1982792 (term76 x n) term14). Qed.
Lemma lem2260435 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260436 : term14 = term180.
Proof. exact (@lem2260435 (NUMERAL 0)). Qed.
Lemma lem2260438 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260439 : term26 = term31.
Proof. exact (@lem2260438 term32). Qed.
Lemma lem2260440 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260441 : term33 = term34.
Proof. exact (MK_COMB (@lem2260440) (@lem2260439)). Qed.
Lemma lem2260442 : term181 = term182.
Proof. exact (MK_COMB (@lem2260441) (@lem2260436)). Qed.
Lemma lem2260443 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2260445 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260446 : term41 = term42.
Proof. exact (@lem2260445 term32 term32). Qed.
Lemma lem2260447 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260448 : term44 = term32.
Proof. exact (EQ_MP (@lem2260447) (@lem940073)). Qed.
Lemma lem2260449 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260450 : term42 = term38.
Proof. exact (MK_COMB (@lem2260449) (@lem2260448)). Qed.
Lemma lem2260451 : term41 = term38.
Proof. exact (TRANS (@lem2260446) (@lem2260450)). Qed.
Lemma lem2260453 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2260454 : term181 = term14.
Proof. exact (@lem2260453 term32). Qed.
Lemma lem2260455 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2260456 : term185 = term186.
Proof. exact (MK_COMB (@lem2260455) (@lem2260454)). Qed.
Lemma lem2260457 : term183 = term180.
Proof. exact (MK_COMB (@lem2260456) (@lem2260451)). Qed.
Lemma lem2260458 : term182 = term180.
Proof. exact (TRANS (@lem2260443) (@lem2260457)). Qed.
Lemma lem2260459 : term181 = term180.
Proof. exact (TRANS (@lem2260442) (@lem2260458)). Qed.
Lemma lem2260461 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2260462 : term180 = term14.
Proof. exact (@lem2260461 term14). Qed.
Lemma lem2260463 : term181 = term14.
Proof. exact (TRANS (@lem2260459) (@lem2260462)). Qed.
Lemma lem2260464 (x : real) (n : nat) : (term219 x n) = (term219 x n).
Proof. exact (eq_refl (term219 x n)). Qed.
Lemma lem2260465 (x : real) (n : nat) : (term218 x n) = (term220 x n).
Proof. exact (MK_COMB (@lem2260464 x n) (@lem2260463)). Qed.
Lemma lem2260466 (x : real) (n : nat) : (term220 x n) = (term76 x n).
Proof. exact (@lem1982723 (term76 x n)). Qed.
Lemma lem2260467 (x : real) (n : nat) : (term218 x n) = (term76 x n).
Proof. exact (TRANS (@lem2260465 x n) (@lem2260466 x n)). Qed.
Lemma lem2260469 (x : real) (n : nat) : (term217 x n) = (term76 x n).
Proof. exact (TRANS (@lem2260433 x n) (@lem2260467 x n)). Qed.
Lemma lem2260470 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260471 (x : real) (n : nat) : (term275 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem2260470) (@lem2260469 x n)). Qed.
Lemma lem2260472 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260473 (x : real) (n : nat) : (term274 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2260471 x n) (@lem2260472)). Qed.
Lemma lem2260474 (x : real) (n : nat) : (term81 x n) = (term81 x n).
Proof. exact (TRANS (@lem2260409 x n) (@lem2260473 x n)). Qed.
Lemma lem2260475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260476 (x : real) (n : nat) : (term202 x n) = (term202 x n).
Proof. exact (MK_COMB (@lem2260475) (@lem2260106 x n)). Qed.
Lemma lem2260477 (x : real) (n : nat) : (term146 x n) = (term146 x n).
Proof. exact (MK_COMB (@lem2260476 x n) (@lem2260474 x n)). Qed.
Lemma lem2260478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260479 (x : real) (n : nat) : (term203 x n) = (term203 x n).
Proof. exact (MK_COMB (@lem2260478) (@lem2260046 x n)). Qed.
Lemma lem2260480 (x : real) (n : nat) : (term267 x n) = (term267 x n).
Proof. exact (MK_COMB (@lem2260479 x n) (@lem2260477 x n)). Qed.
Lemma lem2260481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260482 (x : real) : (term168 x) = (term168 x).
Proof. exact (MK_COMB (@lem2260481) (@lem2259986 x)). Qed.
Lemma lem2260483 (x : real) (n : nat) : (term269 x n) = (term269 x n).
Proof. exact (MK_COMB (@lem2260482 x) (@lem2260480 x n)). Qed.
Lemma lem2260484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260485 (x : real) (n : nat) : (term202 x n) = (term202 x n).
Proof. exact (MK_COMB (@lem2260484) (@lem2260106 x n)). Qed.
Lemma lem2260486 (x : real) (n : nat) : (term146 x n) = (term146 x n).
Proof. exact (MK_COMB (@lem2260485 x n) (@lem2260474 x n)). Qed.
Lemma lem2260487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260488 (x : real) (n : nat) : (term223 x n) = (term224 x n).
Proof. exact (MK_COMB (@lem2260487) (@lem2260254 x n)). Qed.
Lemma lem2260489 (x : real) (n : nat) : (term263 x n) = (term276 x n).
Proof. exact (MK_COMB (@lem2260488 x n) (@lem2260486 x n)). Qed.
Lemma lem2260490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260491 (x : real) : (term163 x) = (term226 x).
Proof. exact (MK_COMB (@lem2260490) (@lem2260188 x)). Qed.
Lemma lem2260492 (x : real) (n : nat) : (term265 x n) = (term277 x n).
Proof. exact (MK_COMB (@lem2260491 x) (@lem2260489 x n)). Qed.
Lemma lem2260493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260494 (x : real) (n : nat) : (term271 x n) = (term271 x n).
Proof. exact (MK_COMB (@lem2260493) (@lem2260483 x n)). Qed.
Lemma lem2260495 (x : real) (n : nat) : (term272 x n) = (term278 x n).
Proof. exact (MK_COMB (@lem2260494 x n) (@lem2260492 x n)). Qed.
Lemma lem2260507 (x : real) (n : nat) : (term259 x n) = (term278 x n).
Proof. exact (TRANS (@lem2260408 x n) (@lem2260495 x n)). Qed.
Lemma lem2260509 (x : real) (n : nat) : (term279 n x) = (term280 x n).
Proof. exact (eq_refl (term279 n x)). Qed.
Lemma lem2260510 (n : nat) (x : real) : (term280 x n) = (term279 n x).
Proof. exact (SYM (@lem2260509 x n)). Qed.
Lemma lem2260511 (n : nat) (x : real) : (term279 n x) = (term281 n x).
Proof. exact (@lem1482981 (term282 x n) x). Qed.
Lemma lem2260512 (n : nat) (x : real) : (term280 x n) = (term281 n x).
Proof. exact (TRANS (@lem2260510 n x) (@lem2260511 n x)). Qed.
Lemma lem2260513 (x : real) (n : nat) : (term283 n x) = (term284 x n).
Proof. exact (eq_refl (term283 n x)). Qed.
Lemma lem2260514 (x : real) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem2260515 (x : real) (n : nat) : (term285 n x) = (term286 x n).
Proof. exact (MK_COMB (@lem2260514 x) (@lem2260513 x n)). Qed.
Lemma lem2260516 (x : real) (n : nat) : (term287 n x) = (term288 x n).
Proof. exact (eq_refl (term287 n x)). Qed.
Lemma lem2260517 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem2260518 (x : real) (n : nat) : (term289 n x) = (term290 x n).
Proof. exact (MK_COMB (@lem2260517 x) (@lem2260516 x n)). Qed.
Lemma lem2260519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260520 (x : real) (n : nat) : (term291 n x) = (term292 x n).
Proof. exact (MK_COMB (@lem2260519) (@lem2260518 x n)). Qed.
Lemma lem2260521 (x : real) (n : nat) : (term281 n x) = (term293 x n).
Proof. exact (MK_COMB (@lem2260520 x n) (@lem2260515 x n)). Qed.
Lemma lem2260522 (x : real) (n : nat) : (term294 x n) = (term294 x n).
Proof. exact (eq_refl (term294 x n)). Qed.
Lemma lem2260523 (x : real) (n : nat) : ((term280 x n) = (term281 n x)) = ((term280 x n) = (term293 x n)).
Proof. exact (MK_COMB (@lem2260522 x n) (@lem2260521 x n)). Qed.
Lemma lem2260524 (x : real) (n : nat) : (term280 x n) = (term293 x n).
Proof. exact (EQ_MP (@lem2260523 x n) (@lem2260512 n x)). Qed.
Lemma lem2260525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260526 (x : real) (n : nat) : (term251 x n) = (term251 x n).
Proof. exact (MK_COMB (@lem2260525) (@lem2260355 x n)). Qed.
Lemma lem2260527 (x : real) (n : nat) : (term147 x n) = (term147 x n).
Proof. exact (MK_COMB (@lem2260526 x n) (@lem2260474 x n)). Qed.
Lemma lem2260528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260529 (x : real) (n : nat) : (term203 x n) = (term203 x n).
Proof. exact (MK_COMB (@lem2260528) (@lem2260046 x n)). Qed.
Lemma lem2260530 (x : real) (n : nat) : (term288 x n) = (term288 x n).
Proof. exact (MK_COMB (@lem2260529 x n) (@lem2260527 x n)). Qed.
Lemma lem2260531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260532 (x : real) : (term168 x) = (term168 x).
Proof. exact (MK_COMB (@lem2260531) (@lem2259986 x)). Qed.
Lemma lem2260533 (x : real) (n : nat) : (term290 x n) = (term290 x n).
Proof. exact (MK_COMB (@lem2260532 x) (@lem2260530 x n)). Qed.
Lemma lem2260534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260535 (x : real) (n : nat) : (term251 x n) = (term251 x n).
Proof. exact (MK_COMB (@lem2260534) (@lem2260355 x n)). Qed.
Lemma lem2260536 (x : real) (n : nat) : (term147 x n) = (term147 x n).
Proof. exact (MK_COMB (@lem2260535 x n) (@lem2260474 x n)). Qed.
Lemma lem2260537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260538 (x : real) (n : nat) : (term223 x n) = (term224 x n).
Proof. exact (MK_COMB (@lem2260537) (@lem2260254 x n)). Qed.
Lemma lem2260539 (x : real) (n : nat) : (term284 x n) = (term295 x n).
Proof. exact (MK_COMB (@lem2260538 x n) (@lem2260536 x n)). Qed.
Lemma lem2260540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260541 (x : real) : (term163 x) = (term226 x).
Proof. exact (MK_COMB (@lem2260540) (@lem2260188 x)). Qed.
Lemma lem2260542 (x : real) (n : nat) : (term286 x n) = (term296 x n).
Proof. exact (MK_COMB (@lem2260541 x) (@lem2260539 x n)). Qed.
Lemma lem2260543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260544 (x : real) (n : nat) : (term292 x n) = (term292 x n).
Proof. exact (MK_COMB (@lem2260543) (@lem2260533 x n)). Qed.
Lemma lem2260545 (x : real) (n : nat) : (term293 x n) = (term297 x n).
Proof. exact (MK_COMB (@lem2260544 x n) (@lem2260542 x n)). Qed.
Lemma lem2260557 (x : real) (n : nat) : (term280 x n) = (term297 x n).
Proof. exact (TRANS (@lem2260524 x n) (@lem2260545 x n)). Qed.
Lemma lem2260558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260559 (x : real) (n : nat) : (term298 x n) = (term299 x n).
Proof. exact (MK_COMB (@lem2260558) (@lem2260507 x n)). Qed.
Lemma lem2260560 (x : real) (n : nat) : (term145 x n) = (term300 x n).
Proof. exact (MK_COMB (@lem2260559 x n) (@lem2260557 x n)). Qed.
Lemma lem2260561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260562 (x : real) (n : nat) : (term153 x n) = (term301 x n).
Proof. exact (MK_COMB (@lem2260561) (@lem2260391 x n)). Qed.
Lemma lem2260563 (x : real) (n : nat) : (term154 x n) = (term302 x n).
Proof. exact (MK_COMB (@lem2260562 x n) (@lem2260560 x n)). Qed.
Lemma lem2260565 (x : real) (n : nat) : (term303 n x) = (term304 x n).
Proof. exact (eq_refl (term303 n x)). Qed.
Lemma lem2260566 (n : nat) (x : real) : (term304 x n) = (term303 n x).
Proof. exact (SYM (@lem2260565 x n)). Qed.
Lemma lem2260567 (n : nat) (x : real) : (term303 n x) = (term305 n x).
Proof. exact (@lem1482981 (term306 x n) x). Qed.
Lemma lem2260568 (n : nat) (x : real) : (term304 x n) = (term305 n x).
Proof. exact (TRANS (@lem2260566 n x) (@lem2260567 n x)). Qed.
Lemma lem2260569 (x : real) (n : nat) : (term307 n x) = (term308 x n).
Proof. exact (eq_refl (term307 n x)). Qed.
Lemma lem2260570 (x : real) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem2260571 (x : real) (n : nat) : (term309 n x) = (term310 x n).
Proof. exact (MK_COMB (@lem2260570 x) (@lem2260569 x n)). Qed.
Lemma lem2260572 (x : real) (n : nat) : (term311 n x) = (term312 x n).
Proof. exact (eq_refl (term311 n x)). Qed.
Lemma lem2260573 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem2260574 (x : real) (n : nat) : (term313 n x) = (term314 x n).
Proof. exact (MK_COMB (@lem2260573 x) (@lem2260572 x n)). Qed.
Lemma lem2260575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260576 (x : real) (n : nat) : (term315 n x) = (term316 x n).
Proof. exact (MK_COMB (@lem2260575) (@lem2260574 x n)). Qed.
Lemma lem2260577 (x : real) (n : nat) : (term305 n x) = (term317 x n).
Proof. exact (MK_COMB (@lem2260576 x n) (@lem2260571 x n)). Qed.
Lemma lem2260578 (x : real) (n : nat) : (term318 x n) = (term318 x n).
Proof. exact (eq_refl (term318 x n)). Qed.
Lemma lem2260579 (x : real) (n : nat) : ((term304 x n) = (term305 n x)) = ((term304 x n) = (term317 x n)).
Proof. exact (MK_COMB (@lem2260578 x n) (@lem2260577 x n)). Qed.
Lemma lem2260580 (x : real) (n : nat) : (term304 x n) = (term317 x n).
Proof. exact (EQ_MP (@lem2260579 x n) (@lem2260568 n x)). Qed.
Lemma lem2260581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260582 (x : real) (n : nat) : (term202 x n) = (term202 x n).
Proof. exact (MK_COMB (@lem2260581) (@lem2260106 x n)). Qed.
Lemma lem2260583 (x : real) (n : nat) : (term312 x n) = (term312 x n).
Proof. exact (MK_COMB (@lem2260582 x n) (@lem2260046 x n)). Qed.
Lemma lem2260584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260585 (x : real) : (term168 x) = (term168 x).
Proof. exact (MK_COMB (@lem2260584) (@lem2259986 x)). Qed.
Lemma lem2260586 (x : real) (n : nat) : (term314 x n) = (term314 x n).
Proof. exact (MK_COMB (@lem2260585 x) (@lem2260583 x n)). Qed.
Lemma lem2260587 (x : real) (n : nat) : (term319 x n) = (term320 x n).
Proof. exact (@lem1988289 (term212 x n) term14). Qed.
Lemma lem2260588 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260595 (n : nat) : (term27 n) = (term27 n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem2260602 (x : real) : (real_neg x) = (term208 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem2260603 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2260604 (x : real) : (term214 x) = (term53 x).
Proof. exact (MK_COMB (@lem2260603) (@lem2260602 x)). Qed.
Lemma lem2260607 (x : real) (n : nat) : (term212 x n) = (term76 x n).
Proof. exact (MK_COMB (@lem2260604 x) (@lem2260595 n)). Qed.
Lemma lem2260608 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2260609 (x : real) (n : nat) : (term215 x n) = (term216 x n).
Proof. exact (MK_COMB (@lem2260608) (@lem2260607 x n)). Qed.
Lemma lem2260610 (x : real) (n : nat) : (term213 x n) = (term217 x n).
Proof. exact (MK_COMB (@lem2260609 x n) (@lem2260588)). Qed.
Lemma lem2260611 (x : real) (n : nat) : (term217 x n) = (term218 x n).
Proof. exact (@lem1982792 (term76 x n) term14). Qed.
Lemma lem2260613 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260614 : term14 = term180.
Proof. exact (@lem2260613 (NUMERAL 0)). Qed.
Lemma lem2260616 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260617 : term26 = term31.
Proof. exact (@lem2260616 term32). Qed.
Lemma lem2260618 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260619 : term33 = term34.
Proof. exact (MK_COMB (@lem2260618) (@lem2260617)). Qed.
Lemma lem2260620 : term181 = term182.
Proof. exact (MK_COMB (@lem2260619) (@lem2260614)). Qed.
Lemma lem2260621 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2260623 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260624 : term41 = term42.
Proof. exact (@lem2260623 term32 term32). Qed.
Lemma lem2260625 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260626 : term44 = term32.
Proof. exact (EQ_MP (@lem2260625) (@lem940073)). Qed.
Lemma lem2260627 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260628 : term42 = term38.
Proof. exact (MK_COMB (@lem2260627) (@lem2260626)). Qed.
Lemma lem2260629 : term41 = term38.
Proof. exact (TRANS (@lem2260624) (@lem2260628)). Qed.
Lemma lem2260631 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2260632 : term181 = term14.
Proof. exact (@lem2260631 term32). Qed.
Lemma lem2260633 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2260634 : term185 = term186.
Proof. exact (MK_COMB (@lem2260633) (@lem2260632)). Qed.
Lemma lem2260635 : term183 = term180.
Proof. exact (MK_COMB (@lem2260634) (@lem2260629)). Qed.
Lemma lem2260636 : term182 = term180.
Proof. exact (TRANS (@lem2260621) (@lem2260635)). Qed.
Lemma lem2260637 : term181 = term180.
Proof. exact (TRANS (@lem2260620) (@lem2260636)). Qed.
Lemma lem2260639 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2260640 : term180 = term14.
Proof. exact (@lem2260639 term14). Qed.
Lemma lem2260641 : term181 = term14.
Proof. exact (TRANS (@lem2260637) (@lem2260640)). Qed.
Lemma lem2260642 (x : real) (n : nat) : (term219 x n) = (term219 x n).
Proof. exact (eq_refl (term219 x n)). Qed.
Lemma lem2260643 (x : real) (n : nat) : (term218 x n) = (term220 x n).
Proof. exact (MK_COMB (@lem2260642 x n) (@lem2260641)). Qed.
Lemma lem2260644 (x : real) (n : nat) : (term220 x n) = (term76 x n).
Proof. exact (@lem1982723 (term76 x n)). Qed.
Lemma lem2260645 (x : real) (n : nat) : (term218 x n) = (term76 x n).
Proof. exact (TRANS (@lem2260643 x n) (@lem2260644 x n)). Qed.
Lemma lem2260646 (x : real) (n : nat) : (term217 x n) = (term76 x n).
Proof. exact (TRANS (@lem2260611 x n) (@lem2260645 x n)). Qed.
Lemma lem2260647 (x : real) (n : nat) : (term213 x n) = (term76 x n).
Proof. exact (TRANS (@lem2260610 x n) (@lem2260646 x n)). Qed.
Lemma lem2260648 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260649 (x : real) (n : nat) : (term321 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem2260648) (@lem2260647 x n)). Qed.
Lemma lem2260650 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260651 (x : real) (n : nat) : (term320 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2260649 x n) (@lem2260650)). Qed.
Lemma lem2260652 (x : real) (n : nat) : (term319 x n) = (term81 x n).
Proof. exact (TRANS (@lem2260587 x n) (@lem2260651 x n)). Qed.
Lemma lem2260653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260654 (x : real) (n : nat) : (term322 x n) = (term323 x n).
Proof. exact (MK_COMB (@lem2260653) (@lem2260652 x n)). Qed.
Lemma lem2260655 (x : real) (n : nat) : (term308 x n) = (term324 x n).
Proof. exact (MK_COMB (@lem2260654 x n) (@lem2260046 x n)). Qed.
Lemma lem2260656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260657 (x : real) : (term163 x) = (term226 x).
Proof. exact (MK_COMB (@lem2260656) (@lem2260188 x)). Qed.
Lemma lem2260658 (x : real) (n : nat) : (term310 x n) = (term325 x n).
Proof. exact (MK_COMB (@lem2260657 x) (@lem2260655 x n)). Qed.
Lemma lem2260659 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260660 (x : real) (n : nat) : (term316 x n) = (term316 x n).
Proof. exact (MK_COMB (@lem2260659) (@lem2260586 x n)). Qed.
Lemma lem2260661 (x : real) (n : nat) : (term317 x n) = (term326 x n).
Proof. exact (MK_COMB (@lem2260660 x n) (@lem2260658 x n)). Qed.
Lemma lem2260673 (x : real) (n : nat) : (term304 x n) = (term326 x n).
Proof. exact (TRANS (@lem2260580 x n) (@lem2260661 x n)). Qed.
Lemma lem2260675 (a : real) (x : real) (r : real) : (term327 x a r) = (term328 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2260676 (n : nat) (x : real) : (term106 x n) = (term329 n x).
Proof. exact (@lem2260675 (real_of_num n) x term14). Qed.
Lemma lem2260683 (x : real) : (term330 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem2260686 (n : nat) : (term331 n) = (term331 n).
Proof. exact (eq_refl (term331 n)). Qed.
Lemma lem2260687 (n : nat) (x : real) : (term332 n x) = (term333 n x).
Proof. exact (MK_COMB (@lem2260686 n) (@lem2260683 x)). Qed.
Lemma lem2260688 (x : real) (n : nat) : (term333 n x) = (term72 x n).
Proof. exact (@lem1982761 x (real_of_num n)). Qed.
Lemma lem2260689 (x : real) (n : nat) : (term332 n x) = (term72 x n).
Proof. exact (TRANS (@lem2260687 n x) (@lem2260688 x n)). Qed.
Lemma lem2260690 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260691 (x : real) (n : nat) : (term334 n x) = (term83 x n).
Proof. exact (MK_COMB (@lem2260690) (@lem2260689 x n)). Qed.
Lemma lem2260692 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260693 (x : real) (n : nat) : (term335 n x) = (term85 x n).
Proof. exact (MK_COMB (@lem2260691 x n) (@lem2260692)). Qed.
Lemma lem2260706 (x : real) (n : nat) : (term336 n x) = (term54 x n).
Proof. exact (@lem1982761 (term208 x) (real_of_num n)). Qed.
Lemma lem2260707 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260708 (x : real) (n : nat) : (term337 n x) = (term57 x n).
Proof. exact (MK_COMB (@lem2260707) (@lem2260706 x n)). Qed.
Lemma lem2260709 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260710 (x : real) (n : nat) : (term338 n x) = (term59 x n).
Proof. exact (MK_COMB (@lem2260708 x n) (@lem2260709)). Qed.
Lemma lem2260711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260712 (x : real) (n : nat) : (term339 n x) = (term251 x n).
Proof. exact (MK_COMB (@lem2260711) (@lem2260710 x n)). Qed.
Lemma lem2260713 (x : real) (n : nat) : (term329 n x) = (term151 x n).
Proof. exact (MK_COMB (@lem2260712 x n) (@lem2260693 x n)). Qed.
Lemma lem2260714 (x : real) (n : nat) : (term106 x n) = (term151 x n).
Proof. exact (TRANS (@lem2260676 n x) (@lem2260713 x n)). Qed.
Lemma lem2260715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260716 (x : real) (n : nat) : (term340 x n) = (term341 x n).
Proof. exact (MK_COMB (@lem2260715) (@lem2260714 x n)). Qed.
Lemma lem2260717 (x : real) (n : nat) : ((term21 x n) = term14) = ((term21 x n) = term14).
Proof. exact (eq_refl ((term21 x n) = term14)). Qed.
Lemma lem2260720 (x : real) (n : nat) : (term342 x n) = (term343 x n).
Proof. exact (MK_COMB (@lem2260716 x n) (@lem2260717 x n)). Qed.
Lemma lem2260721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260722 (x : real) (n : nat) : (term344 x n) = (term345 x n).
Proof. exact (MK_COMB (@lem2260721) (@lem2260673 x n)). Qed.
Lemma lem2260723 (x : real) (n : nat) : (term130 x n) = (term346 x n).
Proof. exact (MK_COMB (@lem2260722 x n) (@lem2260720 x n)). Qed.
Lemma lem2260725 (x : real) (n : nat) : (term347 n x) = (term348 x n).
Proof. exact (eq_refl (term347 n x)). Qed.
Lemma lem2260726 (n : nat) (x : real) : (term348 x n) = (term347 n x).
Proof. exact (SYM (@lem2260725 x n)). Qed.
Lemma lem2260727 (n : nat) (x : real) : (term347 n x) = (term349 n x).
Proof. exact (@lem1482981 (term350 x n) x). Qed.
Lemma lem2260728 (n : nat) (x : real) : (term348 x n) = (term349 n x).
Proof. exact (TRANS (@lem2260726 n x) (@lem2260727 n x)). Qed.
Lemma lem2260729 (x : real) (n : nat) : (term351 n x) = (term352 x n).
Proof. exact (eq_refl (term351 n x)). Qed.
Lemma lem2260730 (x : real) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem2260731 (x : real) (n : nat) : (term353 n x) = (term354 x n).
Proof. exact (MK_COMB (@lem2260730 x) (@lem2260729 x n)). Qed.
Lemma lem2260732 (x : real) (n : nat) : (term355 n x) = (term356 x n).
Proof. exact (eq_refl (term355 n x)). Qed.
Lemma lem2260733 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem2260734 (x : real) (n : nat) : (term357 n x) = (term358 x n).
Proof. exact (MK_COMB (@lem2260733 x) (@lem2260732 x n)). Qed.
Lemma lem2260735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260736 (x : real) (n : nat) : (term359 n x) = (term360 x n).
Proof. exact (MK_COMB (@lem2260735) (@lem2260734 x n)). Qed.
Lemma lem2260737 (x : real) (n : nat) : (term349 n x) = (term361 x n).
Proof. exact (MK_COMB (@lem2260736 x n) (@lem2260731 x n)). Qed.
Lemma lem2260738 (x : real) (n : nat) : (term362 x n) = (term362 x n).
Proof. exact (eq_refl (term362 x n)). Qed.
Lemma lem2260739 (x : real) (n : nat) : ((term348 x n) = (term349 n x)) = ((term348 x n) = (term361 x n)).
Proof. exact (MK_COMB (@lem2260738 x n) (@lem2260737 x n)). Qed.
Lemma lem2260740 (x : real) (n : nat) : (term348 x n) = (term361 x n).
Proof. exact (EQ_MP (@lem2260739 x n) (@lem2260728 n x)). Qed.
Lemma lem2260741 (x : real) (n : nat) : ((term72 x n) = term14) = ((term197 x n) = term14).
Proof. exact (@lem1988293 (term72 x n) term14). Qed.
Lemma lem2260753 (x : real) (n : nat) : (term197 x n) = (term198 x n).
Proof. exact (@lem1982792 (term72 x n) term14). Qed.
Lemma lem2260755 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260756 : term14 = term180.
Proof. exact (@lem2260755 (NUMERAL 0)). Qed.
Lemma lem2260758 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260759 : term26 = term31.
Proof. exact (@lem2260758 term32). Qed.
Lemma lem2260760 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260761 : term33 = term34.
Proof. exact (MK_COMB (@lem2260760) (@lem2260759)). Qed.
Lemma lem2260762 : term181 = term182.
Proof. exact (MK_COMB (@lem2260761) (@lem2260756)). Qed.
Lemma lem2260763 : term182 = term183.
Proof. exact (@lem1981613 term26 term14 term38 term38). Qed.
Lemma lem2260765 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260766 : term41 = term42.
Proof. exact (@lem2260765 term32 term32). Qed.
Lemma lem2260767 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260768 : term44 = term32.
Proof. exact (EQ_MP (@lem2260767) (@lem940073)). Qed.
Lemma lem2260769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260770 : term42 = term38.
Proof. exact (MK_COMB (@lem2260769) (@lem2260768)). Qed.
Lemma lem2260771 : term41 = term38.
Proof. exact (TRANS (@lem2260766) (@lem2260770)). Qed.
Lemma lem2260773 (x : nat) : (term184 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2260774 : term181 = term14.
Proof. exact (@lem2260773 term32). Qed.
Lemma lem2260775 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2260776 : term185 = term186.
Proof. exact (MK_COMB (@lem2260775) (@lem2260774)). Qed.
Lemma lem2260777 : term183 = term180.
Proof. exact (MK_COMB (@lem2260776) (@lem2260771)). Qed.
Lemma lem2260778 : term182 = term180.
Proof. exact (TRANS (@lem2260763) (@lem2260777)). Qed.
Lemma lem2260779 : term181 = term180.
Proof. exact (TRANS (@lem2260762) (@lem2260778)). Qed.
Lemma lem2260781 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2260782 : term180 = term14.
Proof. exact (@lem2260781 term14). Qed.
Lemma lem2260783 : term181 = term14.
Proof. exact (TRANS (@lem2260779) (@lem2260782)). Qed.
Lemma lem2260784 (x : real) (n : nat) : (term199 x n) = (term199 x n).
Proof. exact (eq_refl (term199 x n)). Qed.
Lemma lem2260785 (x : real) (n : nat) : (term198 x n) = (term200 x n).
Proof. exact (MK_COMB (@lem2260784 x n) (@lem2260783)). Qed.
Lemma lem2260786 (x : real) (n : nat) : (term200 x n) = (term72 x n).
Proof. exact (@lem1982723 (term72 x n)). Qed.
Lemma lem2260787 (x : real) (n : nat) : (term198 x n) = (term72 x n).
Proof. exact (TRANS (@lem2260785 x n) (@lem2260786 x n)). Qed.
Lemma lem2260789 (x : real) (n : nat) : (term197 x n) = (term72 x n).
Proof. exact (TRANS (@lem2260753 x n) (@lem2260787 x n)). Qed.
Lemma lem2260790 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2260791 (x : real) (n : nat) : (term363 x n) = (term117 x n).
Proof. exact (MK_COMB (@lem2260790) (@lem2260789 x n)). Qed.
Lemma lem2260792 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260793 (x : real) (n : nat) : ((term197 x n) = term14) = ((term72 x n) = term14).
Proof. exact (MK_COMB (@lem2260791 x n) (@lem2260792)). Qed.
Lemma lem2260794 (x : real) (n : nat) : ((term72 x n) = term14) = ((term72 x n) = term14).
Proof. exact (TRANS (@lem2260741 x n) (@lem2260793 x n)). Qed.
Lemma lem2260795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260796 (x : real) (n : nat) : (term202 x n) = (term202 x n).
Proof. exact (MK_COMB (@lem2260795) (@lem2260106 x n)). Qed.
Lemma lem2260797 (x : real) (n : nat) : (term356 x n) = (term356 x n).
Proof. exact (MK_COMB (@lem2260796 x n) (@lem2260794 x n)). Qed.
Lemma lem2260798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260799 (x : real) : (term168 x) = (term168 x).
Proof. exact (MK_COMB (@lem2260798) (@lem2259986 x)). Qed.
Lemma lem2260800 (x : real) (n : nat) : (term358 x n) = (term358 x n).
Proof. exact (MK_COMB (@lem2260799 x) (@lem2260797 x n)). Qed.
Lemma lem2260801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260802 (x : real) (n : nat) : (term322 x n) = (term323 x n).
Proof. exact (MK_COMB (@lem2260801) (@lem2260652 x n)). Qed.
Lemma lem2260803 (x : real) (n : nat) : (term352 x n) = (term364 x n).
Proof. exact (MK_COMB (@lem2260802 x n) (@lem2260794 x n)). Qed.
Lemma lem2260804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260805 (x : real) : (term163 x) = (term226 x).
Proof. exact (MK_COMB (@lem2260804) (@lem2260188 x)). Qed.
Lemma lem2260806 (x : real) (n : nat) : (term354 x n) = (term365 x n).
Proof. exact (MK_COMB (@lem2260805 x) (@lem2260803 x n)). Qed.
Lemma lem2260807 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260808 (x : real) (n : nat) : (term360 x n) = (term360 x n).
Proof. exact (MK_COMB (@lem2260807) (@lem2260800 x n)). Qed.
Lemma lem2260809 (x : real) (n : nat) : (term361 x n) = (term366 x n).
Proof. exact (MK_COMB (@lem2260808 x n) (@lem2260806 x n)). Qed.
Lemma lem2260821 (x : real) (n : nat) : (term348 x n) = (term366 x n).
Proof. exact (TRANS (@lem2260740 x n) (@lem2260809 x n)). Qed.
Lemma lem2260823 (a : real) (x : real) (r : real) : (term327 x a r) = (term328 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2260824 (n : nat) (x : real) : (term106 x n) = (term329 n x).
Proof. exact (@lem2260823 (real_of_num n) x term14). Qed.
Lemma lem2260831 (x : real) : (term330 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem2260834 (n : nat) : (term331 n) = (term331 n).
Proof. exact (eq_refl (term331 n)). Qed.
Lemma lem2260835 (n : nat) (x : real) : (term332 n x) = (term333 n x).
Proof. exact (MK_COMB (@lem2260834 n) (@lem2260831 x)). Qed.
Lemma lem2260836 (x : real) (n : nat) : (term333 n x) = (term72 x n).
Proof. exact (@lem1982761 x (real_of_num n)). Qed.
Lemma lem2260837 (x : real) (n : nat) : (term332 n x) = (term72 x n).
Proof. exact (TRANS (@lem2260835 n x) (@lem2260836 x n)). Qed.
Lemma lem2260838 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260839 (x : real) (n : nat) : (term334 n x) = (term83 x n).
Proof. exact (MK_COMB (@lem2260838) (@lem2260837 x n)). Qed.
Lemma lem2260840 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260841 (x : real) (n : nat) : (term335 n x) = (term85 x n).
Proof. exact (MK_COMB (@lem2260839 x n) (@lem2260840)). Qed.
Lemma lem2260854 (x : real) (n : nat) : (term336 n x) = (term54 x n).
Proof. exact (@lem1982761 (term208 x) (real_of_num n)). Qed.
Lemma lem2260855 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260856 (x : real) (n : nat) : (term337 n x) = (term57 x n).
Proof. exact (MK_COMB (@lem2260855) (@lem2260854 x n)). Qed.
Lemma lem2260857 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260858 (x : real) (n : nat) : (term338 n x) = (term59 x n).
Proof. exact (MK_COMB (@lem2260856 x n) (@lem2260857)). Qed.
Lemma lem2260859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260860 (x : real) (n : nat) : (term339 n x) = (term251 x n).
Proof. exact (MK_COMB (@lem2260859) (@lem2260858 x n)). Qed.
Lemma lem2260861 (x : real) (n : nat) : (term329 n x) = (term151 x n).
Proof. exact (MK_COMB (@lem2260860 x n) (@lem2260841 x n)). Qed.
Lemma lem2260862 (x : real) (n : nat) : (term106 x n) = (term151 x n).
Proof. exact (TRANS (@lem2260824 n x) (@lem2260861 x n)). Qed.
Lemma lem2260863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2260864 (x : real) (n : nat) : (term340 x n) = (term341 x n).
Proof. exact (MK_COMB (@lem2260863) (@lem2260862 x n)). Qed.
Lemma lem2260865 (x : real) (n : nat) : ((term72 x n) = term14) = ((term72 x n) = term14).
Proof. exact (eq_refl ((term72 x n) = term14)). Qed.
Lemma lem2260868 (x : real) (n : nat) : (term367 x n) = (term368 x n).
Proof. exact (MK_COMB (@lem2260864 x n) (@lem2260865 x n)). Qed.
Lemma lem2260869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260870 (x : real) (n : nat) : (term369 x n) = (term370 x n).
Proof. exact (MK_COMB (@lem2260869) (@lem2260821 x n)). Qed.
Lemma lem2260871 (x : real) (n : nat) : (term128 x n) = (term371 x n).
Proof. exact (MK_COMB (@lem2260870 x n) (@lem2260868 x n)). Qed.
Lemma lem2260872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260873 (x : real) (n : nat) : (term132 x n) = (term372 x n).
Proof. exact (MK_COMB (@lem2260872) (@lem2260723 x n)). Qed.
Lemma lem2260874 (x : real) (n : nat) : (term133 x n) = (term373 x n).
Proof. exact (MK_COMB (@lem2260873 x n) (@lem2260871 x n)). Qed.
Lemma lem2260875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2260876 (x : real) (n : nat) : (term155 x n) = (term374 x n).
Proof. exact (MK_COMB (@lem2260875) (@lem2260563 x n)). Qed.
Lemma lem2260877 (x : real) (n : nat) : (term156 x n) = (term375 x n).
Proof. exact (MK_COMB (@lem2260876 x n) (@lem2260874 x n)). Qed.
Lemma lem2260878 (x : real) (n : nat) (h1 : term375 x n) : term375 x n.
Proof. exact (h1). Qed.
Lemma lem2260879 (x : real) (n : nat) (h1 : term302 x n) : term302 x n.
Proof. exact (h1). Qed.
Lemma lem2260880 (x : real) (n : nat) (h1 : term257 x n) : term257 x n.
Proof. exact (h1). Qed.
Lemma lem2260881 (x : real) (n : nat) (h1 : term228 x n) : term228 x n.
Proof. exact (h1). Qed.
Lemma lem2260882 (x : real) (n : nat) (h1 : term170 x n) : term170 x n.
Proof. exact (h1). Qed.
Lemma lem2260883 (x : real) (n : nat) (h1 : term170 x n) : term167 x n.
Proof. exact (proj2 (@lem2260882 x n h1)). Qed.
Lemma lem2260885 (x : real) (n : nat) (h1 : term170 x n) : term150 x n.
Proof. exact (proj2 (@lem2260883 x n h1)). Qed.
Lemma lem2260886 (x : real) (n : nat) (h1 : term170 x n) : (term21 x n) = term14.
Proof. exact (proj1 (@lem2260883 x n h1)). Qed.
Lemma lem2260888 (x : real) (n : nat) (h1 : term170 x n) : term63 x n.
Proof. exact (proj1 (@lem2260885 x n h1)). Qed.
Lemma lem2260891 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2260892 : term376 = term377.
Proof. exact (@lem2260891 term14 term38). Qed.
Lemma lem2260894 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260895 : term38 = term48.
Proof. exact (@lem2260894 term32). Qed.
Lemma lem2260897 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2260898 : term14 = term180.
Proof. exact (@lem2260897 (NUMERAL 0)). Qed.
Lemma lem2260899 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2260900 : term378 = term379.
Proof. exact (MK_COMB (@lem2260899) (@lem2260898)). Qed.
Lemma lem2260901 : term377 = term380.
Proof. exact (MK_COMB (@lem2260900) (@lem2260895)). Qed.
Lemma lem2260902 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2260904 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2260905 : term377 = term383.
Proof. exact (@lem2260904 (NUMERAL 0) term32). Qed.
Lemma lem2260906 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2260907 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2260908 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2260907 h1) (fun h1 : term383 = True => @lem2260906)). Qed.
Lemma lem2260909 : term383 = True.
Proof. exact (EQ_MP (@lem2260908) (@lem2260906)). Qed.
Lemma lem2260910 : term377 = True.
Proof. exact (TRANS (@lem2260905) (@lem2260909)). Qed.
Lemma lem2260911 : True = term377.
Proof. exact (SYM (@lem2260910)). Qed.
Lemma lem2260912 : term377.
Proof. exact (EQ_MP (@lem2260911) (@lem0)). Qed.
Lemma lem2260913 : term385.
Proof. exact (@lem2260902 (@lem2260912)). Qed.
Lemma lem2260915 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2260916 : term377 = term383.
Proof. exact (@lem2260915 (NUMERAL 0) term32). Qed.
Lemma lem2260917 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2260918 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2260919 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2260918 h1) (fun h1 : term383 = True => @lem2260917)). Qed.
Lemma lem2260920 : term383 = True.
Proof. exact (EQ_MP (@lem2260919) (@lem2260917)). Qed.
Lemma lem2260921 : term377 = True.
Proof. exact (TRANS (@lem2260916) (@lem2260920)). Qed.
Lemma lem2260922 : True = term377.
Proof. exact (SYM (@lem2260921)). Qed.
Lemma lem2260923 : term377.
Proof. exact (EQ_MP (@lem2260922) (@lem0)). Qed.
Lemma lem2260924 : term380 = term386.
Proof. exact (@lem2260913 (@lem2260923)). Qed.
Lemma lem2260926 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260927 : term41 = term42.
Proof. exact (@lem2260926 term32 term32). Qed.
Lemma lem2260928 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260929 : term44 = term32.
Proof. exact (EQ_MP (@lem2260928) (@lem940073)). Qed.
Lemma lem2260930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260931 : term42 = term38.
Proof. exact (MK_COMB (@lem2260930) (@lem2260929)). Qed.
Lemma lem2260932 : term41 = term38.
Proof. exact (TRANS (@lem2260927) (@lem2260931)). Qed.
Lemma lem2260934 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2260935 : term388 = term14.
Proof. exact (@lem2260934 term32). Qed.
Lemma lem2260936 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2260937 : term389 = term378.
Proof. exact (MK_COMB (@lem2260936) (@lem2260935)). Qed.
Lemma lem2260938 : term386 = term377.
Proof. exact (MK_COMB (@lem2260937) (@lem2260932)). Qed.
Lemma lem2260940 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2260941 : term377 = term383.
Proof. exact (@lem2260940 (NUMERAL 0) term32). Qed.
Lemma lem2260942 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2260943 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2260944 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2260943 h1) (fun h1 : term383 = True => @lem2260942)). Qed.
Lemma lem2260945 : term383 = True.
Proof. exact (EQ_MP (@lem2260944) (@lem2260942)). Qed.
Lemma lem2260946 : term377 = True.
Proof. exact (TRANS (@lem2260941) (@lem2260945)). Qed.
Lemma lem2260947 : term386 = True.
Proof. exact (TRANS (@lem2260938) (@lem2260946)). Qed.
Lemma lem2260948 : term380 = True.
Proof. exact (TRANS (@lem2260924) (@lem2260947)). Qed.
Lemma lem2260949 : term377 = True.
Proof. exact (TRANS (@lem2260901) (@lem2260948)). Qed.
Lemma lem2260950 : term376 = True.
Proof. exact (TRANS (@lem2260892) (@lem2260949)). Qed.
Lemma lem2260951 : True = term376.
Proof. exact (SYM (@lem2260950)). Qed.
Lemma lem2260952 : term376.
Proof. exact (EQ_MP (@lem2260951) (@lem0)). Qed.
Lemma lem2260953 (x : real) (n : nat) (h1 : term170 x n) : term390 x n.
Proof. exact (conj (@lem2260952) (@lem2260888 x n h1)). Qed.
Lemma lem2260955 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2260956 (x : real) (n : nat) : term392 x n.
Proof. exact (@lem2260955 term38 (term21 x n)). Qed.
Lemma lem2260957 (x : real) (n : nat) (h1 : term170 x n) : term393 x n.
Proof. exact (@lem2260956 x n (@lem2260953 x n h1)). Qed.
Lemma lem2260958 (x : real) (n : nat) : (term394 x n) = (term21 x n).
Proof. exact (@lem1982733 (term21 x n)). Qed.
Lemma lem2260959 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2260960 (x : real) (n : nat) : (term395 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem2260959) (@lem2260958 x n)). Qed.
Lemma lem2260961 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2260962 (x : real) (n : nat) : (term393 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem2260960 x n) (@lem2260961)). Qed.
Lemma lem2260963 (x : real) (n : nat) (h1 : term170 x n) : term63 x n.
Proof. exact (EQ_MP (@lem2260962 x n) (@lem2260957 x n h1)). Qed.
Lemma lem2260965 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2260966 (x : real) (n : nat) : term397 x n.
Proof. exact (@lem2260965 (term21 x n)). Qed.
Lemma lem2260967 (x : real) (n : nat) (h1 : term170 x n) : term398 x n.
Proof. exact (@lem2260966 x n (@lem2260886 x n h1)). Qed.
Lemma lem2260968 (x : real) (n : nat) (h1 : term170 x n) : term399 x n.
Proof. exact (@lem2260967 x n h1 term26). Qed.
Lemma lem2260969 (x : real) (n : nat) : (term399 x n) = ((term24 x n) = term14).
Proof. exact (eq_refl (term399 x n)). Qed.
Lemma lem2260970 (x : real) (n : nat) (h1 : term170 x n) : (term24 x n) = term14.
Proof. exact (EQ_MP (@lem2260969 x n) (@lem2260968 x n h1)). Qed.
Lemma lem2260971 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (@lem1982781 x term26 (term27 n)). Qed.
Lemma lem2260972 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2260974 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260975 : term26 = term31.
Proof. exact (@lem2260974 term32). Qed.
Lemma lem2260977 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2260978 : term26 = term31.
Proof. exact (@lem2260977 term32). Qed.
Lemma lem2260979 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2260980 : term33 = term34.
Proof. exact (MK_COMB (@lem2260979) (@lem2260978)). Qed.
Lemma lem2260981 : term35 = term36.
Proof. exact (MK_COMB (@lem2260980) (@lem2260975)). Qed.
Lemma lem2260982 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2260984 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2260985 : term41 = term42.
Proof. exact (@lem2260984 term32 term32). Qed.
Lemma lem2260986 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260987 : term44 = term32.
Proof. exact (EQ_MP (@lem2260986) (@lem940073)). Qed.
Lemma lem2260988 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260989 : term42 = term38.
Proof. exact (MK_COMB (@lem2260988) (@lem2260987)). Qed.
Lemma lem2260990 : term41 = term38.
Proof. exact (TRANS (@lem2260985) (@lem2260989)). Qed.
Lemma lem2260992 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2260993 : term35 = term42.
Proof. exact (@lem2260992 term32 term32). Qed.
Lemma lem2260994 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2260995 : term44 = term32.
Proof. exact (EQ_MP (@lem2260994) (@lem940073)). Qed.
Lemma lem2260996 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2260997 : term42 = term38.
Proof. exact (MK_COMB (@lem2260996) (@lem2260995)). Qed.
Lemma lem2260998 : term35 = term38.
Proof. exact (TRANS (@lem2260993) (@lem2260997)). Qed.
Lemma lem2260999 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2261000 : term46 = term47.
Proof. exact (MK_COMB (@lem2260999) (@lem2260998)). Qed.
Lemma lem2261001 : term37 = term48.
Proof. exact (MK_COMB (@lem2261000) (@lem2260990)). Qed.
Lemma lem2261002 : term36 = term48.
Proof. exact (TRANS (@lem2260982) (@lem2261001)). Qed.
Lemma lem2261003 : term35 = term48.
Proof. exact (TRANS (@lem2260981) (@lem2261002)). Qed.
Lemma lem2261005 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2261006 : term48 = term38.
Proof. exact (@lem2261005 term38). Qed.
Lemma lem2261007 : term35 = term38.
Proof. exact (TRANS (@lem2261003) (@lem2261006)). Qed.
Lemma lem2261008 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261009 : term50 = term51.
Proof. exact (MK_COMB (@lem2261008) (@lem2261007)). Qed.
Lemma lem2261010 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2261011 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2261009) (@lem2261010 n)). Qed.
Lemma lem2261012 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2260972 n) (@lem2261011 n)). Qed.
Lemma lem2261013 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2261014 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2261012 n) (@lem2261013 n)). Qed.
Lemma lem2261017 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2261018 (x : real) (n : nat) : (term25 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem2261017 x) (@lem2261014 n)). Qed.
Lemma lem2261019 (x : real) (n : nat) : (term24 x n) = (term54 x n).
Proof. exact (TRANS (@lem2260971 x n) (@lem2261018 x n)). Qed.
Lemma lem2261020 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2261021 (x : real) (n : nat) : (term400 x n) = (term401 x n).
Proof. exact (MK_COMB (@lem2261020) (@lem2261019 x n)). Qed.
Lemma lem2261022 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2261023 (x : real) (n : nat) : ((term24 x n) = term14) = ((term54 x n) = term14).
Proof. exact (MK_COMB (@lem2261021 x n) (@lem2261022)). Qed.
Lemma lem2261024 (x : real) (n : nat) (h1 : term170 x n) : (term54 x n) = term14.
Proof. exact (EQ_MP (@lem2261023 x n) (@lem2260970 x n h1)). Qed.
Lemma lem2261025 (x : real) (n : nat) (h1 : term170 x n) : term402 x n.
Proof. exact (conj (@lem2261024 x n h1) (@lem2260963 x n h1)). Qed.
Lemma lem2261027 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2261028 (x : real) (n : nat) : term404 x n.
Proof. exact (@lem2261027 (term54 x n) (term21 x n)). Qed.
Lemma lem2261029 (x : real) (n : nat) (h1 : term170 x n) : term405 x n.
Proof. exact (@lem2261028 x n (@lem2261025 x n h1)). Qed.
Lemma lem2261030 (x : real) (n : nat) : (term406 x n) = (term407 x n).
Proof. exact (@lem1982753 (term208 x) x (real_of_num n) (term27 n)). Qed.
Lemma lem2261031 (x : real) : (term408 x) = (term409 x).
Proof. exact (@lem1982713 term26 x). Qed.
Lemma lem2261033 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261034 : term38 = term48.
Proof. exact (@lem2261033 term32). Qed.
Lemma lem2261036 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2261037 : term26 = term31.
Proof. exact (@lem2261036 term32). Qed.
Lemma lem2261038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261039 : term410 = term411.
Proof. exact (MK_COMB (@lem2261038) (@lem2261037)). Qed.
Lemma lem2261040 : term412 = term413.
Proof. exact (MK_COMB (@lem2261039) (@lem2261034)). Qed.
Lemma lem2261041 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2261043 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261044 : term377 = term383.
Proof. exact (@lem2261043 (NUMERAL 0) term32). Qed.
Lemma lem2261045 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261046 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261047 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261046 h1) (fun h1 : term383 = True => @lem2261045)). Qed.
Lemma lem2261048 : term383 = True.
Proof. exact (EQ_MP (@lem2261047) (@lem2261045)). Qed.
Lemma lem2261049 : term377 = True.
Proof. exact (TRANS (@lem2261044) (@lem2261048)). Qed.
Lemma lem2261050 : True = term377.
Proof. exact (SYM (@lem2261049)). Qed.
Lemma lem2261051 : term377.
Proof. exact (EQ_MP (@lem2261050) (@lem0)). Qed.
Lemma lem2261052 : term415.
Proof. exact (@lem2261041 (@lem2261051)). Qed.
Lemma lem2261054 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261055 : term377 = term383.
Proof. exact (@lem2261054 (NUMERAL 0) term32). Qed.
Lemma lem2261056 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261057 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261058 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261057 h1) (fun h1 : term383 = True => @lem2261056)). Qed.
Lemma lem2261059 : term383 = True.
Proof. exact (EQ_MP (@lem2261058) (@lem2261056)). Qed.
Lemma lem2261060 : term377 = True.
Proof. exact (TRANS (@lem2261055) (@lem2261059)). Qed.
Lemma lem2261061 : True = term377.
Proof. exact (SYM (@lem2261060)). Qed.
Lemma lem2261062 : term377.
Proof. exact (EQ_MP (@lem2261061) (@lem0)). Qed.
Lemma lem2261063 : term416.
Proof. exact (@lem2261052 (@lem2261062)). Qed.
Lemma lem2261065 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261066 : term377 = term383.
Proof. exact (@lem2261065 (NUMERAL 0) term32). Qed.
Lemma lem2261067 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261068 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261069 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261068 h1) (fun h1 : term383 = True => @lem2261067)). Qed.
Lemma lem2261070 : term383 = True.
Proof. exact (EQ_MP (@lem2261069) (@lem2261067)). Qed.
Lemma lem2261071 : term377 = True.
Proof. exact (TRANS (@lem2261066) (@lem2261070)). Qed.
Lemma lem2261072 : True = term377.
Proof. exact (SYM (@lem2261071)). Qed.
Lemma lem2261073 : term377.
Proof. exact (EQ_MP (@lem2261072) (@lem0)). Qed.
Lemma lem2261074 : term417.
Proof. exact (@lem2261063 (@lem2261073)). Qed.
Lemma lem2261076 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261077 : term41 = term42.
Proof. exact (@lem2261076 term32 term32). Qed.
Lemma lem2261078 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261079 : term44 = term32.
Proof. exact (EQ_MP (@lem2261078) (@lem940073)). Qed.
Lemma lem2261080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261081 : term42 = term38.
Proof. exact (MK_COMB (@lem2261080) (@lem2261079)). Qed.
Lemma lem2261082 : term41 = term38.
Proof. exact (TRANS (@lem2261077) (@lem2261081)). Qed.
Lemma lem2261084 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2261085 : term420 = term421.
Proof. exact (@lem2261084 term32 term32). Qed.
Lemma lem2261086 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261087 : term44 = term32.
Proof. exact (EQ_MP (@lem2261086) (@lem940073)). Qed.
Lemma lem2261088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261089 : term42 = term38.
Proof. exact (MK_COMB (@lem2261088) (@lem2261087)). Qed.
Lemma lem2261090 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2261091 : term421 = term26.
Proof. exact (MK_COMB (@lem2261090) (@lem2261089)). Qed.
Lemma lem2261092 : term420 = term26.
Proof. exact (TRANS (@lem2261085) (@lem2261091)). Qed.
Lemma lem2261093 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261094 : term422 = term410.
Proof. exact (MK_COMB (@lem2261093) (@lem2261092)). Qed.
Lemma lem2261095 : term423 = term412.
Proof. exact (MK_COMB (@lem2261094) (@lem2261082)). Qed.
Lemma lem2261097 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2261098 : term412 = term14.
Proof. exact (@lem2261097 term32). Qed.
Lemma lem2261099 : term423 = term14.
Proof. exact (TRANS (@lem2261095) (@lem2261098)). Qed.
Lemma lem2261100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261101 : term425 = term426.
Proof. exact (MK_COMB (@lem2261100) (@lem2261099)). Qed.
Lemma lem2261102 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2261103 : term427 = term388.
Proof. exact (MK_COMB (@lem2261101) (@lem2261102)). Qed.
Lemma lem2261105 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261106 : term388 = term14.
Proof. exact (@lem2261105 term32). Qed.
Lemma lem2261107 : term427 = term14.
Proof. exact (TRANS (@lem2261103) (@lem2261106)). Qed.
Lemma lem2261109 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261110 : term41 = term42.
Proof. exact (@lem2261109 term32 term32). Qed.
Lemma lem2261111 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261112 : term44 = term32.
Proof. exact (EQ_MP (@lem2261111) (@lem940073)). Qed.
Lemma lem2261113 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261114 : term42 = term38.
Proof. exact (MK_COMB (@lem2261113) (@lem2261112)). Qed.
Lemma lem2261115 : term41 = term38.
Proof. exact (TRANS (@lem2261110) (@lem2261114)). Qed.
Lemma lem2261116 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2261117 : term428 = term388.
Proof. exact (MK_COMB (@lem2261116) (@lem2261115)). Qed.
Lemma lem2261119 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261120 : term388 = term14.
Proof. exact (@lem2261119 term32). Qed.
Lemma lem2261121 : term428 = term14.
Proof. exact (TRANS (@lem2261117) (@lem2261120)). Qed.
Lemma lem2261122 : term14 = term428.
Proof. exact (SYM (@lem2261121)). Qed.
Lemma lem2261123 : term427 = term428.
Proof. exact (TRANS (@lem2261107) (@lem2261122)). Qed.
Lemma lem2261124 : term413 = term180.
Proof. exact (@lem2261074 (@lem2261123)). Qed.
Lemma lem2261125 : term412 = term180.
Proof. exact (TRANS (@lem2261040) (@lem2261124)). Qed.
Lemma lem2261127 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2261128 : term180 = term14.
Proof. exact (@lem2261127 term14). Qed.
Lemma lem2261129 : term412 = term14.
Proof. exact (TRANS (@lem2261125) (@lem2261128)). Qed.
Lemma lem2261130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261131 : term429 = term426.
Proof. exact (MK_COMB (@lem2261130) (@lem2261129)). Qed.
Lemma lem2261132 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2261133 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2261131) (@lem2261132 x)). Qed.
Lemma lem2261134 (x : real) : (term408 x) = (term430 x).
Proof. exact (TRANS (@lem2261031 x) (@lem2261133 x)). Qed.
Lemma lem2261135 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2261136 (x : real) : (term408 x) = term14.
Proof. exact (TRANS (@lem2261134 x) (@lem2261135 x)). Qed.
Lemma lem2261137 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261138 (x : real) : (term431 x) = term432.
Proof. exact (MK_COMB (@lem2261137) (@lem2261136 x)). Qed.
Lemma lem2261139 (n : nat) : (term433 n) = (term434 n).
Proof. exact (@lem1982715 term26 (real_of_num n)). Qed.
Lemma lem2261141 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261142 : term38 = term48.
Proof. exact (@lem2261141 term32). Qed.
Lemma lem2261144 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2261145 : term26 = term31.
Proof. exact (@lem2261144 term32). Qed.
Lemma lem2261146 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261147 : term410 = term411.
Proof. exact (MK_COMB (@lem2261146) (@lem2261145)). Qed.
Lemma lem2261148 : term412 = term413.
Proof. exact (MK_COMB (@lem2261147) (@lem2261142)). Qed.
Lemma lem2261149 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2261151 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261152 : term377 = term383.
Proof. exact (@lem2261151 (NUMERAL 0) term32). Qed.
Lemma lem2261153 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261154 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261155 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261154 h1) (fun h1 : term383 = True => @lem2261153)). Qed.
Lemma lem2261156 : term383 = True.
Proof. exact (EQ_MP (@lem2261155) (@lem2261153)). Qed.
Lemma lem2261157 : term377 = True.
Proof. exact (TRANS (@lem2261152) (@lem2261156)). Qed.
Lemma lem2261158 : True = term377.
Proof. exact (SYM (@lem2261157)). Qed.
Lemma lem2261159 : term377.
Proof. exact (EQ_MP (@lem2261158) (@lem0)). Qed.
Lemma lem2261160 : term415.
Proof. exact (@lem2261149 (@lem2261159)). Qed.
Lemma lem2261162 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261163 : term377 = term383.
Proof. exact (@lem2261162 (NUMERAL 0) term32). Qed.
Lemma lem2261164 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261165 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261166 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261165 h1) (fun h1 : term383 = True => @lem2261164)). Qed.
Lemma lem2261167 : term383 = True.
Proof. exact (EQ_MP (@lem2261166) (@lem2261164)). Qed.
Lemma lem2261168 : term377 = True.
Proof. exact (TRANS (@lem2261163) (@lem2261167)). Qed.
Lemma lem2261169 : True = term377.
Proof. exact (SYM (@lem2261168)). Qed.
Lemma lem2261170 : term377.
Proof. exact (EQ_MP (@lem2261169) (@lem0)). Qed.
Lemma lem2261171 : term416.
Proof. exact (@lem2261160 (@lem2261170)). Qed.
Lemma lem2261173 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261174 : term377 = term383.
Proof. exact (@lem2261173 (NUMERAL 0) term32). Qed.
Lemma lem2261175 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261176 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261177 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261176 h1) (fun h1 : term383 = True => @lem2261175)). Qed.
Lemma lem2261178 : term383 = True.
Proof. exact (EQ_MP (@lem2261177) (@lem2261175)). Qed.
Lemma lem2261179 : term377 = True.
Proof. exact (TRANS (@lem2261174) (@lem2261178)). Qed.
Lemma lem2261180 : True = term377.
Proof. exact (SYM (@lem2261179)). Qed.
Lemma lem2261181 : term377.
Proof. exact (EQ_MP (@lem2261180) (@lem0)). Qed.
Lemma lem2261182 : term417.
Proof. exact (@lem2261171 (@lem2261181)). Qed.
Lemma lem2261184 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261185 : term41 = term42.
Proof. exact (@lem2261184 term32 term32). Qed.
Lemma lem2261186 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261187 : term44 = term32.
Proof. exact (EQ_MP (@lem2261186) (@lem940073)). Qed.
Lemma lem2261188 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261189 : term42 = term38.
Proof. exact (MK_COMB (@lem2261188) (@lem2261187)). Qed.
Lemma lem2261190 : term41 = term38.
Proof. exact (TRANS (@lem2261185) (@lem2261189)). Qed.
Lemma lem2261192 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2261193 : term420 = term421.
Proof. exact (@lem2261192 term32 term32). Qed.
Lemma lem2261194 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261195 : term44 = term32.
Proof. exact (EQ_MP (@lem2261194) (@lem940073)). Qed.
Lemma lem2261196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261197 : term42 = term38.
Proof. exact (MK_COMB (@lem2261196) (@lem2261195)). Qed.
Lemma lem2261198 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2261199 : term421 = term26.
Proof. exact (MK_COMB (@lem2261198) (@lem2261197)). Qed.
Lemma lem2261200 : term420 = term26.
Proof. exact (TRANS (@lem2261193) (@lem2261199)). Qed.
Lemma lem2261201 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261202 : term422 = term410.
Proof. exact (MK_COMB (@lem2261201) (@lem2261200)). Qed.
Lemma lem2261203 : term423 = term412.
Proof. exact (MK_COMB (@lem2261202) (@lem2261190)). Qed.
Lemma lem2261205 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2261206 : term412 = term14.
Proof. exact (@lem2261205 term32). Qed.
Lemma lem2261207 : term423 = term14.
Proof. exact (TRANS (@lem2261203) (@lem2261206)). Qed.
Lemma lem2261208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261209 : term425 = term426.
Proof. exact (MK_COMB (@lem2261208) (@lem2261207)). Qed.
Lemma lem2261210 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2261211 : term427 = term388.
Proof. exact (MK_COMB (@lem2261209) (@lem2261210)). Qed.
Lemma lem2261213 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261214 : term388 = term14.
Proof. exact (@lem2261213 term32). Qed.
Lemma lem2261215 : term427 = term14.
Proof. exact (TRANS (@lem2261211) (@lem2261214)). Qed.
Lemma lem2261217 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261218 : term41 = term42.
Proof. exact (@lem2261217 term32 term32). Qed.
Lemma lem2261219 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261220 : term44 = term32.
Proof. exact (EQ_MP (@lem2261219) (@lem940073)). Qed.
Lemma lem2261221 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261222 : term42 = term38.
Proof. exact (MK_COMB (@lem2261221) (@lem2261220)). Qed.
Lemma lem2261223 : term41 = term38.
Proof. exact (TRANS (@lem2261218) (@lem2261222)). Qed.
Lemma lem2261224 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2261225 : term428 = term388.
Proof. exact (MK_COMB (@lem2261224) (@lem2261223)). Qed.
Lemma lem2261227 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261228 : term388 = term14.
Proof. exact (@lem2261227 term32). Qed.
Lemma lem2261229 : term428 = term14.
Proof. exact (TRANS (@lem2261225) (@lem2261228)). Qed.
Lemma lem2261230 : term14 = term428.
Proof. exact (SYM (@lem2261229)). Qed.
Lemma lem2261231 : term427 = term428.
Proof. exact (TRANS (@lem2261215) (@lem2261230)). Qed.
Lemma lem2261232 : term413 = term180.
Proof. exact (@lem2261182 (@lem2261231)). Qed.
Lemma lem2261233 : term412 = term180.
Proof. exact (TRANS (@lem2261148) (@lem2261232)). Qed.
Lemma lem2261235 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2261236 : term180 = term14.
Proof. exact (@lem2261235 term14). Qed.
Lemma lem2261237 : term412 = term14.
Proof. exact (TRANS (@lem2261233) (@lem2261236)). Qed.
Lemma lem2261238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261239 : term429 = term426.
Proof. exact (MK_COMB (@lem2261238) (@lem2261237)). Qed.
Lemma lem2261240 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2261241 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2261239) (@lem2261240 n)). Qed.
Lemma lem2261242 (n : nat) : (term433 n) = (term387 n).
Proof. exact (TRANS (@lem2261139 n) (@lem2261241 n)). Qed.
Lemma lem2261243 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2261244 (n : nat) : (term433 n) = term14.
Proof. exact (TRANS (@lem2261242 n) (@lem2261243 n)). Qed.
Lemma lem2261245 (x : real) (n : nat) : (term407 x n) = term435.
Proof. exact (MK_COMB (@lem2261138 x) (@lem2261244 n)). Qed.
Lemma lem2261246 (x : real) (n : nat) : (term406 x n) = term435.
Proof. exact (TRANS (@lem2261030 x n) (@lem2261245 x n)). Qed.
Lemma lem2261247 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2261248 (x : real) (n : nat) : (term406 x n) = term14.
Proof. exact (TRANS (@lem2261246 x n) (@lem2261247)). Qed.
Lemma lem2261249 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2261250 (x : real) (n : nat) : (term436 x n) = term437.
Proof. exact (MK_COMB (@lem2261249) (@lem2261248 x n)). Qed.
Lemma lem2261251 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2261252 (x : real) (n : nat) : (term405 x n) = term438.
Proof. exact (MK_COMB (@lem2261250 x n) (@lem2261251)). Qed.
Lemma lem2261253 (x : real) (n : nat) (h1 : term170 x n) : term438.
Proof. exact (EQ_MP (@lem2261252 x n) (@lem2261029 x n h1)). Qed.
Lemma lem2261255 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2261256 : term438 = term439.
Proof. exact (@lem2261255 term14 term14). Qed.
Lemma lem2261258 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261259 : term14 = term180.
Proof. exact (@lem2261258 (NUMERAL 0)). Qed.
Lemma lem2261261 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261262 : term14 = term180.
Proof. exact (@lem2261261 (NUMERAL 0)). Qed.
Lemma lem2261263 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2261264 : term378 = term379.
Proof. exact (MK_COMB (@lem2261263) (@lem2261262)). Qed.
Lemma lem2261265 : term439 = term440.
Proof. exact (MK_COMB (@lem2261264) (@lem2261259)). Qed.
Lemma lem2261266 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2261268 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261269 : term377 = term383.
Proof. exact (@lem2261268 (NUMERAL 0) term32). Qed.
Lemma lem2261270 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261271 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261272 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261271 h1) (fun h1 : term383 = True => @lem2261270)). Qed.
Lemma lem2261273 : term383 = True.
Proof. exact (EQ_MP (@lem2261272) (@lem2261270)). Qed.
Lemma lem2261274 : term377 = True.
Proof. exact (TRANS (@lem2261269) (@lem2261273)). Qed.
Lemma lem2261275 : True = term377.
Proof. exact (SYM (@lem2261274)). Qed.
Lemma lem2261276 : term377.
Proof. exact (EQ_MP (@lem2261275) (@lem0)). Qed.
Lemma lem2261277 : term442.
Proof. exact (@lem2261266 (@lem2261276)). Qed.
Lemma lem2261279 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261280 : term377 = term383.
Proof. exact (@lem2261279 (NUMERAL 0) term32). Qed.
Lemma lem2261281 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261282 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261283 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261282 h1) (fun h1 : term383 = True => @lem2261281)). Qed.
Lemma lem2261284 : term383 = True.
Proof. exact (EQ_MP (@lem2261283) (@lem2261281)). Qed.
Lemma lem2261285 : term377 = True.
Proof. exact (TRANS (@lem2261280) (@lem2261284)). Qed.
Lemma lem2261286 : True = term377.
Proof. exact (SYM (@lem2261285)). Qed.
Lemma lem2261287 : term377.
Proof. exact (EQ_MP (@lem2261286) (@lem0)). Qed.
Lemma lem2261288 : term440 = term443.
Proof. exact (@lem2261277 (@lem2261287)). Qed.
Lemma lem2261290 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261291 : term388 = term14.
Proof. exact (@lem2261290 term32). Qed.
Lemma lem2261293 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261294 : term388 = term14.
Proof. exact (@lem2261293 term32). Qed.
Lemma lem2261295 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2261296 : term389 = term378.
Proof. exact (MK_COMB (@lem2261295) (@lem2261294)). Qed.
Lemma lem2261297 : term443 = term439.
Proof. exact (MK_COMB (@lem2261296) (@lem2261291)). Qed.
Lemma lem2261299 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261300 : term439 = term444.
Proof. exact (@lem2261299 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2261301 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2261302 : term439 = False.
Proof. exact (TRANS (@lem2261300) (@lem2261301)). Qed.
Lemma lem2261303 : term443 = False.
Proof. exact (TRANS (@lem2261297) (@lem2261302)). Qed.
Lemma lem2261304 : term440 = False.
Proof. exact (TRANS (@lem2261288) (@lem2261303)). Qed.
Lemma lem2261305 : term439 = False.
Proof. exact (TRANS (@lem2261265) (@lem2261304)). Qed.
Lemma lem2261306 : term438 = False.
Proof. exact (TRANS (@lem2261256) (@lem2261305)). Qed.
Lemma lem2261307 (x : real) (n : nat) (h1 : term170 x n) : False.
Proof. exact (EQ_MP (@lem2261306) (@lem2261253 x n h1)). Qed.
Lemma lem2261308 (x : real) (n : nat) (h1 : term227 x n) : term227 x n.
Proof. exact (h1). Qed.
Lemma lem2261309 (x : real) (n : nat) (h1 : term227 x n) : term225 x n.
Proof. exact (proj2 (@lem2261308 x n h1)). Qed.
Lemma lem2261311 (x : real) (n : nat) (h1 : term227 x n) : term150 x n.
Proof. exact (proj2 (@lem2261309 x n h1)). Qed.
Lemma lem2261312 (x : real) (n : nat) (h1 : term227 x n) : (term76 x n) = term14.
Proof. exact (proj1 (@lem2261309 x n h1)). Qed.
Lemma lem2261313 (x : real) (n : nat) (h1 : term227 x n) : term85 x n.
Proof. exact (proj2 (@lem2261311 x n h1)). Qed.
Lemma lem2261317 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2261318 : term376 = term377.
Proof. exact (@lem2261317 term14 term38). Qed.
Lemma lem2261320 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261321 : term38 = term48.
Proof. exact (@lem2261320 term32). Qed.
Lemma lem2261323 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261324 : term14 = term180.
Proof. exact (@lem2261323 (NUMERAL 0)). Qed.
Lemma lem2261325 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2261326 : term378 = term379.
Proof. exact (MK_COMB (@lem2261325) (@lem2261324)). Qed.
Lemma lem2261327 : term377 = term380.
Proof. exact (MK_COMB (@lem2261326) (@lem2261321)). Qed.
Lemma lem2261328 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2261330 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261331 : term377 = term383.
Proof. exact (@lem2261330 (NUMERAL 0) term32). Qed.
Lemma lem2261332 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261333 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261334 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261333 h1) (fun h1 : term383 = True => @lem2261332)). Qed.
Lemma lem2261335 : term383 = True.
Proof. exact (EQ_MP (@lem2261334) (@lem2261332)). Qed.
Lemma lem2261336 : term377 = True.
Proof. exact (TRANS (@lem2261331) (@lem2261335)). Qed.
Lemma lem2261337 : True = term377.
Proof. exact (SYM (@lem2261336)). Qed.
Lemma lem2261338 : term377.
Proof. exact (EQ_MP (@lem2261337) (@lem0)). Qed.
Lemma lem2261339 : term385.
Proof. exact (@lem2261328 (@lem2261338)). Qed.
Lemma lem2261341 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261342 : term377 = term383.
Proof. exact (@lem2261341 (NUMERAL 0) term32). Qed.
Lemma lem2261343 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261344 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261345 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261344 h1) (fun h1 : term383 = True => @lem2261343)). Qed.
Lemma lem2261346 : term383 = True.
Proof. exact (EQ_MP (@lem2261345) (@lem2261343)). Qed.
Lemma lem2261347 : term377 = True.
Proof. exact (TRANS (@lem2261342) (@lem2261346)). Qed.
Lemma lem2261348 : True = term377.
Proof. exact (SYM (@lem2261347)). Qed.
Lemma lem2261349 : term377.
Proof. exact (EQ_MP (@lem2261348) (@lem0)). Qed.
Lemma lem2261350 : term380 = term386.
Proof. exact (@lem2261339 (@lem2261349)). Qed.
Lemma lem2261352 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261353 : term41 = term42.
Proof. exact (@lem2261352 term32 term32). Qed.
Lemma lem2261354 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261355 : term44 = term32.
Proof. exact (EQ_MP (@lem2261354) (@lem940073)). Qed.
Lemma lem2261356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261357 : term42 = term38.
Proof. exact (MK_COMB (@lem2261356) (@lem2261355)). Qed.
Lemma lem2261358 : term41 = term38.
Proof. exact (TRANS (@lem2261353) (@lem2261357)). Qed.
Lemma lem2261360 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261361 : term388 = term14.
Proof. exact (@lem2261360 term32). Qed.
Lemma lem2261362 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2261363 : term389 = term378.
Proof. exact (MK_COMB (@lem2261362) (@lem2261361)). Qed.
Lemma lem2261364 : term386 = term377.
Proof. exact (MK_COMB (@lem2261363) (@lem2261358)). Qed.
Lemma lem2261366 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261367 : term377 = term383.
Proof. exact (@lem2261366 (NUMERAL 0) term32). Qed.
Lemma lem2261368 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261369 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261370 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261369 h1) (fun h1 : term383 = True => @lem2261368)). Qed.
Lemma lem2261371 : term383 = True.
Proof. exact (EQ_MP (@lem2261370) (@lem2261368)). Qed.
Lemma lem2261372 : term377 = True.
Proof. exact (TRANS (@lem2261367) (@lem2261371)). Qed.
Lemma lem2261373 : term386 = True.
Proof. exact (TRANS (@lem2261364) (@lem2261372)). Qed.
Lemma lem2261374 : term380 = True.
Proof. exact (TRANS (@lem2261350) (@lem2261373)). Qed.
Lemma lem2261375 : term377 = True.
Proof. exact (TRANS (@lem2261327) (@lem2261374)). Qed.
Lemma lem2261376 : term376 = True.
Proof. exact (TRANS (@lem2261318) (@lem2261375)). Qed.
Lemma lem2261377 : True = term376.
Proof. exact (SYM (@lem2261376)). Qed.
Lemma lem2261378 : term376.
Proof. exact (EQ_MP (@lem2261377) (@lem0)). Qed.
Lemma lem2261379 (x : real) (n : nat) (h1 : term227 x n) : term445 x n.
Proof. exact (conj (@lem2261378) (@lem2261313 x n h1)). Qed.
Lemma lem2261381 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2261382 (x : real) (n : nat) : term446 x n.
Proof. exact (@lem2261381 term38 (term72 x n)). Qed.
Lemma lem2261383 (x : real) (n : nat) (h1 : term227 x n) : term447 x n.
Proof. exact (@lem2261382 x n (@lem2261379 x n h1)). Qed.
Lemma lem2261384 (x : real) (n : nat) : (term448 x n) = (term72 x n).
Proof. exact (@lem1982733 (term72 x n)). Qed.
Lemma lem2261385 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2261386 (x : real) (n : nat) : (term449 x n) = (term83 x n).
Proof. exact (MK_COMB (@lem2261385) (@lem2261384 x n)). Qed.
Lemma lem2261387 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2261388 (x : real) (n : nat) : (term447 x n) = (term85 x n).
Proof. exact (MK_COMB (@lem2261386 x n) (@lem2261387)). Qed.
Lemma lem2261389 (x : real) (n : nat) (h1 : term227 x n) : term85 x n.
Proof. exact (EQ_MP (@lem2261388 x n) (@lem2261383 x n h1)). Qed.
Lemma lem2261391 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2261392 (x : real) (n : nat) : term450 x n.
Proof. exact (@lem2261391 (term76 x n)). Qed.
Lemma lem2261393 (x : real) (n : nat) (h1 : term227 x n) : term451 x n.
Proof. exact (@lem2261392 x n (@lem2261312 x n h1)). Qed.
Lemma lem2261394 (x : real) (n : nat) (h1 : term227 x n) : term452 x n.
Proof. exact (@lem2261393 x n h1 term38). Qed.
Lemma lem2261395 (x : real) (n : nat) : (term452 x n) = ((term453 x n) = term14).
Proof. exact (eq_refl (term452 x n)). Qed.
Lemma lem2261396 (x : real) (n : nat) (h1 : term227 x n) : (term453 x n) = term14.
Proof. exact (EQ_MP (@lem2261395 x n) (@lem2261394 x n h1)). Qed.
Lemma lem2261397 (x : real) (n : nat) : (term453 x n) = (term76 x n).
Proof. exact (@lem1982733 (term76 x n)). Qed.
Lemma lem2261398 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2261399 (x : real) (n : nat) : (term454 x n) = (term222 x n).
Proof. exact (MK_COMB (@lem2261398) (@lem2261397 x n)). Qed.
Lemma lem2261400 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2261401 (x : real) (n : nat) : ((term453 x n) = term14) = ((term76 x n) = term14).
Proof. exact (MK_COMB (@lem2261399 x n) (@lem2261400)). Qed.
Lemma lem2261402 (x : real) (n : nat) (h1 : term227 x n) : (term76 x n) = term14.
Proof. exact (EQ_MP (@lem2261401 x n) (@lem2261396 x n h1)). Qed.
Lemma lem2261403 (x : real) (n : nat) (h1 : term227 x n) : term455 x n.
Proof. exact (conj (@lem2261402 x n h1) (@lem2261389 x n h1)). Qed.
Lemma lem2261405 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2261406 (x : real) (n : nat) : term456 x n.
Proof. exact (@lem2261405 (term76 x n) (term72 x n)). Qed.
Lemma lem2261407 (x : real) (n : nat) (h1 : term227 x n) : term457 x n.
Proof. exact (@lem2261406 x n (@lem2261403 x n h1)). Qed.
Lemma lem2261408 (x : real) (n : nat) : (term458 x n) = (term459 x n).
Proof. exact (@lem1982753 (term208 x) x (term27 n) (real_of_num n)). Qed.
Lemma lem2261409 (x : real) : (term408 x) = (term409 x).
Proof. exact (@lem1982713 term26 x). Qed.
Lemma lem2261411 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261412 : term38 = term48.
Proof. exact (@lem2261411 term32). Qed.
Lemma lem2261414 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2261415 : term26 = term31.
Proof. exact (@lem2261414 term32). Qed.
Lemma lem2261416 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261417 : term410 = term411.
Proof. exact (MK_COMB (@lem2261416) (@lem2261415)). Qed.
Lemma lem2261418 : term412 = term413.
Proof. exact (MK_COMB (@lem2261417) (@lem2261412)). Qed.
Lemma lem2261419 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2261421 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261422 : term377 = term383.
Proof. exact (@lem2261421 (NUMERAL 0) term32). Qed.
Lemma lem2261423 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261424 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261425 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261424 h1) (fun h1 : term383 = True => @lem2261423)). Qed.
Lemma lem2261426 : term383 = True.
Proof. exact (EQ_MP (@lem2261425) (@lem2261423)). Qed.
Lemma lem2261427 : term377 = True.
Proof. exact (TRANS (@lem2261422) (@lem2261426)). Qed.
Lemma lem2261428 : True = term377.
Proof. exact (SYM (@lem2261427)). Qed.
Lemma lem2261429 : term377.
Proof. exact (EQ_MP (@lem2261428) (@lem0)). Qed.
Lemma lem2261430 : term415.
Proof. exact (@lem2261419 (@lem2261429)). Qed.
Lemma lem2261432 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261433 : term377 = term383.
Proof. exact (@lem2261432 (NUMERAL 0) term32). Qed.
Lemma lem2261434 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261435 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261436 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261435 h1) (fun h1 : term383 = True => @lem2261434)). Qed.
Lemma lem2261437 : term383 = True.
Proof. exact (EQ_MP (@lem2261436) (@lem2261434)). Qed.
Lemma lem2261438 : term377 = True.
Proof. exact (TRANS (@lem2261433) (@lem2261437)). Qed.
Lemma lem2261439 : True = term377.
Proof. exact (SYM (@lem2261438)). Qed.
Lemma lem2261440 : term377.
Proof. exact (EQ_MP (@lem2261439) (@lem0)). Qed.
Lemma lem2261441 : term416.
Proof. exact (@lem2261430 (@lem2261440)). Qed.
Lemma lem2261443 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261444 : term377 = term383.
Proof. exact (@lem2261443 (NUMERAL 0) term32). Qed.
Lemma lem2261445 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261446 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261447 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261446 h1) (fun h1 : term383 = True => @lem2261445)). Qed.
Lemma lem2261448 : term383 = True.
Proof. exact (EQ_MP (@lem2261447) (@lem2261445)). Qed.
Lemma lem2261449 : term377 = True.
Proof. exact (TRANS (@lem2261444) (@lem2261448)). Qed.
Lemma lem2261450 : True = term377.
Proof. exact (SYM (@lem2261449)). Qed.
Lemma lem2261451 : term377.
Proof. exact (EQ_MP (@lem2261450) (@lem0)). Qed.
Lemma lem2261452 : term417.
Proof. exact (@lem2261441 (@lem2261451)). Qed.
Lemma lem2261454 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261455 : term41 = term42.
Proof. exact (@lem2261454 term32 term32). Qed.
Lemma lem2261456 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261457 : term44 = term32.
Proof. exact (EQ_MP (@lem2261456) (@lem940073)). Qed.
Lemma lem2261458 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261459 : term42 = term38.
Proof. exact (MK_COMB (@lem2261458) (@lem2261457)). Qed.
Lemma lem2261460 : term41 = term38.
Proof. exact (TRANS (@lem2261455) (@lem2261459)). Qed.
Lemma lem2261462 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2261463 : term420 = term421.
Proof. exact (@lem2261462 term32 term32). Qed.
Lemma lem2261464 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261465 : term44 = term32.
Proof. exact (EQ_MP (@lem2261464) (@lem940073)). Qed.
Lemma lem2261466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261467 : term42 = term38.
Proof. exact (MK_COMB (@lem2261466) (@lem2261465)). Qed.
Lemma lem2261468 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2261469 : term421 = term26.
Proof. exact (MK_COMB (@lem2261468) (@lem2261467)). Qed.
Lemma lem2261470 : term420 = term26.
Proof. exact (TRANS (@lem2261463) (@lem2261469)). Qed.
Lemma lem2261471 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261472 : term422 = term410.
Proof. exact (MK_COMB (@lem2261471) (@lem2261470)). Qed.
Lemma lem2261473 : term423 = term412.
Proof. exact (MK_COMB (@lem2261472) (@lem2261460)). Qed.
Lemma lem2261475 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2261476 : term412 = term14.
Proof. exact (@lem2261475 term32). Qed.
Lemma lem2261477 : term423 = term14.
Proof. exact (TRANS (@lem2261473) (@lem2261476)). Qed.
Lemma lem2261478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261479 : term425 = term426.
Proof. exact (MK_COMB (@lem2261478) (@lem2261477)). Qed.
Lemma lem2261480 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2261481 : term427 = term388.
Proof. exact (MK_COMB (@lem2261479) (@lem2261480)). Qed.
Lemma lem2261483 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261484 : term388 = term14.
Proof. exact (@lem2261483 term32). Qed.
Lemma lem2261485 : term427 = term14.
Proof. exact (TRANS (@lem2261481) (@lem2261484)). Qed.
Lemma lem2261487 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261488 : term41 = term42.
Proof. exact (@lem2261487 term32 term32). Qed.
Lemma lem2261489 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261490 : term44 = term32.
Proof. exact (EQ_MP (@lem2261489) (@lem940073)). Qed.
Lemma lem2261491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261492 : term42 = term38.
Proof. exact (MK_COMB (@lem2261491) (@lem2261490)). Qed.
Lemma lem2261493 : term41 = term38.
Proof. exact (TRANS (@lem2261488) (@lem2261492)). Qed.
Lemma lem2261494 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2261495 : term428 = term388.
Proof. exact (MK_COMB (@lem2261494) (@lem2261493)). Qed.
Lemma lem2261497 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261498 : term388 = term14.
Proof. exact (@lem2261497 term32). Qed.
Lemma lem2261499 : term428 = term14.
Proof. exact (TRANS (@lem2261495) (@lem2261498)). Qed.
Lemma lem2261500 : term14 = term428.
Proof. exact (SYM (@lem2261499)). Qed.
Lemma lem2261501 : term427 = term428.
Proof. exact (TRANS (@lem2261485) (@lem2261500)). Qed.
Lemma lem2261502 : term413 = term180.
Proof. exact (@lem2261452 (@lem2261501)). Qed.
Lemma lem2261503 : term412 = term180.
Proof. exact (TRANS (@lem2261418) (@lem2261502)). Qed.
Lemma lem2261505 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2261506 : term180 = term14.
Proof. exact (@lem2261505 term14). Qed.
Lemma lem2261507 : term412 = term14.
Proof. exact (TRANS (@lem2261503) (@lem2261506)). Qed.
Lemma lem2261508 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261509 : term429 = term426.
Proof. exact (MK_COMB (@lem2261508) (@lem2261507)). Qed.
Lemma lem2261510 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2261511 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2261509) (@lem2261510 x)). Qed.
Lemma lem2261512 (x : real) : (term408 x) = (term430 x).
Proof. exact (TRANS (@lem2261409 x) (@lem2261511 x)). Qed.
Lemma lem2261513 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2261514 (x : real) : (term408 x) = term14.
Proof. exact (TRANS (@lem2261512 x) (@lem2261513 x)). Qed.
Lemma lem2261515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261516 (x : real) : (term431 x) = term432.
Proof. exact (MK_COMB (@lem2261515) (@lem2261514 x)). Qed.
Lemma lem2261517 (n : nat) : (term460 n) = (term434 n).
Proof. exact (@lem1982713 term26 (real_of_num n)). Qed.
Lemma lem2261519 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261520 : term38 = term48.
Proof. exact (@lem2261519 term32). Qed.
Lemma lem2261522 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2261523 : term26 = term31.
Proof. exact (@lem2261522 term32). Qed.
Lemma lem2261524 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261525 : term410 = term411.
Proof. exact (MK_COMB (@lem2261524) (@lem2261523)). Qed.
Lemma lem2261526 : term412 = term413.
Proof. exact (MK_COMB (@lem2261525) (@lem2261520)). Qed.
Lemma lem2261527 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2261529 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261530 : term377 = term383.
Proof. exact (@lem2261529 (NUMERAL 0) term32). Qed.
Lemma lem2261531 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261532 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261533 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261532 h1) (fun h1 : term383 = True => @lem2261531)). Qed.
Lemma lem2261534 : term383 = True.
Proof. exact (EQ_MP (@lem2261533) (@lem2261531)). Qed.
Lemma lem2261535 : term377 = True.
Proof. exact (TRANS (@lem2261530) (@lem2261534)). Qed.
Lemma lem2261536 : True = term377.
Proof. exact (SYM (@lem2261535)). Qed.
Lemma lem2261537 : term377.
Proof. exact (EQ_MP (@lem2261536) (@lem0)). Qed.
Lemma lem2261538 : term415.
Proof. exact (@lem2261527 (@lem2261537)). Qed.
Lemma lem2261540 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261541 : term377 = term383.
Proof. exact (@lem2261540 (NUMERAL 0) term32). Qed.
Lemma lem2261542 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261543 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261544 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261543 h1) (fun h1 : term383 = True => @lem2261542)). Qed.
Lemma lem2261545 : term383 = True.
Proof. exact (EQ_MP (@lem2261544) (@lem2261542)). Qed.
Lemma lem2261546 : term377 = True.
Proof. exact (TRANS (@lem2261541) (@lem2261545)). Qed.
Lemma lem2261547 : True = term377.
Proof. exact (SYM (@lem2261546)). Qed.
Lemma lem2261548 : term377.
Proof. exact (EQ_MP (@lem2261547) (@lem0)). Qed.
Lemma lem2261549 : term416.
Proof. exact (@lem2261538 (@lem2261548)). Qed.
Lemma lem2261551 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261552 : term377 = term383.
Proof. exact (@lem2261551 (NUMERAL 0) term32). Qed.
Lemma lem2261553 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261554 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261555 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261554 h1) (fun h1 : term383 = True => @lem2261553)). Qed.
Lemma lem2261556 : term383 = True.
Proof. exact (EQ_MP (@lem2261555) (@lem2261553)). Qed.
Lemma lem2261557 : term377 = True.
Proof. exact (TRANS (@lem2261552) (@lem2261556)). Qed.
Lemma lem2261558 : True = term377.
Proof. exact (SYM (@lem2261557)). Qed.
Lemma lem2261559 : term377.
Proof. exact (EQ_MP (@lem2261558) (@lem0)). Qed.
Lemma lem2261560 : term417.
Proof. exact (@lem2261549 (@lem2261559)). Qed.
Lemma lem2261562 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261563 : term41 = term42.
Proof. exact (@lem2261562 term32 term32). Qed.
Lemma lem2261564 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261565 : term44 = term32.
Proof. exact (EQ_MP (@lem2261564) (@lem940073)). Qed.
Lemma lem2261566 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261567 : term42 = term38.
Proof. exact (MK_COMB (@lem2261566) (@lem2261565)). Qed.
Lemma lem2261568 : term41 = term38.
Proof. exact (TRANS (@lem2261563) (@lem2261567)). Qed.
Lemma lem2261570 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2261571 : term420 = term421.
Proof. exact (@lem2261570 term32 term32). Qed.
Lemma lem2261572 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261573 : term44 = term32.
Proof. exact (EQ_MP (@lem2261572) (@lem940073)). Qed.
Lemma lem2261574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261575 : term42 = term38.
Proof. exact (MK_COMB (@lem2261574) (@lem2261573)). Qed.
Lemma lem2261576 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2261577 : term421 = term26.
Proof. exact (MK_COMB (@lem2261576) (@lem2261575)). Qed.
Lemma lem2261578 : term420 = term26.
Proof. exact (TRANS (@lem2261571) (@lem2261577)). Qed.
Lemma lem2261579 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261580 : term422 = term410.
Proof. exact (MK_COMB (@lem2261579) (@lem2261578)). Qed.
Lemma lem2261581 : term423 = term412.
Proof. exact (MK_COMB (@lem2261580) (@lem2261568)). Qed.
Lemma lem2261583 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2261584 : term412 = term14.
Proof. exact (@lem2261583 term32). Qed.
Lemma lem2261585 : term423 = term14.
Proof. exact (TRANS (@lem2261581) (@lem2261584)). Qed.
Lemma lem2261586 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261587 : term425 = term426.
Proof. exact (MK_COMB (@lem2261586) (@lem2261585)). Qed.
Lemma lem2261588 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2261589 : term427 = term388.
Proof. exact (MK_COMB (@lem2261587) (@lem2261588)). Qed.
Lemma lem2261591 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261592 : term388 = term14.
Proof. exact (@lem2261591 term32). Qed.
Lemma lem2261593 : term427 = term14.
Proof. exact (TRANS (@lem2261589) (@lem2261592)). Qed.
Lemma lem2261595 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261596 : term41 = term42.
Proof. exact (@lem2261595 term32 term32). Qed.
Lemma lem2261597 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261598 : term44 = term32.
Proof. exact (EQ_MP (@lem2261597) (@lem940073)). Qed.
Lemma lem2261599 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261600 : term42 = term38.
Proof. exact (MK_COMB (@lem2261599) (@lem2261598)). Qed.
Lemma lem2261601 : term41 = term38.
Proof. exact (TRANS (@lem2261596) (@lem2261600)). Qed.
Lemma lem2261602 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2261603 : term428 = term388.
Proof. exact (MK_COMB (@lem2261602) (@lem2261601)). Qed.
Lemma lem2261605 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261606 : term388 = term14.
Proof. exact (@lem2261605 term32). Qed.
Lemma lem2261607 : term428 = term14.
Proof. exact (TRANS (@lem2261603) (@lem2261606)). Qed.
Lemma lem2261608 : term14 = term428.
Proof. exact (SYM (@lem2261607)). Qed.
Lemma lem2261609 : term427 = term428.
Proof. exact (TRANS (@lem2261593) (@lem2261608)). Qed.
Lemma lem2261610 : term413 = term180.
Proof. exact (@lem2261560 (@lem2261609)). Qed.
Lemma lem2261611 : term412 = term180.
Proof. exact (TRANS (@lem2261526) (@lem2261610)). Qed.
Lemma lem2261613 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2261614 : term180 = term14.
Proof. exact (@lem2261613 term14). Qed.
Lemma lem2261615 : term412 = term14.
Proof. exact (TRANS (@lem2261611) (@lem2261614)). Qed.
Lemma lem2261616 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261617 : term429 = term426.
Proof. exact (MK_COMB (@lem2261616) (@lem2261615)). Qed.
Lemma lem2261618 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2261619 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2261617) (@lem2261618 n)). Qed.
Lemma lem2261620 (n : nat) : (term460 n) = (term387 n).
Proof. exact (TRANS (@lem2261517 n) (@lem2261619 n)). Qed.
Lemma lem2261621 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2261622 (n : nat) : (term460 n) = term14.
Proof. exact (TRANS (@lem2261620 n) (@lem2261621 n)). Qed.
Lemma lem2261623 (x : real) (n : nat) : (term459 x n) = term435.
Proof. exact (MK_COMB (@lem2261516 x) (@lem2261622 n)). Qed.
Lemma lem2261624 (x : real) (n : nat) : (term458 x n) = term435.
Proof. exact (TRANS (@lem2261408 x n) (@lem2261623 x n)). Qed.
Lemma lem2261625 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2261626 (x : real) (n : nat) : (term458 x n) = term14.
Proof. exact (TRANS (@lem2261624 x n) (@lem2261625)). Qed.
Lemma lem2261627 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2261628 (x : real) (n : nat) : (term461 x n) = term437.
Proof. exact (MK_COMB (@lem2261627) (@lem2261626 x n)). Qed.
Lemma lem2261629 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2261630 (x : real) (n : nat) : (term457 x n) = term438.
Proof. exact (MK_COMB (@lem2261628 x n) (@lem2261629)). Qed.
Lemma lem2261631 (x : real) (n : nat) (h1 : term227 x n) : term438.
Proof. exact (EQ_MP (@lem2261630 x n) (@lem2261407 x n h1)). Qed.
Lemma lem2261633 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2261634 : term438 = term439.
Proof. exact (@lem2261633 term14 term14). Qed.
Lemma lem2261636 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261637 : term14 = term180.
Proof. exact (@lem2261636 (NUMERAL 0)). Qed.
Lemma lem2261639 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261640 : term14 = term180.
Proof. exact (@lem2261639 (NUMERAL 0)). Qed.
Lemma lem2261641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2261642 : term378 = term379.
Proof. exact (MK_COMB (@lem2261641) (@lem2261640)). Qed.
Lemma lem2261643 : term439 = term440.
Proof. exact (MK_COMB (@lem2261642) (@lem2261637)). Qed.
Lemma lem2261644 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2261646 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261647 : term377 = term383.
Proof. exact (@lem2261646 (NUMERAL 0) term32). Qed.
Lemma lem2261648 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261649 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261650 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261649 h1) (fun h1 : term383 = True => @lem2261648)). Qed.
Lemma lem2261651 : term383 = True.
Proof. exact (EQ_MP (@lem2261650) (@lem2261648)). Qed.
Lemma lem2261652 : term377 = True.
Proof. exact (TRANS (@lem2261647) (@lem2261651)). Qed.
Lemma lem2261653 : True = term377.
Proof. exact (SYM (@lem2261652)). Qed.
Lemma lem2261654 : term377.
Proof. exact (EQ_MP (@lem2261653) (@lem0)). Qed.
Lemma lem2261655 : term442.
Proof. exact (@lem2261644 (@lem2261654)). Qed.
Lemma lem2261657 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261658 : term377 = term383.
Proof. exact (@lem2261657 (NUMERAL 0) term32). Qed.
Lemma lem2261659 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261660 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261661 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261660 h1) (fun h1 : term383 = True => @lem2261659)). Qed.
Lemma lem2261662 : term383 = True.
Proof. exact (EQ_MP (@lem2261661) (@lem2261659)). Qed.
Lemma lem2261663 : term377 = True.
Proof. exact (TRANS (@lem2261658) (@lem2261662)). Qed.
Lemma lem2261664 : True = term377.
Proof. exact (SYM (@lem2261663)). Qed.
Lemma lem2261665 : term377.
Proof. exact (EQ_MP (@lem2261664) (@lem0)). Qed.
Lemma lem2261666 : term440 = term443.
Proof. exact (@lem2261655 (@lem2261665)). Qed.
Lemma lem2261668 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261669 : term388 = term14.
Proof. exact (@lem2261668 term32). Qed.
Lemma lem2261671 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261672 : term388 = term14.
Proof. exact (@lem2261671 term32). Qed.
Lemma lem2261673 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2261674 : term389 = term378.
Proof. exact (MK_COMB (@lem2261673) (@lem2261672)). Qed.
Lemma lem2261675 : term443 = term439.
Proof. exact (MK_COMB (@lem2261674) (@lem2261669)). Qed.
Lemma lem2261677 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261678 : term439 = term444.
Proof. exact (@lem2261677 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2261679 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2261680 : term439 = False.
Proof. exact (TRANS (@lem2261678) (@lem2261679)). Qed.
Lemma lem2261681 : term443 = False.
Proof. exact (TRANS (@lem2261675) (@lem2261680)). Qed.
Lemma lem2261682 : term440 = False.
Proof. exact (TRANS (@lem2261666) (@lem2261681)). Qed.
Lemma lem2261683 : term439 = False.
Proof. exact (TRANS (@lem2261643) (@lem2261682)). Qed.
Lemma lem2261684 : term438 = False.
Proof. exact (TRANS (@lem2261634) (@lem2261683)). Qed.
Lemma lem2261685 (x : real) (n : nat) (h1 : term227 x n) : False.
Proof. exact (EQ_MP (@lem2261684) (@lem2261631 x n h1)). Qed.
Lemma lem2261686 (x : real) (n : nat) (h1 : term228 x n) : False.
Proof. exact (or_elim (@lem2260881 x n h1) (fun h0 : term170 x n => @lem2261307 x n h0) (fun h0 : term227 x n => @lem2261685 x n h0)). Qed.
Lemma lem2261687 (x : real) (n : nat) (h1 : term254 x n) : term254 x n.
Proof. exact (h1). Qed.
Lemma lem2261688 (x : real) (n : nat) (h1 : term240 x n) : term240 x n.
Proof. exact (h1). Qed.
Lemma lem2261689 (x : real) (n : nat) (h1 : term240 x n) : term238 x n.
Proof. exact (proj2 (@lem2261688 x n h1)). Qed.
Lemma lem2261691 (x : real) (n : nat) (h1 : term240 x n) : term151 x n.
Proof. exact (proj2 (@lem2261689 x n h1)). Qed.
Lemma lem2261692 (x : real) (n : nat) (h1 : term240 x n) : (term21 x n) = term14.
Proof. exact (proj1 (@lem2261689 x n h1)). Qed.
Lemma lem2261694 (x : real) (n : nat) (h1 : term240 x n) : term59 x n.
Proof. exact (proj1 (@lem2261691 x n h1)). Qed.
Lemma lem2261697 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2261698 : term376 = term377.
Proof. exact (@lem2261697 term14 term38). Qed.
Lemma lem2261700 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261701 : term38 = term48.
Proof. exact (@lem2261700 term32). Qed.
Lemma lem2261703 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261704 : term14 = term180.
Proof. exact (@lem2261703 (NUMERAL 0)). Qed.
Lemma lem2261705 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2261706 : term378 = term379.
Proof. exact (MK_COMB (@lem2261705) (@lem2261704)). Qed.
Lemma lem2261707 : term377 = term380.
Proof. exact (MK_COMB (@lem2261706) (@lem2261701)). Qed.
Lemma lem2261708 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2261710 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261711 : term377 = term383.
Proof. exact (@lem2261710 (NUMERAL 0) term32). Qed.
Lemma lem2261712 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261713 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261714 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261713 h1) (fun h1 : term383 = True => @lem2261712)). Qed.
Lemma lem2261715 : term383 = True.
Proof. exact (EQ_MP (@lem2261714) (@lem2261712)). Qed.
Lemma lem2261716 : term377 = True.
Proof. exact (TRANS (@lem2261711) (@lem2261715)). Qed.
Lemma lem2261717 : True = term377.
Proof. exact (SYM (@lem2261716)). Qed.
Lemma lem2261718 : term377.
Proof. exact (EQ_MP (@lem2261717) (@lem0)). Qed.
Lemma lem2261719 : term385.
Proof. exact (@lem2261708 (@lem2261718)). Qed.
Lemma lem2261721 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261722 : term377 = term383.
Proof. exact (@lem2261721 (NUMERAL 0) term32). Qed.
Lemma lem2261723 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261724 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261725 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261724 h1) (fun h1 : term383 = True => @lem2261723)). Qed.
Lemma lem2261726 : term383 = True.
Proof. exact (EQ_MP (@lem2261725) (@lem2261723)). Qed.
Lemma lem2261727 : term377 = True.
Proof. exact (TRANS (@lem2261722) (@lem2261726)). Qed.
Lemma lem2261728 : True = term377.
Proof. exact (SYM (@lem2261727)). Qed.
Lemma lem2261729 : term377.
Proof. exact (EQ_MP (@lem2261728) (@lem0)). Qed.
Lemma lem2261730 : term380 = term386.
Proof. exact (@lem2261719 (@lem2261729)). Qed.
Lemma lem2261732 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261733 : term41 = term42.
Proof. exact (@lem2261732 term32 term32). Qed.
Lemma lem2261734 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261735 : term44 = term32.
Proof. exact (EQ_MP (@lem2261734) (@lem940073)). Qed.
Lemma lem2261736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261737 : term42 = term38.
Proof. exact (MK_COMB (@lem2261736) (@lem2261735)). Qed.
Lemma lem2261738 : term41 = term38.
Proof. exact (TRANS (@lem2261733) (@lem2261737)). Qed.
Lemma lem2261740 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261741 : term388 = term14.
Proof. exact (@lem2261740 term32). Qed.
Lemma lem2261742 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2261743 : term389 = term378.
Proof. exact (MK_COMB (@lem2261742) (@lem2261741)). Qed.
Lemma lem2261744 : term386 = term377.
Proof. exact (MK_COMB (@lem2261743) (@lem2261738)). Qed.
Lemma lem2261746 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261747 : term377 = term383.
Proof. exact (@lem2261746 (NUMERAL 0) term32). Qed.
Lemma lem2261748 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261749 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261750 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261749 h1) (fun h1 : term383 = True => @lem2261748)). Qed.
Lemma lem2261751 : term383 = True.
Proof. exact (EQ_MP (@lem2261750) (@lem2261748)). Qed.
Lemma lem2261752 : term377 = True.
Proof. exact (TRANS (@lem2261747) (@lem2261751)). Qed.
Lemma lem2261753 : term386 = True.
Proof. exact (TRANS (@lem2261744) (@lem2261752)). Qed.
Lemma lem2261754 : term380 = True.
Proof. exact (TRANS (@lem2261730) (@lem2261753)). Qed.
Lemma lem2261755 : term377 = True.
Proof. exact (TRANS (@lem2261707) (@lem2261754)). Qed.
Lemma lem2261756 : term376 = True.
Proof. exact (TRANS (@lem2261698) (@lem2261755)). Qed.
Lemma lem2261757 : True = term376.
Proof. exact (SYM (@lem2261756)). Qed.
Lemma lem2261758 : term376.
Proof. exact (EQ_MP (@lem2261757) (@lem0)). Qed.
Lemma lem2261759 (x : real) (n : nat) (h1 : term240 x n) : term462 x n.
Proof. exact (conj (@lem2261758) (@lem2261694 x n h1)). Qed.
Lemma lem2261761 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2261762 (x : real) (n : nat) : term463 x n.
Proof. exact (@lem2261761 term38 (term54 x n)). Qed.
Lemma lem2261763 (x : real) (n : nat) (h1 : term240 x n) : term464 x n.
Proof. exact (@lem2261762 x n (@lem2261759 x n h1)). Qed.
Lemma lem2261764 (x : real) (n : nat) : (term465 x n) = (term54 x n).
Proof. exact (@lem1982733 (term54 x n)). Qed.
Lemma lem2261765 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2261766 (x : real) (n : nat) : (term466 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem2261765) (@lem2261764 x n)). Qed.
Lemma lem2261767 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2261768 (x : real) (n : nat) : (term464 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem2261766 x n) (@lem2261767)). Qed.
Lemma lem2261769 (x : real) (n : nat) (h1 : term240 x n) : term59 x n.
Proof. exact (EQ_MP (@lem2261768 x n) (@lem2261763 x n h1)). Qed.
Lemma lem2261771 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2261772 (x : real) (n : nat) : term397 x n.
Proof. exact (@lem2261771 (term21 x n)). Qed.
Lemma lem2261773 (x : real) (n : nat) (h1 : term240 x n) : term398 x n.
Proof. exact (@lem2261772 x n (@lem2261692 x n h1)). Qed.
Lemma lem2261774 (x : real) (n : nat) (h1 : term240 x n) : term467 x n.
Proof. exact (@lem2261773 x n h1 term38). Qed.
Lemma lem2261775 (x : real) (n : nat) : (term467 x n) = ((term394 x n) = term14).
Proof. exact (eq_refl (term467 x n)). Qed.
Lemma lem2261776 (x : real) (n : nat) (h1 : term240 x n) : (term394 x n) = term14.
Proof. exact (EQ_MP (@lem2261775 x n) (@lem2261774 x n h1)). Qed.
Lemma lem2261777 (x : real) (n : nat) : (term394 x n) = (term21 x n).
Proof. exact (@lem1982733 (term21 x n)). Qed.
Lemma lem2261778 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2261779 (x : real) (n : nat) : (term468 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2261778) (@lem2261777 x n)). Qed.
Lemma lem2261780 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2261781 (x : real) (n : nat) : ((term394 x n) = term14) = ((term21 x n) = term14).
Proof. exact (MK_COMB (@lem2261779 x n) (@lem2261780)). Qed.
Lemma lem2261782 (x : real) (n : nat) (h1 : term240 x n) : (term21 x n) = term14.
Proof. exact (EQ_MP (@lem2261781 x n) (@lem2261776 x n h1)). Qed.
Lemma lem2261783 (x : real) (n : nat) (h1 : term240 x n) : term469 x n.
Proof. exact (conj (@lem2261782 x n h1) (@lem2261769 x n h1)). Qed.
Lemma lem2261785 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2261786 (x : real) (n : nat) : term470 x n.
Proof. exact (@lem2261785 (term21 x n) (term54 x n)). Qed.
Lemma lem2261787 (x : real) (n : nat) (h1 : term240 x n) : term471 x n.
Proof. exact (@lem2261786 x n (@lem2261783 x n h1)). Qed.
Lemma lem2261788 (x : real) (n : nat) : (term472 x n) = (term473 x n).
Proof. exact (@lem1982753 x (term208 x) (term27 n) (real_of_num n)). Qed.
Lemma lem2261789 (x : real) : (term474 x) = (term409 x).
Proof. exact (@lem1982715 term26 x). Qed.
Lemma lem2261791 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261792 : term38 = term48.
Proof. exact (@lem2261791 term32). Qed.
Lemma lem2261794 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2261795 : term26 = term31.
Proof. exact (@lem2261794 term32). Qed.
Lemma lem2261796 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261797 : term410 = term411.
Proof. exact (MK_COMB (@lem2261796) (@lem2261795)). Qed.
Lemma lem2261798 : term412 = term413.
Proof. exact (MK_COMB (@lem2261797) (@lem2261792)). Qed.
Lemma lem2261799 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2261801 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261802 : term377 = term383.
Proof. exact (@lem2261801 (NUMERAL 0) term32). Qed.
Lemma lem2261803 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261804 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261805 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261804 h1) (fun h1 : term383 = True => @lem2261803)). Qed.
Lemma lem2261806 : term383 = True.
Proof. exact (EQ_MP (@lem2261805) (@lem2261803)). Qed.
Lemma lem2261807 : term377 = True.
Proof. exact (TRANS (@lem2261802) (@lem2261806)). Qed.
Lemma lem2261808 : True = term377.
Proof. exact (SYM (@lem2261807)). Qed.
Lemma lem2261809 : term377.
Proof. exact (EQ_MP (@lem2261808) (@lem0)). Qed.
Lemma lem2261810 : term415.
Proof. exact (@lem2261799 (@lem2261809)). Qed.
Lemma lem2261812 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261813 : term377 = term383.
Proof. exact (@lem2261812 (NUMERAL 0) term32). Qed.
Lemma lem2261814 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261815 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261816 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261815 h1) (fun h1 : term383 = True => @lem2261814)). Qed.
Lemma lem2261817 : term383 = True.
Proof. exact (EQ_MP (@lem2261816) (@lem2261814)). Qed.
Lemma lem2261818 : term377 = True.
Proof. exact (TRANS (@lem2261813) (@lem2261817)). Qed.
Lemma lem2261819 : True = term377.
Proof. exact (SYM (@lem2261818)). Qed.
Lemma lem2261820 : term377.
Proof. exact (EQ_MP (@lem2261819) (@lem0)). Qed.
Lemma lem2261821 : term416.
Proof. exact (@lem2261810 (@lem2261820)). Qed.
Lemma lem2261823 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261824 : term377 = term383.
Proof. exact (@lem2261823 (NUMERAL 0) term32). Qed.
Lemma lem2261825 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261826 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261827 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261826 h1) (fun h1 : term383 = True => @lem2261825)). Qed.
Lemma lem2261828 : term383 = True.
Proof. exact (EQ_MP (@lem2261827) (@lem2261825)). Qed.
Lemma lem2261829 : term377 = True.
Proof. exact (TRANS (@lem2261824) (@lem2261828)). Qed.
Lemma lem2261830 : True = term377.
Proof. exact (SYM (@lem2261829)). Qed.
Lemma lem2261831 : term377.
Proof. exact (EQ_MP (@lem2261830) (@lem0)). Qed.
Lemma lem2261832 : term417.
Proof. exact (@lem2261821 (@lem2261831)). Qed.
Lemma lem2261834 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261835 : term41 = term42.
Proof. exact (@lem2261834 term32 term32). Qed.
Lemma lem2261836 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261837 : term44 = term32.
Proof. exact (EQ_MP (@lem2261836) (@lem940073)). Qed.
Lemma lem2261838 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261839 : term42 = term38.
Proof. exact (MK_COMB (@lem2261838) (@lem2261837)). Qed.
Lemma lem2261840 : term41 = term38.
Proof. exact (TRANS (@lem2261835) (@lem2261839)). Qed.
Lemma lem2261842 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2261843 : term420 = term421.
Proof. exact (@lem2261842 term32 term32). Qed.
Lemma lem2261844 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261845 : term44 = term32.
Proof. exact (EQ_MP (@lem2261844) (@lem940073)). Qed.
Lemma lem2261846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261847 : term42 = term38.
Proof. exact (MK_COMB (@lem2261846) (@lem2261845)). Qed.
Lemma lem2261848 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2261849 : term421 = term26.
Proof. exact (MK_COMB (@lem2261848) (@lem2261847)). Qed.
Lemma lem2261850 : term420 = term26.
Proof. exact (TRANS (@lem2261843) (@lem2261849)). Qed.
Lemma lem2261851 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261852 : term422 = term410.
Proof. exact (MK_COMB (@lem2261851) (@lem2261850)). Qed.
Lemma lem2261853 : term423 = term412.
Proof. exact (MK_COMB (@lem2261852) (@lem2261840)). Qed.
Lemma lem2261855 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2261856 : term412 = term14.
Proof. exact (@lem2261855 term32). Qed.
Lemma lem2261857 : term423 = term14.
Proof. exact (TRANS (@lem2261853) (@lem2261856)). Qed.
Lemma lem2261858 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261859 : term425 = term426.
Proof. exact (MK_COMB (@lem2261858) (@lem2261857)). Qed.
Lemma lem2261860 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2261861 : term427 = term388.
Proof. exact (MK_COMB (@lem2261859) (@lem2261860)). Qed.
Lemma lem2261863 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261864 : term388 = term14.
Proof. exact (@lem2261863 term32). Qed.
Lemma lem2261865 : term427 = term14.
Proof. exact (TRANS (@lem2261861) (@lem2261864)). Qed.
Lemma lem2261867 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261868 : term41 = term42.
Proof. exact (@lem2261867 term32 term32). Qed.
Lemma lem2261869 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261870 : term44 = term32.
Proof. exact (EQ_MP (@lem2261869) (@lem940073)). Qed.
Lemma lem2261871 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261872 : term42 = term38.
Proof. exact (MK_COMB (@lem2261871) (@lem2261870)). Qed.
Lemma lem2261873 : term41 = term38.
Proof. exact (TRANS (@lem2261868) (@lem2261872)). Qed.
Lemma lem2261874 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2261875 : term428 = term388.
Proof. exact (MK_COMB (@lem2261874) (@lem2261873)). Qed.
Lemma lem2261877 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261878 : term388 = term14.
Proof. exact (@lem2261877 term32). Qed.
Lemma lem2261879 : term428 = term14.
Proof. exact (TRANS (@lem2261875) (@lem2261878)). Qed.
Lemma lem2261880 : term14 = term428.
Proof. exact (SYM (@lem2261879)). Qed.
Lemma lem2261881 : term427 = term428.
Proof. exact (TRANS (@lem2261865) (@lem2261880)). Qed.
Lemma lem2261882 : term413 = term180.
Proof. exact (@lem2261832 (@lem2261881)). Qed.
Lemma lem2261883 : term412 = term180.
Proof. exact (TRANS (@lem2261798) (@lem2261882)). Qed.
Lemma lem2261885 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2261886 : term180 = term14.
Proof. exact (@lem2261885 term14). Qed.
Lemma lem2261887 : term412 = term14.
Proof. exact (TRANS (@lem2261883) (@lem2261886)). Qed.
Lemma lem2261888 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261889 : term429 = term426.
Proof. exact (MK_COMB (@lem2261888) (@lem2261887)). Qed.
Lemma lem2261890 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2261891 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2261889) (@lem2261890 x)). Qed.
Lemma lem2261892 (x : real) : (term474 x) = (term430 x).
Proof. exact (TRANS (@lem2261789 x) (@lem2261891 x)). Qed.
Lemma lem2261893 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2261894 (x : real) : (term474 x) = term14.
Proof. exact (TRANS (@lem2261892 x) (@lem2261893 x)). Qed.
Lemma lem2261895 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261896 (x : real) : (term475 x) = term432.
Proof. exact (MK_COMB (@lem2261895) (@lem2261894 x)). Qed.
Lemma lem2261897 (n : nat) : (term460 n) = (term434 n).
Proof. exact (@lem1982713 term26 (real_of_num n)). Qed.
Lemma lem2261899 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2261900 : term38 = term48.
Proof. exact (@lem2261899 term32). Qed.
Lemma lem2261902 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2261903 : term26 = term31.
Proof. exact (@lem2261902 term32). Qed.
Lemma lem2261904 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261905 : term410 = term411.
Proof. exact (MK_COMB (@lem2261904) (@lem2261903)). Qed.
Lemma lem2261906 : term412 = term413.
Proof. exact (MK_COMB (@lem2261905) (@lem2261900)). Qed.
Lemma lem2261907 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2261909 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261910 : term377 = term383.
Proof. exact (@lem2261909 (NUMERAL 0) term32). Qed.
Lemma lem2261911 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261912 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261913 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261912 h1) (fun h1 : term383 = True => @lem2261911)). Qed.
Lemma lem2261914 : term383 = True.
Proof. exact (EQ_MP (@lem2261913) (@lem2261911)). Qed.
Lemma lem2261915 : term377 = True.
Proof. exact (TRANS (@lem2261910) (@lem2261914)). Qed.
Lemma lem2261916 : True = term377.
Proof. exact (SYM (@lem2261915)). Qed.
Lemma lem2261917 : term377.
Proof. exact (EQ_MP (@lem2261916) (@lem0)). Qed.
Lemma lem2261918 : term415.
Proof. exact (@lem2261907 (@lem2261917)). Qed.
Lemma lem2261920 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261921 : term377 = term383.
Proof. exact (@lem2261920 (NUMERAL 0) term32). Qed.
Lemma lem2261922 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261923 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261924 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261923 h1) (fun h1 : term383 = True => @lem2261922)). Qed.
Lemma lem2261925 : term383 = True.
Proof. exact (EQ_MP (@lem2261924) (@lem2261922)). Qed.
Lemma lem2261926 : term377 = True.
Proof. exact (TRANS (@lem2261921) (@lem2261925)). Qed.
Lemma lem2261927 : True = term377.
Proof. exact (SYM (@lem2261926)). Qed.
Lemma lem2261928 : term377.
Proof. exact (EQ_MP (@lem2261927) (@lem0)). Qed.
Lemma lem2261929 : term416.
Proof. exact (@lem2261918 (@lem2261928)). Qed.
Lemma lem2261931 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2261932 : term377 = term383.
Proof. exact (@lem2261931 (NUMERAL 0) term32). Qed.
Lemma lem2261933 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2261934 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2261935 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2261934 h1) (fun h1 : term383 = True => @lem2261933)). Qed.
Lemma lem2261936 : term383 = True.
Proof. exact (EQ_MP (@lem2261935) (@lem2261933)). Qed.
Lemma lem2261937 : term377 = True.
Proof. exact (TRANS (@lem2261932) (@lem2261936)). Qed.
Lemma lem2261938 : True = term377.
Proof. exact (SYM (@lem2261937)). Qed.
Lemma lem2261939 : term377.
Proof. exact (EQ_MP (@lem2261938) (@lem0)). Qed.
Lemma lem2261940 : term417.
Proof. exact (@lem2261929 (@lem2261939)). Qed.
Lemma lem2261942 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261943 : term41 = term42.
Proof. exact (@lem2261942 term32 term32). Qed.
Lemma lem2261944 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261945 : term44 = term32.
Proof. exact (EQ_MP (@lem2261944) (@lem940073)). Qed.
Lemma lem2261946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261947 : term42 = term38.
Proof. exact (MK_COMB (@lem2261946) (@lem2261945)). Qed.
Lemma lem2261948 : term41 = term38.
Proof. exact (TRANS (@lem2261943) (@lem2261947)). Qed.
Lemma lem2261950 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2261951 : term420 = term421.
Proof. exact (@lem2261950 term32 term32). Qed.
Lemma lem2261952 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261953 : term44 = term32.
Proof. exact (EQ_MP (@lem2261952) (@lem940073)). Qed.
Lemma lem2261954 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261955 : term42 = term38.
Proof. exact (MK_COMB (@lem2261954) (@lem2261953)). Qed.
Lemma lem2261956 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2261957 : term421 = term26.
Proof. exact (MK_COMB (@lem2261956) (@lem2261955)). Qed.
Lemma lem2261958 : term420 = term26.
Proof. exact (TRANS (@lem2261951) (@lem2261957)). Qed.
Lemma lem2261959 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2261960 : term422 = term410.
Proof. exact (MK_COMB (@lem2261959) (@lem2261958)). Qed.
Lemma lem2261961 : term423 = term412.
Proof. exact (MK_COMB (@lem2261960) (@lem2261948)). Qed.
Lemma lem2261963 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2261964 : term412 = term14.
Proof. exact (@lem2261963 term32). Qed.
Lemma lem2261965 : term423 = term14.
Proof. exact (TRANS (@lem2261961) (@lem2261964)). Qed.
Lemma lem2261966 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261967 : term425 = term426.
Proof. exact (MK_COMB (@lem2261966) (@lem2261965)). Qed.
Lemma lem2261968 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2261969 : term427 = term388.
Proof. exact (MK_COMB (@lem2261967) (@lem2261968)). Qed.
Lemma lem2261971 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261972 : term388 = term14.
Proof. exact (@lem2261971 term32). Qed.
Lemma lem2261973 : term427 = term14.
Proof. exact (TRANS (@lem2261969) (@lem2261972)). Qed.
Lemma lem2261975 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2261976 : term41 = term42.
Proof. exact (@lem2261975 term32 term32). Qed.
Lemma lem2261977 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2261978 : term44 = term32.
Proof. exact (EQ_MP (@lem2261977) (@lem940073)). Qed.
Lemma lem2261979 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2261980 : term42 = term38.
Proof. exact (MK_COMB (@lem2261979) (@lem2261978)). Qed.
Lemma lem2261981 : term41 = term38.
Proof. exact (TRANS (@lem2261976) (@lem2261980)). Qed.
Lemma lem2261982 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2261983 : term428 = term388.
Proof. exact (MK_COMB (@lem2261982) (@lem2261981)). Qed.
Lemma lem2261985 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2261986 : term388 = term14.
Proof. exact (@lem2261985 term32). Qed.
Lemma lem2261987 : term428 = term14.
Proof. exact (TRANS (@lem2261983) (@lem2261986)). Qed.
Lemma lem2261988 : term14 = term428.
Proof. exact (SYM (@lem2261987)). Qed.
Lemma lem2261989 : term427 = term428.
Proof. exact (TRANS (@lem2261973) (@lem2261988)). Qed.
Lemma lem2261990 : term413 = term180.
Proof. exact (@lem2261940 (@lem2261989)). Qed.
Lemma lem2261991 : term412 = term180.
Proof. exact (TRANS (@lem2261906) (@lem2261990)). Qed.
Lemma lem2261993 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2261994 : term180 = term14.
Proof. exact (@lem2261993 term14). Qed.
Lemma lem2261995 : term412 = term14.
Proof. exact (TRANS (@lem2261991) (@lem2261994)). Qed.
Lemma lem2261996 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2261997 : term429 = term426.
Proof. exact (MK_COMB (@lem2261996) (@lem2261995)). Qed.
Lemma lem2261998 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2261999 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2261997) (@lem2261998 n)). Qed.
Lemma lem2262000 (n : nat) : (term460 n) = (term387 n).
Proof. exact (TRANS (@lem2261897 n) (@lem2261999 n)). Qed.
Lemma lem2262001 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2262002 (n : nat) : (term460 n) = term14.
Proof. exact (TRANS (@lem2262000 n) (@lem2262001 n)). Qed.
Lemma lem2262003 (x : real) (n : nat) : (term473 x n) = term435.
Proof. exact (MK_COMB (@lem2261896 x) (@lem2262002 n)). Qed.
Lemma lem2262004 (x : real) (n : nat) : (term472 x n) = term435.
Proof. exact (TRANS (@lem2261788 x n) (@lem2262003 x n)). Qed.
Lemma lem2262005 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2262006 (x : real) (n : nat) : (term472 x n) = term14.
Proof. exact (TRANS (@lem2262004 x n) (@lem2262005)). Qed.
Lemma lem2262007 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2262008 (x : real) (n : nat) : (term476 x n) = term437.
Proof. exact (MK_COMB (@lem2262007) (@lem2262006 x n)). Qed.
Lemma lem2262009 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2262010 (x : real) (n : nat) : (term471 x n) = term438.
Proof. exact (MK_COMB (@lem2262008 x n) (@lem2262009)). Qed.
Lemma lem2262011 (x : real) (n : nat) (h1 : term240 x n) : term438.
Proof. exact (EQ_MP (@lem2262010 x n) (@lem2261787 x n h1)). Qed.
Lemma lem2262013 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2262014 : term438 = term439.
Proof. exact (@lem2262013 term14 term14). Qed.
Lemma lem2262016 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262017 : term14 = term180.
Proof. exact (@lem2262016 (NUMERAL 0)). Qed.
Lemma lem2262019 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262020 : term14 = term180.
Proof. exact (@lem2262019 (NUMERAL 0)). Qed.
Lemma lem2262021 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262022 : term378 = term379.
Proof. exact (MK_COMB (@lem2262021) (@lem2262020)). Qed.
Lemma lem2262023 : term439 = term440.
Proof. exact (MK_COMB (@lem2262022) (@lem2262017)). Qed.
Lemma lem2262024 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2262026 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262027 : term377 = term383.
Proof. exact (@lem2262026 (NUMERAL 0) term32). Qed.
Lemma lem2262028 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262029 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262030 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262029 h1) (fun h1 : term383 = True => @lem2262028)). Qed.
Lemma lem2262031 : term383 = True.
Proof. exact (EQ_MP (@lem2262030) (@lem2262028)). Qed.
Lemma lem2262032 : term377 = True.
Proof. exact (TRANS (@lem2262027) (@lem2262031)). Qed.
Lemma lem2262033 : True = term377.
Proof. exact (SYM (@lem2262032)). Qed.
Lemma lem2262034 : term377.
Proof. exact (EQ_MP (@lem2262033) (@lem0)). Qed.
Lemma lem2262035 : term442.
Proof. exact (@lem2262024 (@lem2262034)). Qed.
Lemma lem2262037 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262038 : term377 = term383.
Proof. exact (@lem2262037 (NUMERAL 0) term32). Qed.
Lemma lem2262039 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262040 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262041 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262040 h1) (fun h1 : term383 = True => @lem2262039)). Qed.
Lemma lem2262042 : term383 = True.
Proof. exact (EQ_MP (@lem2262041) (@lem2262039)). Qed.
Lemma lem2262043 : term377 = True.
Proof. exact (TRANS (@lem2262038) (@lem2262042)). Qed.
Lemma lem2262044 : True = term377.
Proof. exact (SYM (@lem2262043)). Qed.
Lemma lem2262045 : term377.
Proof. exact (EQ_MP (@lem2262044) (@lem0)). Qed.
Lemma lem2262046 : term440 = term443.
Proof. exact (@lem2262035 (@lem2262045)). Qed.
Lemma lem2262048 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262049 : term388 = term14.
Proof. exact (@lem2262048 term32). Qed.
Lemma lem2262051 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262052 : term388 = term14.
Proof. exact (@lem2262051 term32). Qed.
Lemma lem2262053 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262054 : term389 = term378.
Proof. exact (MK_COMB (@lem2262053) (@lem2262052)). Qed.
Lemma lem2262055 : term443 = term439.
Proof. exact (MK_COMB (@lem2262054) (@lem2262049)). Qed.
Lemma lem2262057 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262058 : term439 = term444.
Proof. exact (@lem2262057 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2262059 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2262060 : term439 = False.
Proof. exact (TRANS (@lem2262058) (@lem2262059)). Qed.
Lemma lem2262061 : term443 = False.
Proof. exact (TRANS (@lem2262055) (@lem2262060)). Qed.
Lemma lem2262062 : term440 = False.
Proof. exact (TRANS (@lem2262046) (@lem2262061)). Qed.
Lemma lem2262063 : term439 = False.
Proof. exact (TRANS (@lem2262023) (@lem2262062)). Qed.
Lemma lem2262064 : term438 = False.
Proof. exact (TRANS (@lem2262014) (@lem2262063)). Qed.
Lemma lem2262065 (x : real) (n : nat) (h1 : term240 x n) : False.
Proof. exact (EQ_MP (@lem2262064) (@lem2262011 x n h1)). Qed.
Lemma lem2262066 (x : real) (n : nat) (h1 : term253 x n) : term253 x n.
Proof. exact (h1). Qed.
Lemma lem2262067 (x : real) (n : nat) (h1 : term253 x n) : term252 x n.
Proof. exact (proj2 (@lem2262066 x n h1)). Qed.
Lemma lem2262069 (x : real) (n : nat) (h1 : term253 x n) : term151 x n.
Proof. exact (proj2 (@lem2262067 x n h1)). Qed.
Lemma lem2262070 (x : real) (n : nat) (h1 : term253 x n) : (term76 x n) = term14.
Proof. exact (proj1 (@lem2262067 x n h1)). Qed.
Lemma lem2262071 (x : real) (n : nat) (h1 : term253 x n) : term85 x n.
Proof. exact (proj2 (@lem2262069 x n h1)). Qed.
Lemma lem2262075 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2262076 : term376 = term377.
Proof. exact (@lem2262075 term14 term38). Qed.
Lemma lem2262078 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262079 : term38 = term48.
Proof. exact (@lem2262078 term32). Qed.
Lemma lem2262081 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262082 : term14 = term180.
Proof. exact (@lem2262081 (NUMERAL 0)). Qed.
Lemma lem2262083 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262084 : term378 = term379.
Proof. exact (MK_COMB (@lem2262083) (@lem2262082)). Qed.
Lemma lem2262085 : term377 = term380.
Proof. exact (MK_COMB (@lem2262084) (@lem2262079)). Qed.
Lemma lem2262086 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2262088 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262089 : term377 = term383.
Proof. exact (@lem2262088 (NUMERAL 0) term32). Qed.
Lemma lem2262090 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262091 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262092 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262091 h1) (fun h1 : term383 = True => @lem2262090)). Qed.
Lemma lem2262093 : term383 = True.
Proof. exact (EQ_MP (@lem2262092) (@lem2262090)). Qed.
Lemma lem2262094 : term377 = True.
Proof. exact (TRANS (@lem2262089) (@lem2262093)). Qed.
Lemma lem2262095 : True = term377.
Proof. exact (SYM (@lem2262094)). Qed.
Lemma lem2262096 : term377.
Proof. exact (EQ_MP (@lem2262095) (@lem0)). Qed.
Lemma lem2262097 : term385.
Proof. exact (@lem2262086 (@lem2262096)). Qed.
Lemma lem2262099 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262100 : term377 = term383.
Proof. exact (@lem2262099 (NUMERAL 0) term32). Qed.
Lemma lem2262101 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262102 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262103 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262102 h1) (fun h1 : term383 = True => @lem2262101)). Qed.
Lemma lem2262104 : term383 = True.
Proof. exact (EQ_MP (@lem2262103) (@lem2262101)). Qed.
Lemma lem2262105 : term377 = True.
Proof. exact (TRANS (@lem2262100) (@lem2262104)). Qed.
Lemma lem2262106 : True = term377.
Proof. exact (SYM (@lem2262105)). Qed.
Lemma lem2262107 : term377.
Proof. exact (EQ_MP (@lem2262106) (@lem0)). Qed.
Lemma lem2262108 : term380 = term386.
Proof. exact (@lem2262097 (@lem2262107)). Qed.
Lemma lem2262110 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262111 : term41 = term42.
Proof. exact (@lem2262110 term32 term32). Qed.
Lemma lem2262112 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262113 : term44 = term32.
Proof. exact (EQ_MP (@lem2262112) (@lem940073)). Qed.
Lemma lem2262114 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262115 : term42 = term38.
Proof. exact (MK_COMB (@lem2262114) (@lem2262113)). Qed.
Lemma lem2262116 : term41 = term38.
Proof. exact (TRANS (@lem2262111) (@lem2262115)). Qed.
Lemma lem2262118 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262119 : term388 = term14.
Proof. exact (@lem2262118 term32). Qed.
Lemma lem2262120 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262121 : term389 = term378.
Proof. exact (MK_COMB (@lem2262120) (@lem2262119)). Qed.
Lemma lem2262122 : term386 = term377.
Proof. exact (MK_COMB (@lem2262121) (@lem2262116)). Qed.
Lemma lem2262124 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262125 : term377 = term383.
Proof. exact (@lem2262124 (NUMERAL 0) term32). Qed.
Lemma lem2262126 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262127 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262128 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262127 h1) (fun h1 : term383 = True => @lem2262126)). Qed.
Lemma lem2262129 : term383 = True.
Proof. exact (EQ_MP (@lem2262128) (@lem2262126)). Qed.
Lemma lem2262130 : term377 = True.
Proof. exact (TRANS (@lem2262125) (@lem2262129)). Qed.
Lemma lem2262131 : term386 = True.
Proof. exact (TRANS (@lem2262122) (@lem2262130)). Qed.
Lemma lem2262132 : term380 = True.
Proof. exact (TRANS (@lem2262108) (@lem2262131)). Qed.
Lemma lem2262133 : term377 = True.
Proof. exact (TRANS (@lem2262085) (@lem2262132)). Qed.
Lemma lem2262134 : term376 = True.
Proof. exact (TRANS (@lem2262076) (@lem2262133)). Qed.
Lemma lem2262135 : True = term376.
Proof. exact (SYM (@lem2262134)). Qed.
Lemma lem2262136 : term376.
Proof. exact (EQ_MP (@lem2262135) (@lem0)). Qed.
Lemma lem2262137 (x : real) (n : nat) (h1 : term253 x n) : term445 x n.
Proof. exact (conj (@lem2262136) (@lem2262071 x n h1)). Qed.
Lemma lem2262139 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2262140 (x : real) (n : nat) : term446 x n.
Proof. exact (@lem2262139 term38 (term72 x n)). Qed.
Lemma lem2262141 (x : real) (n : nat) (h1 : term253 x n) : term447 x n.
Proof. exact (@lem2262140 x n (@lem2262137 x n h1)). Qed.
Lemma lem2262142 (x : real) (n : nat) : (term448 x n) = (term72 x n).
Proof. exact (@lem1982733 (term72 x n)). Qed.
Lemma lem2262143 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2262144 (x : real) (n : nat) : (term449 x n) = (term83 x n).
Proof. exact (MK_COMB (@lem2262143) (@lem2262142 x n)). Qed.
Lemma lem2262145 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2262146 (x : real) (n : nat) : (term447 x n) = (term85 x n).
Proof. exact (MK_COMB (@lem2262144 x n) (@lem2262145)). Qed.
Lemma lem2262147 (x : real) (n : nat) (h1 : term253 x n) : term85 x n.
Proof. exact (EQ_MP (@lem2262146 x n) (@lem2262141 x n h1)). Qed.
Lemma lem2262149 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2262150 (x : real) (n : nat) : term450 x n.
Proof. exact (@lem2262149 (term76 x n)). Qed.
Lemma lem2262151 (x : real) (n : nat) (h1 : term253 x n) : term451 x n.
Proof. exact (@lem2262150 x n (@lem2262070 x n h1)). Qed.
Lemma lem2262152 (x : real) (n : nat) (h1 : term253 x n) : term452 x n.
Proof. exact (@lem2262151 x n h1 term38). Qed.
Lemma lem2262153 (x : real) (n : nat) : (term452 x n) = ((term453 x n) = term14).
Proof. exact (eq_refl (term452 x n)). Qed.
Lemma lem2262154 (x : real) (n : nat) (h1 : term253 x n) : (term453 x n) = term14.
Proof. exact (EQ_MP (@lem2262153 x n) (@lem2262152 x n h1)). Qed.
Lemma lem2262155 (x : real) (n : nat) : (term453 x n) = (term76 x n).
Proof. exact (@lem1982733 (term76 x n)). Qed.
Lemma lem2262156 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2262157 (x : real) (n : nat) : (term454 x n) = (term222 x n).
Proof. exact (MK_COMB (@lem2262156) (@lem2262155 x n)). Qed.
Lemma lem2262158 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2262159 (x : real) (n : nat) : ((term453 x n) = term14) = ((term76 x n) = term14).
Proof. exact (MK_COMB (@lem2262157 x n) (@lem2262158)). Qed.
Lemma lem2262160 (x : real) (n : nat) (h1 : term253 x n) : (term76 x n) = term14.
Proof. exact (EQ_MP (@lem2262159 x n) (@lem2262154 x n h1)). Qed.
Lemma lem2262161 (x : real) (n : nat) (h1 : term253 x n) : term455 x n.
Proof. exact (conj (@lem2262160 x n h1) (@lem2262147 x n h1)). Qed.
Lemma lem2262163 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2262164 (x : real) (n : nat) : term456 x n.
Proof. exact (@lem2262163 (term76 x n) (term72 x n)). Qed.
Lemma lem2262165 (x : real) (n : nat) (h1 : term253 x n) : term457 x n.
Proof. exact (@lem2262164 x n (@lem2262161 x n h1)). Qed.
Lemma lem2262166 (x : real) (n : nat) : (term458 x n) = (term459 x n).
Proof. exact (@lem1982753 (term208 x) x (term27 n) (real_of_num n)). Qed.
Lemma lem2262167 (x : real) : (term408 x) = (term409 x).
Proof. exact (@lem1982713 term26 x). Qed.
Lemma lem2262169 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262170 : term38 = term48.
Proof. exact (@lem2262169 term32). Qed.
Lemma lem2262172 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2262173 : term26 = term31.
Proof. exact (@lem2262172 term32). Qed.
Lemma lem2262174 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262175 : term410 = term411.
Proof. exact (MK_COMB (@lem2262174) (@lem2262173)). Qed.
Lemma lem2262176 : term412 = term413.
Proof. exact (MK_COMB (@lem2262175) (@lem2262170)). Qed.
Lemma lem2262177 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2262179 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262180 : term377 = term383.
Proof. exact (@lem2262179 (NUMERAL 0) term32). Qed.
Lemma lem2262181 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262182 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262183 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262182 h1) (fun h1 : term383 = True => @lem2262181)). Qed.
Lemma lem2262184 : term383 = True.
Proof. exact (EQ_MP (@lem2262183) (@lem2262181)). Qed.
Lemma lem2262185 : term377 = True.
Proof. exact (TRANS (@lem2262180) (@lem2262184)). Qed.
Lemma lem2262186 : True = term377.
Proof. exact (SYM (@lem2262185)). Qed.
Lemma lem2262187 : term377.
Proof. exact (EQ_MP (@lem2262186) (@lem0)). Qed.
Lemma lem2262188 : term415.
Proof. exact (@lem2262177 (@lem2262187)). Qed.
Lemma lem2262190 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262191 : term377 = term383.
Proof. exact (@lem2262190 (NUMERAL 0) term32). Qed.
Lemma lem2262192 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262193 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262194 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262193 h1) (fun h1 : term383 = True => @lem2262192)). Qed.
Lemma lem2262195 : term383 = True.
Proof. exact (EQ_MP (@lem2262194) (@lem2262192)). Qed.
Lemma lem2262196 : term377 = True.
Proof. exact (TRANS (@lem2262191) (@lem2262195)). Qed.
Lemma lem2262197 : True = term377.
Proof. exact (SYM (@lem2262196)). Qed.
Lemma lem2262198 : term377.
Proof. exact (EQ_MP (@lem2262197) (@lem0)). Qed.
Lemma lem2262199 : term416.
Proof. exact (@lem2262188 (@lem2262198)). Qed.
Lemma lem2262201 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262202 : term377 = term383.
Proof. exact (@lem2262201 (NUMERAL 0) term32). Qed.
Lemma lem2262203 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262204 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262205 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262204 h1) (fun h1 : term383 = True => @lem2262203)). Qed.
Lemma lem2262206 : term383 = True.
Proof. exact (EQ_MP (@lem2262205) (@lem2262203)). Qed.
Lemma lem2262207 : term377 = True.
Proof. exact (TRANS (@lem2262202) (@lem2262206)). Qed.
Lemma lem2262208 : True = term377.
Proof. exact (SYM (@lem2262207)). Qed.
Lemma lem2262209 : term377.
Proof. exact (EQ_MP (@lem2262208) (@lem0)). Qed.
Lemma lem2262210 : term417.
Proof. exact (@lem2262199 (@lem2262209)). Qed.
Lemma lem2262212 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262213 : term41 = term42.
Proof. exact (@lem2262212 term32 term32). Qed.
Lemma lem2262214 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262215 : term44 = term32.
Proof. exact (EQ_MP (@lem2262214) (@lem940073)). Qed.
Lemma lem2262216 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262217 : term42 = term38.
Proof. exact (MK_COMB (@lem2262216) (@lem2262215)). Qed.
Lemma lem2262218 : term41 = term38.
Proof. exact (TRANS (@lem2262213) (@lem2262217)). Qed.
Lemma lem2262220 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2262221 : term420 = term421.
Proof. exact (@lem2262220 term32 term32). Qed.
Lemma lem2262222 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262223 : term44 = term32.
Proof. exact (EQ_MP (@lem2262222) (@lem940073)). Qed.
Lemma lem2262224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262225 : term42 = term38.
Proof. exact (MK_COMB (@lem2262224) (@lem2262223)). Qed.
Lemma lem2262226 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2262227 : term421 = term26.
Proof. exact (MK_COMB (@lem2262226) (@lem2262225)). Qed.
Lemma lem2262228 : term420 = term26.
Proof. exact (TRANS (@lem2262221) (@lem2262227)). Qed.
Lemma lem2262229 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262230 : term422 = term410.
Proof. exact (MK_COMB (@lem2262229) (@lem2262228)). Qed.
Lemma lem2262231 : term423 = term412.
Proof. exact (MK_COMB (@lem2262230) (@lem2262218)). Qed.
Lemma lem2262233 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2262234 : term412 = term14.
Proof. exact (@lem2262233 term32). Qed.
Lemma lem2262235 : term423 = term14.
Proof. exact (TRANS (@lem2262231) (@lem2262234)). Qed.
Lemma lem2262236 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262237 : term425 = term426.
Proof. exact (MK_COMB (@lem2262236) (@lem2262235)). Qed.
Lemma lem2262238 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2262239 : term427 = term388.
Proof. exact (MK_COMB (@lem2262237) (@lem2262238)). Qed.
Lemma lem2262241 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262242 : term388 = term14.
Proof. exact (@lem2262241 term32). Qed.
Lemma lem2262243 : term427 = term14.
Proof. exact (TRANS (@lem2262239) (@lem2262242)). Qed.
Lemma lem2262245 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262246 : term41 = term42.
Proof. exact (@lem2262245 term32 term32). Qed.
Lemma lem2262247 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262248 : term44 = term32.
Proof. exact (EQ_MP (@lem2262247) (@lem940073)). Qed.
Lemma lem2262249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262250 : term42 = term38.
Proof. exact (MK_COMB (@lem2262249) (@lem2262248)). Qed.
Lemma lem2262251 : term41 = term38.
Proof. exact (TRANS (@lem2262246) (@lem2262250)). Qed.
Lemma lem2262252 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2262253 : term428 = term388.
Proof. exact (MK_COMB (@lem2262252) (@lem2262251)). Qed.
Lemma lem2262255 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262256 : term388 = term14.
Proof. exact (@lem2262255 term32). Qed.
Lemma lem2262257 : term428 = term14.
Proof. exact (TRANS (@lem2262253) (@lem2262256)). Qed.
Lemma lem2262258 : term14 = term428.
Proof. exact (SYM (@lem2262257)). Qed.
Lemma lem2262259 : term427 = term428.
Proof. exact (TRANS (@lem2262243) (@lem2262258)). Qed.
Lemma lem2262260 : term413 = term180.
Proof. exact (@lem2262210 (@lem2262259)). Qed.
Lemma lem2262261 : term412 = term180.
Proof. exact (TRANS (@lem2262176) (@lem2262260)). Qed.
Lemma lem2262263 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2262264 : term180 = term14.
Proof. exact (@lem2262263 term14). Qed.
Lemma lem2262265 : term412 = term14.
Proof. exact (TRANS (@lem2262261) (@lem2262264)). Qed.
Lemma lem2262266 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262267 : term429 = term426.
Proof. exact (MK_COMB (@lem2262266) (@lem2262265)). Qed.
Lemma lem2262268 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2262269 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2262267) (@lem2262268 x)). Qed.
Lemma lem2262270 (x : real) : (term408 x) = (term430 x).
Proof. exact (TRANS (@lem2262167 x) (@lem2262269 x)). Qed.
Lemma lem2262271 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2262272 (x : real) : (term408 x) = term14.
Proof. exact (TRANS (@lem2262270 x) (@lem2262271 x)). Qed.
Lemma lem2262273 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262274 (x : real) : (term431 x) = term432.
Proof. exact (MK_COMB (@lem2262273) (@lem2262272 x)). Qed.
Lemma lem2262275 (n : nat) : (term460 n) = (term434 n).
Proof. exact (@lem1982713 term26 (real_of_num n)). Qed.
Lemma lem2262277 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262278 : term38 = term48.
Proof. exact (@lem2262277 term32). Qed.
Lemma lem2262280 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2262281 : term26 = term31.
Proof. exact (@lem2262280 term32). Qed.
Lemma lem2262282 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262283 : term410 = term411.
Proof. exact (MK_COMB (@lem2262282) (@lem2262281)). Qed.
Lemma lem2262284 : term412 = term413.
Proof. exact (MK_COMB (@lem2262283) (@lem2262278)). Qed.
Lemma lem2262285 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2262287 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262288 : term377 = term383.
Proof. exact (@lem2262287 (NUMERAL 0) term32). Qed.
Lemma lem2262289 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262290 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262291 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262290 h1) (fun h1 : term383 = True => @lem2262289)). Qed.
Lemma lem2262292 : term383 = True.
Proof. exact (EQ_MP (@lem2262291) (@lem2262289)). Qed.
Lemma lem2262293 : term377 = True.
Proof. exact (TRANS (@lem2262288) (@lem2262292)). Qed.
Lemma lem2262294 : True = term377.
Proof. exact (SYM (@lem2262293)). Qed.
Lemma lem2262295 : term377.
Proof. exact (EQ_MP (@lem2262294) (@lem0)). Qed.
Lemma lem2262296 : term415.
Proof. exact (@lem2262285 (@lem2262295)). Qed.
Lemma lem2262298 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262299 : term377 = term383.
Proof. exact (@lem2262298 (NUMERAL 0) term32). Qed.
Lemma lem2262300 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262301 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262302 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262301 h1) (fun h1 : term383 = True => @lem2262300)). Qed.
Lemma lem2262303 : term383 = True.
Proof. exact (EQ_MP (@lem2262302) (@lem2262300)). Qed.
Lemma lem2262304 : term377 = True.
Proof. exact (TRANS (@lem2262299) (@lem2262303)). Qed.
Lemma lem2262305 : True = term377.
Proof. exact (SYM (@lem2262304)). Qed.
Lemma lem2262306 : term377.
Proof. exact (EQ_MP (@lem2262305) (@lem0)). Qed.
Lemma lem2262307 : term416.
Proof. exact (@lem2262296 (@lem2262306)). Qed.
Lemma lem2262309 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262310 : term377 = term383.
Proof. exact (@lem2262309 (NUMERAL 0) term32). Qed.
Lemma lem2262311 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262312 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262313 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262312 h1) (fun h1 : term383 = True => @lem2262311)). Qed.
Lemma lem2262314 : term383 = True.
Proof. exact (EQ_MP (@lem2262313) (@lem2262311)). Qed.
Lemma lem2262315 : term377 = True.
Proof. exact (TRANS (@lem2262310) (@lem2262314)). Qed.
Lemma lem2262316 : True = term377.
Proof. exact (SYM (@lem2262315)). Qed.
Lemma lem2262317 : term377.
Proof. exact (EQ_MP (@lem2262316) (@lem0)). Qed.
Lemma lem2262318 : term417.
Proof. exact (@lem2262307 (@lem2262317)). Qed.
Lemma lem2262320 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262321 : term41 = term42.
Proof. exact (@lem2262320 term32 term32). Qed.
Lemma lem2262322 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262323 : term44 = term32.
Proof. exact (EQ_MP (@lem2262322) (@lem940073)). Qed.
Lemma lem2262324 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262325 : term42 = term38.
Proof. exact (MK_COMB (@lem2262324) (@lem2262323)). Qed.
Lemma lem2262326 : term41 = term38.
Proof. exact (TRANS (@lem2262321) (@lem2262325)). Qed.
Lemma lem2262328 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2262329 : term420 = term421.
Proof. exact (@lem2262328 term32 term32). Qed.
Lemma lem2262330 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262331 : term44 = term32.
Proof. exact (EQ_MP (@lem2262330) (@lem940073)). Qed.
Lemma lem2262332 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262333 : term42 = term38.
Proof. exact (MK_COMB (@lem2262332) (@lem2262331)). Qed.
Lemma lem2262334 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2262335 : term421 = term26.
Proof. exact (MK_COMB (@lem2262334) (@lem2262333)). Qed.
Lemma lem2262336 : term420 = term26.
Proof. exact (TRANS (@lem2262329) (@lem2262335)). Qed.
Lemma lem2262337 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262338 : term422 = term410.
Proof. exact (MK_COMB (@lem2262337) (@lem2262336)). Qed.
Lemma lem2262339 : term423 = term412.
Proof. exact (MK_COMB (@lem2262338) (@lem2262326)). Qed.
Lemma lem2262341 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2262342 : term412 = term14.
Proof. exact (@lem2262341 term32). Qed.
Lemma lem2262343 : term423 = term14.
Proof. exact (TRANS (@lem2262339) (@lem2262342)). Qed.
Lemma lem2262344 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262345 : term425 = term426.
Proof. exact (MK_COMB (@lem2262344) (@lem2262343)). Qed.
Lemma lem2262346 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2262347 : term427 = term388.
Proof. exact (MK_COMB (@lem2262345) (@lem2262346)). Qed.
Lemma lem2262349 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262350 : term388 = term14.
Proof. exact (@lem2262349 term32). Qed.
Lemma lem2262351 : term427 = term14.
Proof. exact (TRANS (@lem2262347) (@lem2262350)). Qed.
Lemma lem2262353 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262354 : term41 = term42.
Proof. exact (@lem2262353 term32 term32). Qed.
Lemma lem2262355 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262356 : term44 = term32.
Proof. exact (EQ_MP (@lem2262355) (@lem940073)). Qed.
Lemma lem2262357 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262358 : term42 = term38.
Proof. exact (MK_COMB (@lem2262357) (@lem2262356)). Qed.
Lemma lem2262359 : term41 = term38.
Proof. exact (TRANS (@lem2262354) (@lem2262358)). Qed.
Lemma lem2262360 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2262361 : term428 = term388.
Proof. exact (MK_COMB (@lem2262360) (@lem2262359)). Qed.
Lemma lem2262363 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262364 : term388 = term14.
Proof. exact (@lem2262363 term32). Qed.
Lemma lem2262365 : term428 = term14.
Proof. exact (TRANS (@lem2262361) (@lem2262364)). Qed.
Lemma lem2262366 : term14 = term428.
Proof. exact (SYM (@lem2262365)). Qed.
Lemma lem2262367 : term427 = term428.
Proof. exact (TRANS (@lem2262351) (@lem2262366)). Qed.
Lemma lem2262368 : term413 = term180.
Proof. exact (@lem2262318 (@lem2262367)). Qed.
Lemma lem2262369 : term412 = term180.
Proof. exact (TRANS (@lem2262284) (@lem2262368)). Qed.
Lemma lem2262371 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2262372 : term180 = term14.
Proof. exact (@lem2262371 term14). Qed.
Lemma lem2262373 : term412 = term14.
Proof. exact (TRANS (@lem2262369) (@lem2262372)). Qed.
Lemma lem2262374 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262375 : term429 = term426.
Proof. exact (MK_COMB (@lem2262374) (@lem2262373)). Qed.
Lemma lem2262376 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2262377 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2262375) (@lem2262376 n)). Qed.
Lemma lem2262378 (n : nat) : (term460 n) = (term387 n).
Proof. exact (TRANS (@lem2262275 n) (@lem2262377 n)). Qed.
Lemma lem2262379 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2262380 (n : nat) : (term460 n) = term14.
Proof. exact (TRANS (@lem2262378 n) (@lem2262379 n)). Qed.
Lemma lem2262381 (x : real) (n : nat) : (term459 x n) = term435.
Proof. exact (MK_COMB (@lem2262274 x) (@lem2262380 n)). Qed.
Lemma lem2262382 (x : real) (n : nat) : (term458 x n) = term435.
Proof. exact (TRANS (@lem2262166 x n) (@lem2262381 x n)). Qed.
Lemma lem2262383 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2262384 (x : real) (n : nat) : (term458 x n) = term14.
Proof. exact (TRANS (@lem2262382 x n) (@lem2262383)). Qed.
Lemma lem2262385 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2262386 (x : real) (n : nat) : (term461 x n) = term437.
Proof. exact (MK_COMB (@lem2262385) (@lem2262384 x n)). Qed.
Lemma lem2262387 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2262388 (x : real) (n : nat) : (term457 x n) = term438.
Proof. exact (MK_COMB (@lem2262386 x n) (@lem2262387)). Qed.
Lemma lem2262389 (x : real) (n : nat) (h1 : term253 x n) : term438.
Proof. exact (EQ_MP (@lem2262388 x n) (@lem2262165 x n h1)). Qed.
Lemma lem2262391 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2262392 : term438 = term439.
Proof. exact (@lem2262391 term14 term14). Qed.
Lemma lem2262394 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262395 : term14 = term180.
Proof. exact (@lem2262394 (NUMERAL 0)). Qed.
Lemma lem2262397 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262398 : term14 = term180.
Proof. exact (@lem2262397 (NUMERAL 0)). Qed.
Lemma lem2262399 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262400 : term378 = term379.
Proof. exact (MK_COMB (@lem2262399) (@lem2262398)). Qed.
Lemma lem2262401 : term439 = term440.
Proof. exact (MK_COMB (@lem2262400) (@lem2262395)). Qed.
Lemma lem2262402 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2262404 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262405 : term377 = term383.
Proof. exact (@lem2262404 (NUMERAL 0) term32). Qed.
Lemma lem2262406 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262407 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262408 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262407 h1) (fun h1 : term383 = True => @lem2262406)). Qed.
Lemma lem2262409 : term383 = True.
Proof. exact (EQ_MP (@lem2262408) (@lem2262406)). Qed.
Lemma lem2262410 : term377 = True.
Proof. exact (TRANS (@lem2262405) (@lem2262409)). Qed.
Lemma lem2262411 : True = term377.
Proof. exact (SYM (@lem2262410)). Qed.
Lemma lem2262412 : term377.
Proof. exact (EQ_MP (@lem2262411) (@lem0)). Qed.
Lemma lem2262413 : term442.
Proof. exact (@lem2262402 (@lem2262412)). Qed.
Lemma lem2262415 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262416 : term377 = term383.
Proof. exact (@lem2262415 (NUMERAL 0) term32). Qed.
Lemma lem2262417 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262418 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262419 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262418 h1) (fun h1 : term383 = True => @lem2262417)). Qed.
Lemma lem2262420 : term383 = True.
Proof. exact (EQ_MP (@lem2262419) (@lem2262417)). Qed.
Lemma lem2262421 : term377 = True.
Proof. exact (TRANS (@lem2262416) (@lem2262420)). Qed.
Lemma lem2262422 : True = term377.
Proof. exact (SYM (@lem2262421)). Qed.
Lemma lem2262423 : term377.
Proof. exact (EQ_MP (@lem2262422) (@lem0)). Qed.
Lemma lem2262424 : term440 = term443.
Proof. exact (@lem2262413 (@lem2262423)). Qed.
Lemma lem2262426 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262427 : term388 = term14.
Proof. exact (@lem2262426 term32). Qed.
Lemma lem2262429 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262430 : term388 = term14.
Proof. exact (@lem2262429 term32). Qed.
Lemma lem2262431 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262432 : term389 = term378.
Proof. exact (MK_COMB (@lem2262431) (@lem2262430)). Qed.
Lemma lem2262433 : term443 = term439.
Proof. exact (MK_COMB (@lem2262432) (@lem2262427)). Qed.
Lemma lem2262435 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262436 : term439 = term444.
Proof. exact (@lem2262435 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2262437 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2262438 : term439 = False.
Proof. exact (TRANS (@lem2262436) (@lem2262437)). Qed.
Lemma lem2262439 : term443 = False.
Proof. exact (TRANS (@lem2262433) (@lem2262438)). Qed.
Lemma lem2262440 : term440 = False.
Proof. exact (TRANS (@lem2262424) (@lem2262439)). Qed.
Lemma lem2262441 : term439 = False.
Proof. exact (TRANS (@lem2262401) (@lem2262440)). Qed.
Lemma lem2262442 : term438 = False.
Proof. exact (TRANS (@lem2262392) (@lem2262441)). Qed.
Lemma lem2262443 (x : real) (n : nat) (h1 : term253 x n) : False.
Proof. exact (EQ_MP (@lem2262442) (@lem2262389 x n h1)). Qed.
Lemma lem2262444 (x : real) (n : nat) (h1 : term254 x n) : False.
Proof. exact (or_elim (@lem2261687 x n h1) (fun h0 : term240 x n => @lem2262065 x n h0) (fun h0 : term253 x n => @lem2262443 x n h0)). Qed.
Lemma lem2262445 (x : real) (n : nat) (h1 : term257 x n) : False.
Proof. exact (or_elim (@lem2260880 x n h1) (fun h0 : term228 x n => @lem2261686 x n h0) (fun h0 : term254 x n => @lem2262444 x n h0)). Qed.
Lemma lem2262446 (x : real) (n : nat) (h1 : term300 x n) : term300 x n.
Proof. exact (h1). Qed.
Lemma lem2262447 (x : real) (n : nat) (h1 : term278 x n) : term278 x n.
Proof. exact (h1). Qed.
Lemma lem2262448 (x : real) (n : nat) (h1 : term269 x n) : term269 x n.
Proof. exact (h1). Qed.
Lemma lem2262449 (x : real) (n : nat) (h1 : term269 x n) : term267 x n.
Proof. exact (proj2 (@lem2262448 x n h1)). Qed.
Lemma lem2262451 (x : real) (n : nat) (h1 : term269 x n) : term146 x n.
Proof. exact (proj2 (@lem2262449 x n h1)). Qed.
Lemma lem2262452 (x : real) (n : nat) (h1 : term269 x n) : (term21 x n) = term14.
Proof. exact (proj1 (@lem2262449 x n h1)). Qed.
Lemma lem2262454 (x : real) (n : nat) (h1 : term269 x n) : term63 x n.
Proof. exact (proj1 (@lem2262451 x n h1)). Qed.
Lemma lem2262457 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2262458 : term376 = term377.
Proof. exact (@lem2262457 term14 term38). Qed.
Lemma lem2262460 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262461 : term38 = term48.
Proof. exact (@lem2262460 term32). Qed.
Lemma lem2262463 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262464 : term14 = term180.
Proof. exact (@lem2262463 (NUMERAL 0)). Qed.
Lemma lem2262465 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262466 : term378 = term379.
Proof. exact (MK_COMB (@lem2262465) (@lem2262464)). Qed.
Lemma lem2262467 : term377 = term380.
Proof. exact (MK_COMB (@lem2262466) (@lem2262461)). Qed.
Lemma lem2262468 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2262470 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262471 : term377 = term383.
Proof. exact (@lem2262470 (NUMERAL 0) term32). Qed.
Lemma lem2262472 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262473 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262474 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262473 h1) (fun h1 : term383 = True => @lem2262472)). Qed.
Lemma lem2262475 : term383 = True.
Proof. exact (EQ_MP (@lem2262474) (@lem2262472)). Qed.
Lemma lem2262476 : term377 = True.
Proof. exact (TRANS (@lem2262471) (@lem2262475)). Qed.
Lemma lem2262477 : True = term377.
Proof. exact (SYM (@lem2262476)). Qed.
Lemma lem2262478 : term377.
Proof. exact (EQ_MP (@lem2262477) (@lem0)). Qed.
Lemma lem2262479 : term385.
Proof. exact (@lem2262468 (@lem2262478)). Qed.
Lemma lem2262481 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262482 : term377 = term383.
Proof. exact (@lem2262481 (NUMERAL 0) term32). Qed.
Lemma lem2262483 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262484 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262485 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262484 h1) (fun h1 : term383 = True => @lem2262483)). Qed.
Lemma lem2262486 : term383 = True.
Proof. exact (EQ_MP (@lem2262485) (@lem2262483)). Qed.
Lemma lem2262487 : term377 = True.
Proof. exact (TRANS (@lem2262482) (@lem2262486)). Qed.
Lemma lem2262488 : True = term377.
Proof. exact (SYM (@lem2262487)). Qed.
Lemma lem2262489 : term377.
Proof. exact (EQ_MP (@lem2262488) (@lem0)). Qed.
Lemma lem2262490 : term380 = term386.
Proof. exact (@lem2262479 (@lem2262489)). Qed.
Lemma lem2262492 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262493 : term41 = term42.
Proof. exact (@lem2262492 term32 term32). Qed.
Lemma lem2262494 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262495 : term44 = term32.
Proof. exact (EQ_MP (@lem2262494) (@lem940073)). Qed.
Lemma lem2262496 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262497 : term42 = term38.
Proof. exact (MK_COMB (@lem2262496) (@lem2262495)). Qed.
Lemma lem2262498 : term41 = term38.
Proof. exact (TRANS (@lem2262493) (@lem2262497)). Qed.
Lemma lem2262500 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262501 : term388 = term14.
Proof. exact (@lem2262500 term32). Qed.
Lemma lem2262502 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262503 : term389 = term378.
Proof. exact (MK_COMB (@lem2262502) (@lem2262501)). Qed.
Lemma lem2262504 : term386 = term377.
Proof. exact (MK_COMB (@lem2262503) (@lem2262498)). Qed.
Lemma lem2262506 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262507 : term377 = term383.
Proof. exact (@lem2262506 (NUMERAL 0) term32). Qed.
Lemma lem2262508 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262509 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262510 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262509 h1) (fun h1 : term383 = True => @lem2262508)). Qed.
Lemma lem2262511 : term383 = True.
Proof. exact (EQ_MP (@lem2262510) (@lem2262508)). Qed.
Lemma lem2262512 : term377 = True.
Proof. exact (TRANS (@lem2262507) (@lem2262511)). Qed.
Lemma lem2262513 : term386 = True.
Proof. exact (TRANS (@lem2262504) (@lem2262512)). Qed.
Lemma lem2262514 : term380 = True.
Proof. exact (TRANS (@lem2262490) (@lem2262513)). Qed.
Lemma lem2262515 : term377 = True.
Proof. exact (TRANS (@lem2262467) (@lem2262514)). Qed.
Lemma lem2262516 : term376 = True.
Proof. exact (TRANS (@lem2262458) (@lem2262515)). Qed.
Lemma lem2262517 : True = term376.
Proof. exact (SYM (@lem2262516)). Qed.
Lemma lem2262518 : term376.
Proof. exact (EQ_MP (@lem2262517) (@lem0)). Qed.
Lemma lem2262519 (x : real) (n : nat) (h1 : term269 x n) : term390 x n.
Proof. exact (conj (@lem2262518) (@lem2262454 x n h1)). Qed.
Lemma lem2262521 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2262522 (x : real) (n : nat) : term392 x n.
Proof. exact (@lem2262521 term38 (term21 x n)). Qed.
Lemma lem2262523 (x : real) (n : nat) (h1 : term269 x n) : term393 x n.
Proof. exact (@lem2262522 x n (@lem2262519 x n h1)). Qed.
Lemma lem2262524 (x : real) (n : nat) : (term394 x n) = (term21 x n).
Proof. exact (@lem1982733 (term21 x n)). Qed.
Lemma lem2262525 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2262526 (x : real) (n : nat) : (term395 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem2262525) (@lem2262524 x n)). Qed.
Lemma lem2262527 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2262528 (x : real) (n : nat) : (term393 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem2262526 x n) (@lem2262527)). Qed.
Lemma lem2262529 (x : real) (n : nat) (h1 : term269 x n) : term63 x n.
Proof. exact (EQ_MP (@lem2262528 x n) (@lem2262523 x n h1)). Qed.
Lemma lem2262531 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2262532 (x : real) (n : nat) : term397 x n.
Proof. exact (@lem2262531 (term21 x n)). Qed.
Lemma lem2262533 (x : real) (n : nat) (h1 : term269 x n) : term398 x n.
Proof. exact (@lem2262532 x n (@lem2262452 x n h1)). Qed.
Lemma lem2262534 (x : real) (n : nat) (h1 : term269 x n) : term399 x n.
Proof. exact (@lem2262533 x n h1 term26). Qed.
Lemma lem2262535 (x : real) (n : nat) : (term399 x n) = ((term24 x n) = term14).
Proof. exact (eq_refl (term399 x n)). Qed.
Lemma lem2262536 (x : real) (n : nat) (h1 : term269 x n) : (term24 x n) = term14.
Proof. exact (EQ_MP (@lem2262535 x n) (@lem2262534 x n h1)). Qed.
Lemma lem2262537 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (@lem1982781 x term26 (term27 n)). Qed.
Lemma lem2262538 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2262540 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2262541 : term26 = term31.
Proof. exact (@lem2262540 term32). Qed.
Lemma lem2262543 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2262544 : term26 = term31.
Proof. exact (@lem2262543 term32). Qed.
Lemma lem2262545 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262546 : term33 = term34.
Proof. exact (MK_COMB (@lem2262545) (@lem2262544)). Qed.
Lemma lem2262547 : term35 = term36.
Proof. exact (MK_COMB (@lem2262546) (@lem2262541)). Qed.
Lemma lem2262548 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2262550 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262551 : term41 = term42.
Proof. exact (@lem2262550 term32 term32). Qed.
Lemma lem2262552 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262553 : term44 = term32.
Proof. exact (EQ_MP (@lem2262552) (@lem940073)). Qed.
Lemma lem2262554 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262555 : term42 = term38.
Proof. exact (MK_COMB (@lem2262554) (@lem2262553)). Qed.
Lemma lem2262556 : term41 = term38.
Proof. exact (TRANS (@lem2262551) (@lem2262555)). Qed.
Lemma lem2262558 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2262559 : term35 = term42.
Proof. exact (@lem2262558 term32 term32). Qed.
Lemma lem2262560 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262561 : term44 = term32.
Proof. exact (EQ_MP (@lem2262560) (@lem940073)). Qed.
Lemma lem2262562 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262563 : term42 = term38.
Proof. exact (MK_COMB (@lem2262562) (@lem2262561)). Qed.
Lemma lem2262564 : term35 = term38.
Proof. exact (TRANS (@lem2262559) (@lem2262563)). Qed.
Lemma lem2262565 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2262566 : term46 = term47.
Proof. exact (MK_COMB (@lem2262565) (@lem2262564)). Qed.
Lemma lem2262567 : term37 = term48.
Proof. exact (MK_COMB (@lem2262566) (@lem2262556)). Qed.
Lemma lem2262568 : term36 = term48.
Proof. exact (TRANS (@lem2262548) (@lem2262567)). Qed.
Lemma lem2262569 : term35 = term48.
Proof. exact (TRANS (@lem2262547) (@lem2262568)). Qed.
Lemma lem2262571 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2262572 : term48 = term38.
Proof. exact (@lem2262571 term38). Qed.
Lemma lem2262573 : term35 = term38.
Proof. exact (TRANS (@lem2262569) (@lem2262572)). Qed.
Lemma lem2262574 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262575 : term50 = term51.
Proof. exact (MK_COMB (@lem2262574) (@lem2262573)). Qed.
Lemma lem2262576 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2262577 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2262575) (@lem2262576 n)). Qed.
Lemma lem2262578 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2262538 n) (@lem2262577 n)). Qed.
Lemma lem2262579 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2262580 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2262578 n) (@lem2262579 n)). Qed.
Lemma lem2262583 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2262584 (x : real) (n : nat) : (term25 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem2262583 x) (@lem2262580 n)). Qed.
Lemma lem2262585 (x : real) (n : nat) : (term24 x n) = (term54 x n).
Proof. exact (TRANS (@lem2262537 x n) (@lem2262584 x n)). Qed.
Lemma lem2262586 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2262587 (x : real) (n : nat) : (term400 x n) = (term401 x n).
Proof. exact (MK_COMB (@lem2262586) (@lem2262585 x n)). Qed.
Lemma lem2262588 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2262589 (x : real) (n : nat) : ((term24 x n) = term14) = ((term54 x n) = term14).
Proof. exact (MK_COMB (@lem2262587 x n) (@lem2262588)). Qed.
Lemma lem2262590 (x : real) (n : nat) (h1 : term269 x n) : (term54 x n) = term14.
Proof. exact (EQ_MP (@lem2262589 x n) (@lem2262536 x n h1)). Qed.
Lemma lem2262591 (x : real) (n : nat) (h1 : term269 x n) : term402 x n.
Proof. exact (conj (@lem2262590 x n h1) (@lem2262529 x n h1)). Qed.
Lemma lem2262593 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2262594 (x : real) (n : nat) : term404 x n.
Proof. exact (@lem2262593 (term54 x n) (term21 x n)). Qed.
Lemma lem2262595 (x : real) (n : nat) (h1 : term269 x n) : term405 x n.
Proof. exact (@lem2262594 x n (@lem2262591 x n h1)). Qed.
Lemma lem2262596 (x : real) (n : nat) : (term406 x n) = (term407 x n).
Proof. exact (@lem1982753 (term208 x) x (real_of_num n) (term27 n)). Qed.
Lemma lem2262597 (x : real) : (term408 x) = (term409 x).
Proof. exact (@lem1982713 term26 x). Qed.
Lemma lem2262599 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262600 : term38 = term48.
Proof. exact (@lem2262599 term32). Qed.
Lemma lem2262602 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2262603 : term26 = term31.
Proof. exact (@lem2262602 term32). Qed.
Lemma lem2262604 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262605 : term410 = term411.
Proof. exact (MK_COMB (@lem2262604) (@lem2262603)). Qed.
Lemma lem2262606 : term412 = term413.
Proof. exact (MK_COMB (@lem2262605) (@lem2262600)). Qed.
Lemma lem2262607 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2262609 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262610 : term377 = term383.
Proof. exact (@lem2262609 (NUMERAL 0) term32). Qed.
Lemma lem2262611 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262612 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262613 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262612 h1) (fun h1 : term383 = True => @lem2262611)). Qed.
Lemma lem2262614 : term383 = True.
Proof. exact (EQ_MP (@lem2262613) (@lem2262611)). Qed.
Lemma lem2262615 : term377 = True.
Proof. exact (TRANS (@lem2262610) (@lem2262614)). Qed.
Lemma lem2262616 : True = term377.
Proof. exact (SYM (@lem2262615)). Qed.
Lemma lem2262617 : term377.
Proof. exact (EQ_MP (@lem2262616) (@lem0)). Qed.
Lemma lem2262618 : term415.
Proof. exact (@lem2262607 (@lem2262617)). Qed.
Lemma lem2262620 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262621 : term377 = term383.
Proof. exact (@lem2262620 (NUMERAL 0) term32). Qed.
Lemma lem2262622 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262623 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262624 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262623 h1) (fun h1 : term383 = True => @lem2262622)). Qed.
Lemma lem2262625 : term383 = True.
Proof. exact (EQ_MP (@lem2262624) (@lem2262622)). Qed.
Lemma lem2262626 : term377 = True.
Proof. exact (TRANS (@lem2262621) (@lem2262625)). Qed.
Lemma lem2262627 : True = term377.
Proof. exact (SYM (@lem2262626)). Qed.
Lemma lem2262628 : term377.
Proof. exact (EQ_MP (@lem2262627) (@lem0)). Qed.
Lemma lem2262629 : term416.
Proof. exact (@lem2262618 (@lem2262628)). Qed.
Lemma lem2262631 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262632 : term377 = term383.
Proof. exact (@lem2262631 (NUMERAL 0) term32). Qed.
Lemma lem2262633 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262634 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262635 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262634 h1) (fun h1 : term383 = True => @lem2262633)). Qed.
Lemma lem2262636 : term383 = True.
Proof. exact (EQ_MP (@lem2262635) (@lem2262633)). Qed.
Lemma lem2262637 : term377 = True.
Proof. exact (TRANS (@lem2262632) (@lem2262636)). Qed.
Lemma lem2262638 : True = term377.
Proof. exact (SYM (@lem2262637)). Qed.
Lemma lem2262639 : term377.
Proof. exact (EQ_MP (@lem2262638) (@lem0)). Qed.
Lemma lem2262640 : term417.
Proof. exact (@lem2262629 (@lem2262639)). Qed.
Lemma lem2262642 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262643 : term41 = term42.
Proof. exact (@lem2262642 term32 term32). Qed.
Lemma lem2262644 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262645 : term44 = term32.
Proof. exact (EQ_MP (@lem2262644) (@lem940073)). Qed.
Lemma lem2262646 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262647 : term42 = term38.
Proof. exact (MK_COMB (@lem2262646) (@lem2262645)). Qed.
Lemma lem2262648 : term41 = term38.
Proof. exact (TRANS (@lem2262643) (@lem2262647)). Qed.
Lemma lem2262650 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2262651 : term420 = term421.
Proof. exact (@lem2262650 term32 term32). Qed.
Lemma lem2262652 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262653 : term44 = term32.
Proof. exact (EQ_MP (@lem2262652) (@lem940073)). Qed.
Lemma lem2262654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262655 : term42 = term38.
Proof. exact (MK_COMB (@lem2262654) (@lem2262653)). Qed.
Lemma lem2262656 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2262657 : term421 = term26.
Proof. exact (MK_COMB (@lem2262656) (@lem2262655)). Qed.
Lemma lem2262658 : term420 = term26.
Proof. exact (TRANS (@lem2262651) (@lem2262657)). Qed.
Lemma lem2262659 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262660 : term422 = term410.
Proof. exact (MK_COMB (@lem2262659) (@lem2262658)). Qed.
Lemma lem2262661 : term423 = term412.
Proof. exact (MK_COMB (@lem2262660) (@lem2262648)). Qed.
Lemma lem2262663 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2262664 : term412 = term14.
Proof. exact (@lem2262663 term32). Qed.
Lemma lem2262665 : term423 = term14.
Proof. exact (TRANS (@lem2262661) (@lem2262664)). Qed.
Lemma lem2262666 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262667 : term425 = term426.
Proof. exact (MK_COMB (@lem2262666) (@lem2262665)). Qed.
Lemma lem2262668 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2262669 : term427 = term388.
Proof. exact (MK_COMB (@lem2262667) (@lem2262668)). Qed.
Lemma lem2262671 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262672 : term388 = term14.
Proof. exact (@lem2262671 term32). Qed.
Lemma lem2262673 : term427 = term14.
Proof. exact (TRANS (@lem2262669) (@lem2262672)). Qed.
Lemma lem2262675 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262676 : term41 = term42.
Proof. exact (@lem2262675 term32 term32). Qed.
Lemma lem2262677 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262678 : term44 = term32.
Proof. exact (EQ_MP (@lem2262677) (@lem940073)). Qed.
Lemma lem2262679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262680 : term42 = term38.
Proof. exact (MK_COMB (@lem2262679) (@lem2262678)). Qed.
Lemma lem2262681 : term41 = term38.
Proof. exact (TRANS (@lem2262676) (@lem2262680)). Qed.
Lemma lem2262682 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2262683 : term428 = term388.
Proof. exact (MK_COMB (@lem2262682) (@lem2262681)). Qed.
Lemma lem2262685 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262686 : term388 = term14.
Proof. exact (@lem2262685 term32). Qed.
Lemma lem2262687 : term428 = term14.
Proof. exact (TRANS (@lem2262683) (@lem2262686)). Qed.
Lemma lem2262688 : term14 = term428.
Proof. exact (SYM (@lem2262687)). Qed.
Lemma lem2262689 : term427 = term428.
Proof. exact (TRANS (@lem2262673) (@lem2262688)). Qed.
Lemma lem2262690 : term413 = term180.
Proof. exact (@lem2262640 (@lem2262689)). Qed.
Lemma lem2262691 : term412 = term180.
Proof. exact (TRANS (@lem2262606) (@lem2262690)). Qed.
Lemma lem2262693 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2262694 : term180 = term14.
Proof. exact (@lem2262693 term14). Qed.
Lemma lem2262695 : term412 = term14.
Proof. exact (TRANS (@lem2262691) (@lem2262694)). Qed.
Lemma lem2262696 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262697 : term429 = term426.
Proof. exact (MK_COMB (@lem2262696) (@lem2262695)). Qed.
Lemma lem2262698 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2262699 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2262697) (@lem2262698 x)). Qed.
Lemma lem2262700 (x : real) : (term408 x) = (term430 x).
Proof. exact (TRANS (@lem2262597 x) (@lem2262699 x)). Qed.
Lemma lem2262701 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2262702 (x : real) : (term408 x) = term14.
Proof. exact (TRANS (@lem2262700 x) (@lem2262701 x)). Qed.
Lemma lem2262703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262704 (x : real) : (term431 x) = term432.
Proof. exact (MK_COMB (@lem2262703) (@lem2262702 x)). Qed.
Lemma lem2262705 (n : nat) : (term433 n) = (term434 n).
Proof. exact (@lem1982715 term26 (real_of_num n)). Qed.
Lemma lem2262707 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262708 : term38 = term48.
Proof. exact (@lem2262707 term32). Qed.
Lemma lem2262710 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2262711 : term26 = term31.
Proof. exact (@lem2262710 term32). Qed.
Lemma lem2262712 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262713 : term410 = term411.
Proof. exact (MK_COMB (@lem2262712) (@lem2262711)). Qed.
Lemma lem2262714 : term412 = term413.
Proof. exact (MK_COMB (@lem2262713) (@lem2262708)). Qed.
Lemma lem2262715 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2262717 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262718 : term377 = term383.
Proof. exact (@lem2262717 (NUMERAL 0) term32). Qed.
Lemma lem2262719 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262720 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262721 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262720 h1) (fun h1 : term383 = True => @lem2262719)). Qed.
Lemma lem2262722 : term383 = True.
Proof. exact (EQ_MP (@lem2262721) (@lem2262719)). Qed.
Lemma lem2262723 : term377 = True.
Proof. exact (TRANS (@lem2262718) (@lem2262722)). Qed.
Lemma lem2262724 : True = term377.
Proof. exact (SYM (@lem2262723)). Qed.
Lemma lem2262725 : term377.
Proof. exact (EQ_MP (@lem2262724) (@lem0)). Qed.
Lemma lem2262726 : term415.
Proof. exact (@lem2262715 (@lem2262725)). Qed.
Lemma lem2262728 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262729 : term377 = term383.
Proof. exact (@lem2262728 (NUMERAL 0) term32). Qed.
Lemma lem2262730 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262731 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262732 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262731 h1) (fun h1 : term383 = True => @lem2262730)). Qed.
Lemma lem2262733 : term383 = True.
Proof. exact (EQ_MP (@lem2262732) (@lem2262730)). Qed.
Lemma lem2262734 : term377 = True.
Proof. exact (TRANS (@lem2262729) (@lem2262733)). Qed.
Lemma lem2262735 : True = term377.
Proof. exact (SYM (@lem2262734)). Qed.
Lemma lem2262736 : term377.
Proof. exact (EQ_MP (@lem2262735) (@lem0)). Qed.
Lemma lem2262737 : term416.
Proof. exact (@lem2262726 (@lem2262736)). Qed.
Lemma lem2262739 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262740 : term377 = term383.
Proof. exact (@lem2262739 (NUMERAL 0) term32). Qed.
Lemma lem2262741 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262742 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262743 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262742 h1) (fun h1 : term383 = True => @lem2262741)). Qed.
Lemma lem2262744 : term383 = True.
Proof. exact (EQ_MP (@lem2262743) (@lem2262741)). Qed.
Lemma lem2262745 : term377 = True.
Proof. exact (TRANS (@lem2262740) (@lem2262744)). Qed.
Lemma lem2262746 : True = term377.
Proof. exact (SYM (@lem2262745)). Qed.
Lemma lem2262747 : term377.
Proof. exact (EQ_MP (@lem2262746) (@lem0)). Qed.
Lemma lem2262748 : term417.
Proof. exact (@lem2262737 (@lem2262747)). Qed.
Lemma lem2262750 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262751 : term41 = term42.
Proof. exact (@lem2262750 term32 term32). Qed.
Lemma lem2262752 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262753 : term44 = term32.
Proof. exact (EQ_MP (@lem2262752) (@lem940073)). Qed.
Lemma lem2262754 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262755 : term42 = term38.
Proof. exact (MK_COMB (@lem2262754) (@lem2262753)). Qed.
Lemma lem2262756 : term41 = term38.
Proof. exact (TRANS (@lem2262751) (@lem2262755)). Qed.
Lemma lem2262758 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2262759 : term420 = term421.
Proof. exact (@lem2262758 term32 term32). Qed.
Lemma lem2262760 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262761 : term44 = term32.
Proof. exact (EQ_MP (@lem2262760) (@lem940073)). Qed.
Lemma lem2262762 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262763 : term42 = term38.
Proof. exact (MK_COMB (@lem2262762) (@lem2262761)). Qed.
Lemma lem2262764 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2262765 : term421 = term26.
Proof. exact (MK_COMB (@lem2262764) (@lem2262763)). Qed.
Lemma lem2262766 : term420 = term26.
Proof. exact (TRANS (@lem2262759) (@lem2262765)). Qed.
Lemma lem2262767 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2262768 : term422 = term410.
Proof. exact (MK_COMB (@lem2262767) (@lem2262766)). Qed.
Lemma lem2262769 : term423 = term412.
Proof. exact (MK_COMB (@lem2262768) (@lem2262756)). Qed.
Lemma lem2262771 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2262772 : term412 = term14.
Proof. exact (@lem2262771 term32). Qed.
Lemma lem2262773 : term423 = term14.
Proof. exact (TRANS (@lem2262769) (@lem2262772)). Qed.
Lemma lem2262774 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262775 : term425 = term426.
Proof. exact (MK_COMB (@lem2262774) (@lem2262773)). Qed.
Lemma lem2262776 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2262777 : term427 = term388.
Proof. exact (MK_COMB (@lem2262775) (@lem2262776)). Qed.
Lemma lem2262779 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262780 : term388 = term14.
Proof. exact (@lem2262779 term32). Qed.
Lemma lem2262781 : term427 = term14.
Proof. exact (TRANS (@lem2262777) (@lem2262780)). Qed.
Lemma lem2262783 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262784 : term41 = term42.
Proof. exact (@lem2262783 term32 term32). Qed.
Lemma lem2262785 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262786 : term44 = term32.
Proof. exact (EQ_MP (@lem2262785) (@lem940073)). Qed.
Lemma lem2262787 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262788 : term42 = term38.
Proof. exact (MK_COMB (@lem2262787) (@lem2262786)). Qed.
Lemma lem2262789 : term41 = term38.
Proof. exact (TRANS (@lem2262784) (@lem2262788)). Qed.
Lemma lem2262790 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2262791 : term428 = term388.
Proof. exact (MK_COMB (@lem2262790) (@lem2262789)). Qed.
Lemma lem2262793 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262794 : term388 = term14.
Proof. exact (@lem2262793 term32). Qed.
Lemma lem2262795 : term428 = term14.
Proof. exact (TRANS (@lem2262791) (@lem2262794)). Qed.
Lemma lem2262796 : term14 = term428.
Proof. exact (SYM (@lem2262795)). Qed.
Lemma lem2262797 : term427 = term428.
Proof. exact (TRANS (@lem2262781) (@lem2262796)). Qed.
Lemma lem2262798 : term413 = term180.
Proof. exact (@lem2262748 (@lem2262797)). Qed.
Lemma lem2262799 : term412 = term180.
Proof. exact (TRANS (@lem2262714) (@lem2262798)). Qed.
Lemma lem2262801 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2262802 : term180 = term14.
Proof. exact (@lem2262801 term14). Qed.
Lemma lem2262803 : term412 = term14.
Proof. exact (TRANS (@lem2262799) (@lem2262802)). Qed.
Lemma lem2262804 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262805 : term429 = term426.
Proof. exact (MK_COMB (@lem2262804) (@lem2262803)). Qed.
Lemma lem2262806 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2262807 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2262805) (@lem2262806 n)). Qed.
Lemma lem2262808 (n : nat) : (term433 n) = (term387 n).
Proof. exact (TRANS (@lem2262705 n) (@lem2262807 n)). Qed.
Lemma lem2262809 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2262810 (n : nat) : (term433 n) = term14.
Proof. exact (TRANS (@lem2262808 n) (@lem2262809 n)). Qed.
Lemma lem2262811 (x : real) (n : nat) : (term407 x n) = term435.
Proof. exact (MK_COMB (@lem2262704 x) (@lem2262810 n)). Qed.
Lemma lem2262812 (x : real) (n : nat) : (term406 x n) = term435.
Proof. exact (TRANS (@lem2262596 x n) (@lem2262811 x n)). Qed.
Lemma lem2262813 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2262814 (x : real) (n : nat) : (term406 x n) = term14.
Proof. exact (TRANS (@lem2262812 x n) (@lem2262813)). Qed.
Lemma lem2262815 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2262816 (x : real) (n : nat) : (term436 x n) = term437.
Proof. exact (MK_COMB (@lem2262815) (@lem2262814 x n)). Qed.
Lemma lem2262817 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2262818 (x : real) (n : nat) : (term405 x n) = term438.
Proof. exact (MK_COMB (@lem2262816 x n) (@lem2262817)). Qed.
Lemma lem2262819 (x : real) (n : nat) (h1 : term269 x n) : term438.
Proof. exact (EQ_MP (@lem2262818 x n) (@lem2262595 x n h1)). Qed.
Lemma lem2262821 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2262822 : term438 = term439.
Proof. exact (@lem2262821 term14 term14). Qed.
Lemma lem2262824 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262825 : term14 = term180.
Proof. exact (@lem2262824 (NUMERAL 0)). Qed.
Lemma lem2262827 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262828 : term14 = term180.
Proof. exact (@lem2262827 (NUMERAL 0)). Qed.
Lemma lem2262829 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262830 : term378 = term379.
Proof. exact (MK_COMB (@lem2262829) (@lem2262828)). Qed.
Lemma lem2262831 : term439 = term440.
Proof. exact (MK_COMB (@lem2262830) (@lem2262825)). Qed.
Lemma lem2262832 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2262834 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262835 : term377 = term383.
Proof. exact (@lem2262834 (NUMERAL 0) term32). Qed.
Lemma lem2262836 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262837 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262838 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262837 h1) (fun h1 : term383 = True => @lem2262836)). Qed.
Lemma lem2262839 : term383 = True.
Proof. exact (EQ_MP (@lem2262838) (@lem2262836)). Qed.
Lemma lem2262840 : term377 = True.
Proof. exact (TRANS (@lem2262835) (@lem2262839)). Qed.
Lemma lem2262841 : True = term377.
Proof. exact (SYM (@lem2262840)). Qed.
Lemma lem2262842 : term377.
Proof. exact (EQ_MP (@lem2262841) (@lem0)). Qed.
Lemma lem2262843 : term442.
Proof. exact (@lem2262832 (@lem2262842)). Qed.
Lemma lem2262845 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262846 : term377 = term383.
Proof. exact (@lem2262845 (NUMERAL 0) term32). Qed.
Lemma lem2262847 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262848 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262849 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262848 h1) (fun h1 : term383 = True => @lem2262847)). Qed.
Lemma lem2262850 : term383 = True.
Proof. exact (EQ_MP (@lem2262849) (@lem2262847)). Qed.
Lemma lem2262851 : term377 = True.
Proof. exact (TRANS (@lem2262846) (@lem2262850)). Qed.
Lemma lem2262852 : True = term377.
Proof. exact (SYM (@lem2262851)). Qed.
Lemma lem2262853 : term377.
Proof. exact (EQ_MP (@lem2262852) (@lem0)). Qed.
Lemma lem2262854 : term440 = term443.
Proof. exact (@lem2262843 (@lem2262853)). Qed.
Lemma lem2262856 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262857 : term388 = term14.
Proof. exact (@lem2262856 term32). Qed.
Lemma lem2262859 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262860 : term388 = term14.
Proof. exact (@lem2262859 term32). Qed.
Lemma lem2262861 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262862 : term389 = term378.
Proof. exact (MK_COMB (@lem2262861) (@lem2262860)). Qed.
Lemma lem2262863 : term443 = term439.
Proof. exact (MK_COMB (@lem2262862) (@lem2262857)). Qed.
Lemma lem2262865 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262866 : term439 = term444.
Proof. exact (@lem2262865 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2262867 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2262868 : term439 = False.
Proof. exact (TRANS (@lem2262866) (@lem2262867)). Qed.
Lemma lem2262869 : term443 = False.
Proof. exact (TRANS (@lem2262863) (@lem2262868)). Qed.
Lemma lem2262870 : term440 = False.
Proof. exact (TRANS (@lem2262854) (@lem2262869)). Qed.
Lemma lem2262871 : term439 = False.
Proof. exact (TRANS (@lem2262831) (@lem2262870)). Qed.
Lemma lem2262872 : term438 = False.
Proof. exact (TRANS (@lem2262822) (@lem2262871)). Qed.
Lemma lem2262873 (x : real) (n : nat) (h1 : term269 x n) : False.
Proof. exact (EQ_MP (@lem2262872) (@lem2262819 x n h1)). Qed.
Lemma lem2262874 (x : real) (n : nat) (h1 : term277 x n) : term277 x n.
Proof. exact (h1). Qed.
Lemma lem2262875 (x : real) (n : nat) (h1 : term277 x n) : term276 x n.
Proof. exact (proj2 (@lem2262874 x n h1)). Qed.
Lemma lem2262877 (x : real) (n : nat) (h1 : term277 x n) : term146 x n.
Proof. exact (proj2 (@lem2262875 x n h1)). Qed.
Lemma lem2262878 (x : real) (n : nat) (h1 : term277 x n) : (term76 x n) = term14.
Proof. exact (proj1 (@lem2262875 x n h1)). Qed.
Lemma lem2262879 (x : real) (n : nat) (h1 : term277 x n) : term81 x n.
Proof. exact (proj2 (@lem2262877 x n h1)). Qed.
Lemma lem2262883 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2262884 : term376 = term377.
Proof. exact (@lem2262883 term14 term38). Qed.
Lemma lem2262886 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262887 : term38 = term48.
Proof. exact (@lem2262886 term32). Qed.
Lemma lem2262889 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2262890 : term14 = term180.
Proof. exact (@lem2262889 (NUMERAL 0)). Qed.
Lemma lem2262891 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262892 : term378 = term379.
Proof. exact (MK_COMB (@lem2262891) (@lem2262890)). Qed.
Lemma lem2262893 : term377 = term380.
Proof. exact (MK_COMB (@lem2262892) (@lem2262887)). Qed.
Lemma lem2262894 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2262896 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262897 : term377 = term383.
Proof. exact (@lem2262896 (NUMERAL 0) term32). Qed.
Lemma lem2262898 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262899 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262900 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262899 h1) (fun h1 : term383 = True => @lem2262898)). Qed.
Lemma lem2262901 : term383 = True.
Proof. exact (EQ_MP (@lem2262900) (@lem2262898)). Qed.
Lemma lem2262902 : term377 = True.
Proof. exact (TRANS (@lem2262897) (@lem2262901)). Qed.
Lemma lem2262903 : True = term377.
Proof. exact (SYM (@lem2262902)). Qed.
Lemma lem2262904 : term377.
Proof. exact (EQ_MP (@lem2262903) (@lem0)). Qed.
Lemma lem2262905 : term385.
Proof. exact (@lem2262894 (@lem2262904)). Qed.
Lemma lem2262907 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262908 : term377 = term383.
Proof. exact (@lem2262907 (NUMERAL 0) term32). Qed.
Lemma lem2262909 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262910 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262911 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262910 h1) (fun h1 : term383 = True => @lem2262909)). Qed.
Lemma lem2262912 : term383 = True.
Proof. exact (EQ_MP (@lem2262911) (@lem2262909)). Qed.
Lemma lem2262913 : term377 = True.
Proof. exact (TRANS (@lem2262908) (@lem2262912)). Qed.
Lemma lem2262914 : True = term377.
Proof. exact (SYM (@lem2262913)). Qed.
Lemma lem2262915 : term377.
Proof. exact (EQ_MP (@lem2262914) (@lem0)). Qed.
Lemma lem2262916 : term380 = term386.
Proof. exact (@lem2262905 (@lem2262915)). Qed.
Lemma lem2262918 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262919 : term41 = term42.
Proof. exact (@lem2262918 term32 term32). Qed.
Lemma lem2262920 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262921 : term44 = term32.
Proof. exact (EQ_MP (@lem2262920) (@lem940073)). Qed.
Lemma lem2262922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262923 : term42 = term38.
Proof. exact (MK_COMB (@lem2262922) (@lem2262921)). Qed.
Lemma lem2262924 : term41 = term38.
Proof. exact (TRANS (@lem2262919) (@lem2262923)). Qed.
Lemma lem2262926 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2262927 : term388 = term14.
Proof. exact (@lem2262926 term32). Qed.
Lemma lem2262928 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2262929 : term389 = term378.
Proof. exact (MK_COMB (@lem2262928) (@lem2262927)). Qed.
Lemma lem2262930 : term386 = term377.
Proof. exact (MK_COMB (@lem2262929) (@lem2262924)). Qed.
Lemma lem2262932 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2262933 : term377 = term383.
Proof. exact (@lem2262932 (NUMERAL 0) term32). Qed.
Lemma lem2262934 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2262935 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2262936 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2262935 h1) (fun h1 : term383 = True => @lem2262934)). Qed.
Lemma lem2262937 : term383 = True.
Proof. exact (EQ_MP (@lem2262936) (@lem2262934)). Qed.
Lemma lem2262938 : term377 = True.
Proof. exact (TRANS (@lem2262933) (@lem2262937)). Qed.
Lemma lem2262939 : term386 = True.
Proof. exact (TRANS (@lem2262930) (@lem2262938)). Qed.
Lemma lem2262940 : term380 = True.
Proof. exact (TRANS (@lem2262916) (@lem2262939)). Qed.
Lemma lem2262941 : term377 = True.
Proof. exact (TRANS (@lem2262893) (@lem2262940)). Qed.
Lemma lem2262942 : term376 = True.
Proof. exact (TRANS (@lem2262884) (@lem2262941)). Qed.
Lemma lem2262943 : True = term376.
Proof. exact (SYM (@lem2262942)). Qed.
Lemma lem2262944 : term376.
Proof. exact (EQ_MP (@lem2262943) (@lem0)). Qed.
Lemma lem2262945 (x : real) (n : nat) (h1 : term277 x n) : term477 x n.
Proof. exact (conj (@lem2262944) (@lem2262879 x n h1)). Qed.
Lemma lem2262947 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2262948 (x : real) (n : nat) : term478 x n.
Proof. exact (@lem2262947 term38 (term76 x n)). Qed.
Lemma lem2262949 (x : real) (n : nat) (h1 : term277 x n) : term479 x n.
Proof. exact (@lem2262948 x n (@lem2262945 x n h1)). Qed.
Lemma lem2262950 (x : real) (n : nat) : (term453 x n) = (term76 x n).
Proof. exact (@lem1982733 (term76 x n)). Qed.
Lemma lem2262951 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2262952 (x : real) (n : nat) : (term480 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem2262951) (@lem2262950 x n)). Qed.
Lemma lem2262953 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2262954 (x : real) (n : nat) : (term479 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2262952 x n) (@lem2262953)). Qed.
Lemma lem2262955 (x : real) (n : nat) (h1 : term277 x n) : term81 x n.
Proof. exact (EQ_MP (@lem2262954 x n) (@lem2262949 x n h1)). Qed.
Lemma lem2262957 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2262958 (x : real) (n : nat) : term450 x n.
Proof. exact (@lem2262957 (term76 x n)). Qed.
Lemma lem2262959 (x : real) (n : nat) (h1 : term277 x n) : term451 x n.
Proof. exact (@lem2262958 x n (@lem2262878 x n h1)). Qed.
Lemma lem2262960 (x : real) (n : nat) (h1 : term277 x n) : term481 x n.
Proof. exact (@lem2262959 x n h1 term26). Qed.
Lemma lem2262961 (x : real) (n : nat) : (term481 x n) = ((term482 x n) = term14).
Proof. exact (eq_refl (term481 x n)). Qed.
Lemma lem2262962 (x : real) (n : nat) (h1 : term277 x n) : (term482 x n) = term14.
Proof. exact (EQ_MP (@lem2262961 x n) (@lem2262960 x n h1)). Qed.
Lemma lem2262963 (x : real) (n : nat) : (term482 x n) = (term483 x n).
Proof. exact (@lem1982781 (term208 x) term26 (term27 n)). Qed.
Lemma lem2262964 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2262966 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2262967 : term26 = term31.
Proof. exact (@lem2262966 term32). Qed.
Lemma lem2262969 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2262970 : term26 = term31.
Proof. exact (@lem2262969 term32). Qed.
Lemma lem2262971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2262972 : term33 = term34.
Proof. exact (MK_COMB (@lem2262971) (@lem2262970)). Qed.
Lemma lem2262973 : term35 = term36.
Proof. exact (MK_COMB (@lem2262972) (@lem2262967)). Qed.
Lemma lem2262974 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2262976 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2262977 : term41 = term42.
Proof. exact (@lem2262976 term32 term32). Qed.
Lemma lem2262978 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262979 : term44 = term32.
Proof. exact (EQ_MP (@lem2262978) (@lem940073)). Qed.
Lemma lem2262980 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262981 : term42 = term38.
Proof. exact (MK_COMB (@lem2262980) (@lem2262979)). Qed.
Lemma lem2262982 : term41 = term38.
Proof. exact (TRANS (@lem2262977) (@lem2262981)). Qed.
Lemma lem2262984 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2262985 : term35 = term42.
Proof. exact (@lem2262984 term32 term32). Qed.
Lemma lem2262986 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2262987 : term44 = term32.
Proof. exact (EQ_MP (@lem2262986) (@lem940073)). Qed.
Lemma lem2262988 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2262989 : term42 = term38.
Proof. exact (MK_COMB (@lem2262988) (@lem2262987)). Qed.
Lemma lem2262990 : term35 = term38.
Proof. exact (TRANS (@lem2262985) (@lem2262989)). Qed.
Lemma lem2262991 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2262992 : term46 = term47.
Proof. exact (MK_COMB (@lem2262991) (@lem2262990)). Qed.
Lemma lem2262993 : term37 = term48.
Proof. exact (MK_COMB (@lem2262992) (@lem2262982)). Qed.
Lemma lem2262994 : term36 = term48.
Proof. exact (TRANS (@lem2262974) (@lem2262993)). Qed.
Lemma lem2262995 : term35 = term48.
Proof. exact (TRANS (@lem2262973) (@lem2262994)). Qed.
Lemma lem2262997 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2262998 : term48 = term38.
Proof. exact (@lem2262997 term38). Qed.
Lemma lem2262999 : term35 = term38.
Proof. exact (TRANS (@lem2262995) (@lem2262998)). Qed.
Lemma lem2263000 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263001 : term50 = term51.
Proof. exact (MK_COMB (@lem2263000) (@lem2262999)). Qed.
Lemma lem2263002 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2263003 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2263001) (@lem2263002 n)). Qed.
Lemma lem2263004 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2262964 n) (@lem2263003 n)). Qed.
Lemma lem2263005 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2263006 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2263004 n) (@lem2263005 n)). Qed.
Lemma lem2263007 (x : real) : (term484 x) = (term485 x).
Proof. exact (@lem1982749 term26 term26 x). Qed.
Lemma lem2263009 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263010 : term26 = term31.
Proof. exact (@lem2263009 term32). Qed.
Lemma lem2263012 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263013 : term26 = term31.
Proof. exact (@lem2263012 term32). Qed.
Lemma lem2263014 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263015 : term33 = term34.
Proof. exact (MK_COMB (@lem2263014) (@lem2263013)). Qed.
Lemma lem2263016 : term35 = term36.
Proof. exact (MK_COMB (@lem2263015) (@lem2263010)). Qed.
Lemma lem2263017 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2263019 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263020 : term41 = term42.
Proof. exact (@lem2263019 term32 term32). Qed.
Lemma lem2263021 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263022 : term44 = term32.
Proof. exact (EQ_MP (@lem2263021) (@lem940073)). Qed.
Lemma lem2263023 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263024 : term42 = term38.
Proof. exact (MK_COMB (@lem2263023) (@lem2263022)). Qed.
Lemma lem2263025 : term41 = term38.
Proof. exact (TRANS (@lem2263020) (@lem2263024)). Qed.
Lemma lem2263027 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2263028 : term35 = term42.
Proof. exact (@lem2263027 term32 term32). Qed.
Lemma lem2263029 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263030 : term44 = term32.
Proof. exact (EQ_MP (@lem2263029) (@lem940073)). Qed.
Lemma lem2263031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263032 : term42 = term38.
Proof. exact (MK_COMB (@lem2263031) (@lem2263030)). Qed.
Lemma lem2263033 : term35 = term38.
Proof. exact (TRANS (@lem2263028) (@lem2263032)). Qed.
Lemma lem2263034 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2263035 : term46 = term47.
Proof. exact (MK_COMB (@lem2263034) (@lem2263033)). Qed.
Lemma lem2263036 : term37 = term48.
Proof. exact (MK_COMB (@lem2263035) (@lem2263025)). Qed.
Lemma lem2263037 : term36 = term48.
Proof. exact (TRANS (@lem2263017) (@lem2263036)). Qed.
Lemma lem2263038 : term35 = term48.
Proof. exact (TRANS (@lem2263016) (@lem2263037)). Qed.
Lemma lem2263040 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2263041 : term48 = term38.
Proof. exact (@lem2263040 term38). Qed.
Lemma lem2263042 : term35 = term38.
Proof. exact (TRANS (@lem2263038) (@lem2263041)). Qed.
Lemma lem2263043 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263044 : term50 = term51.
Proof. exact (MK_COMB (@lem2263043) (@lem2263042)). Qed.
Lemma lem2263045 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2263046 (x : real) : (term485 x) = (term330 x).
Proof. exact (MK_COMB (@lem2263044) (@lem2263045 x)). Qed.
Lemma lem2263047 (x : real) : (term484 x) = (term330 x).
Proof. exact (TRANS (@lem2263007 x) (@lem2263046 x)). Qed.
Lemma lem2263048 (x : real) : (term330 x) = x.
Proof. exact (@lem1982709 x). Qed.
Lemma lem2263049 (x : real) : (term484 x) = x.
Proof. exact (TRANS (@lem2263047 x) (@lem2263048 x)). Qed.
Lemma lem2263050 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263051 (x : real) : (term486 x) = (real_add x).
Proof. exact (MK_COMB (@lem2263050) (@lem2263049 x)). Qed.
Lemma lem2263052 (x : real) (n : nat) : (term483 x n) = (term72 x n).
Proof. exact (MK_COMB (@lem2263051 x) (@lem2263006 n)). Qed.
Lemma lem2263053 (x : real) (n : nat) : (term482 x n) = (term72 x n).
Proof. exact (TRANS (@lem2262963 x n) (@lem2263052 x n)). Qed.
Lemma lem2263054 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2263055 (x : real) (n : nat) : (term487 x n) = (term117 x n).
Proof. exact (MK_COMB (@lem2263054) (@lem2263053 x n)). Qed.
Lemma lem2263056 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2263057 (x : real) (n : nat) : ((term482 x n) = term14) = ((term72 x n) = term14).
Proof. exact (MK_COMB (@lem2263055 x n) (@lem2263056)). Qed.
Lemma lem2263058 (x : real) (n : nat) (h1 : term277 x n) : (term72 x n) = term14.
Proof. exact (EQ_MP (@lem2263057 x n) (@lem2262962 x n h1)). Qed.
Lemma lem2263059 (x : real) (n : nat) (h1 : term277 x n) : term488 x n.
Proof. exact (conj (@lem2263058 x n h1) (@lem2262955 x n h1)). Qed.
Lemma lem2263061 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2263062 (x : real) (n : nat) : term489 x n.
Proof. exact (@lem2263061 (term72 x n) (term76 x n)). Qed.
Lemma lem2263063 (x : real) (n : nat) (h1 : term277 x n) : term490 x n.
Proof. exact (@lem2263062 x n (@lem2263059 x n h1)). Qed.
Lemma lem2263064 (x : real) (n : nat) : (term491 x n) = (term492 x n).
Proof. exact (@lem1982753 x (term208 x) (real_of_num n) (term27 n)). Qed.
Lemma lem2263065 (x : real) : (term474 x) = (term409 x).
Proof. exact (@lem1982715 term26 x). Qed.
Lemma lem2263067 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263068 : term38 = term48.
Proof. exact (@lem2263067 term32). Qed.
Lemma lem2263070 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263071 : term26 = term31.
Proof. exact (@lem2263070 term32). Qed.
Lemma lem2263072 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263073 : term410 = term411.
Proof. exact (MK_COMB (@lem2263072) (@lem2263071)). Qed.
Lemma lem2263074 : term412 = term413.
Proof. exact (MK_COMB (@lem2263073) (@lem2263068)). Qed.
Lemma lem2263075 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2263077 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263078 : term377 = term383.
Proof. exact (@lem2263077 (NUMERAL 0) term32). Qed.
Lemma lem2263079 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263080 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263081 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263080 h1) (fun h1 : term383 = True => @lem2263079)). Qed.
Lemma lem2263082 : term383 = True.
Proof. exact (EQ_MP (@lem2263081) (@lem2263079)). Qed.
Lemma lem2263083 : term377 = True.
Proof. exact (TRANS (@lem2263078) (@lem2263082)). Qed.
Lemma lem2263084 : True = term377.
Proof. exact (SYM (@lem2263083)). Qed.
Lemma lem2263085 : term377.
Proof. exact (EQ_MP (@lem2263084) (@lem0)). Qed.
Lemma lem2263086 : term415.
Proof. exact (@lem2263075 (@lem2263085)). Qed.
Lemma lem2263088 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263089 : term377 = term383.
Proof. exact (@lem2263088 (NUMERAL 0) term32). Qed.
Lemma lem2263090 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263091 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263092 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263091 h1) (fun h1 : term383 = True => @lem2263090)). Qed.
Lemma lem2263093 : term383 = True.
Proof. exact (EQ_MP (@lem2263092) (@lem2263090)). Qed.
Lemma lem2263094 : term377 = True.
Proof. exact (TRANS (@lem2263089) (@lem2263093)). Qed.
Lemma lem2263095 : True = term377.
Proof. exact (SYM (@lem2263094)). Qed.
Lemma lem2263096 : term377.
Proof. exact (EQ_MP (@lem2263095) (@lem0)). Qed.
Lemma lem2263097 : term416.
Proof. exact (@lem2263086 (@lem2263096)). Qed.
Lemma lem2263099 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263100 : term377 = term383.
Proof. exact (@lem2263099 (NUMERAL 0) term32). Qed.
Lemma lem2263101 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263102 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263103 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263102 h1) (fun h1 : term383 = True => @lem2263101)). Qed.
Lemma lem2263104 : term383 = True.
Proof. exact (EQ_MP (@lem2263103) (@lem2263101)). Qed.
Lemma lem2263105 : term377 = True.
Proof. exact (TRANS (@lem2263100) (@lem2263104)). Qed.
Lemma lem2263106 : True = term377.
Proof. exact (SYM (@lem2263105)). Qed.
Lemma lem2263107 : term377.
Proof. exact (EQ_MP (@lem2263106) (@lem0)). Qed.
Lemma lem2263108 : term417.
Proof. exact (@lem2263097 (@lem2263107)). Qed.
Lemma lem2263110 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263111 : term41 = term42.
Proof. exact (@lem2263110 term32 term32). Qed.
Lemma lem2263112 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263113 : term44 = term32.
Proof. exact (EQ_MP (@lem2263112) (@lem940073)). Qed.
Lemma lem2263114 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263115 : term42 = term38.
Proof. exact (MK_COMB (@lem2263114) (@lem2263113)). Qed.
Lemma lem2263116 : term41 = term38.
Proof. exact (TRANS (@lem2263111) (@lem2263115)). Qed.
Lemma lem2263118 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2263119 : term420 = term421.
Proof. exact (@lem2263118 term32 term32). Qed.
Lemma lem2263120 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263121 : term44 = term32.
Proof. exact (EQ_MP (@lem2263120) (@lem940073)). Qed.
Lemma lem2263122 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263123 : term42 = term38.
Proof. exact (MK_COMB (@lem2263122) (@lem2263121)). Qed.
Lemma lem2263124 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2263125 : term421 = term26.
Proof. exact (MK_COMB (@lem2263124) (@lem2263123)). Qed.
Lemma lem2263126 : term420 = term26.
Proof. exact (TRANS (@lem2263119) (@lem2263125)). Qed.
Lemma lem2263127 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263128 : term422 = term410.
Proof. exact (MK_COMB (@lem2263127) (@lem2263126)). Qed.
Lemma lem2263129 : term423 = term412.
Proof. exact (MK_COMB (@lem2263128) (@lem2263116)). Qed.
Lemma lem2263131 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2263132 : term412 = term14.
Proof. exact (@lem2263131 term32). Qed.
Lemma lem2263133 : term423 = term14.
Proof. exact (TRANS (@lem2263129) (@lem2263132)). Qed.
Lemma lem2263134 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263135 : term425 = term426.
Proof. exact (MK_COMB (@lem2263134) (@lem2263133)). Qed.
Lemma lem2263136 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2263137 : term427 = term388.
Proof. exact (MK_COMB (@lem2263135) (@lem2263136)). Qed.
Lemma lem2263139 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263140 : term388 = term14.
Proof. exact (@lem2263139 term32). Qed.
Lemma lem2263141 : term427 = term14.
Proof. exact (TRANS (@lem2263137) (@lem2263140)). Qed.
Lemma lem2263143 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263144 : term41 = term42.
Proof. exact (@lem2263143 term32 term32). Qed.
Lemma lem2263145 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263146 : term44 = term32.
Proof. exact (EQ_MP (@lem2263145) (@lem940073)). Qed.
Lemma lem2263147 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263148 : term42 = term38.
Proof. exact (MK_COMB (@lem2263147) (@lem2263146)). Qed.
Lemma lem2263149 : term41 = term38.
Proof. exact (TRANS (@lem2263144) (@lem2263148)). Qed.
Lemma lem2263150 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2263151 : term428 = term388.
Proof. exact (MK_COMB (@lem2263150) (@lem2263149)). Qed.
Lemma lem2263153 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263154 : term388 = term14.
Proof. exact (@lem2263153 term32). Qed.
Lemma lem2263155 : term428 = term14.
Proof. exact (TRANS (@lem2263151) (@lem2263154)). Qed.
Lemma lem2263156 : term14 = term428.
Proof. exact (SYM (@lem2263155)). Qed.
Lemma lem2263157 : term427 = term428.
Proof. exact (TRANS (@lem2263141) (@lem2263156)). Qed.
Lemma lem2263158 : term413 = term180.
Proof. exact (@lem2263108 (@lem2263157)). Qed.
Lemma lem2263159 : term412 = term180.
Proof. exact (TRANS (@lem2263074) (@lem2263158)). Qed.
Lemma lem2263161 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2263162 : term180 = term14.
Proof. exact (@lem2263161 term14). Qed.
Lemma lem2263163 : term412 = term14.
Proof. exact (TRANS (@lem2263159) (@lem2263162)). Qed.
Lemma lem2263164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263165 : term429 = term426.
Proof. exact (MK_COMB (@lem2263164) (@lem2263163)). Qed.
Lemma lem2263166 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2263167 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2263165) (@lem2263166 x)). Qed.
Lemma lem2263168 (x : real) : (term474 x) = (term430 x).
Proof. exact (TRANS (@lem2263065 x) (@lem2263167 x)). Qed.
Lemma lem2263169 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2263170 (x : real) : (term474 x) = term14.
Proof. exact (TRANS (@lem2263168 x) (@lem2263169 x)). Qed.
Lemma lem2263171 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263172 (x : real) : (term475 x) = term432.
Proof. exact (MK_COMB (@lem2263171) (@lem2263170 x)). Qed.
Lemma lem2263173 (n : nat) : (term433 n) = (term434 n).
Proof. exact (@lem1982715 term26 (real_of_num n)). Qed.
Lemma lem2263175 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263176 : term38 = term48.
Proof. exact (@lem2263175 term32). Qed.
Lemma lem2263178 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263179 : term26 = term31.
Proof. exact (@lem2263178 term32). Qed.
Lemma lem2263180 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263181 : term410 = term411.
Proof. exact (MK_COMB (@lem2263180) (@lem2263179)). Qed.
Lemma lem2263182 : term412 = term413.
Proof. exact (MK_COMB (@lem2263181) (@lem2263176)). Qed.
Lemma lem2263183 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2263185 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263186 : term377 = term383.
Proof. exact (@lem2263185 (NUMERAL 0) term32). Qed.
Lemma lem2263187 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263188 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263189 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263188 h1) (fun h1 : term383 = True => @lem2263187)). Qed.
Lemma lem2263190 : term383 = True.
Proof. exact (EQ_MP (@lem2263189) (@lem2263187)). Qed.
Lemma lem2263191 : term377 = True.
Proof. exact (TRANS (@lem2263186) (@lem2263190)). Qed.
Lemma lem2263192 : True = term377.
Proof. exact (SYM (@lem2263191)). Qed.
Lemma lem2263193 : term377.
Proof. exact (EQ_MP (@lem2263192) (@lem0)). Qed.
Lemma lem2263194 : term415.
Proof. exact (@lem2263183 (@lem2263193)). Qed.
Lemma lem2263196 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263197 : term377 = term383.
Proof. exact (@lem2263196 (NUMERAL 0) term32). Qed.
Lemma lem2263198 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263199 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263200 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263199 h1) (fun h1 : term383 = True => @lem2263198)). Qed.
Lemma lem2263201 : term383 = True.
Proof. exact (EQ_MP (@lem2263200) (@lem2263198)). Qed.
Lemma lem2263202 : term377 = True.
Proof. exact (TRANS (@lem2263197) (@lem2263201)). Qed.
Lemma lem2263203 : True = term377.
Proof. exact (SYM (@lem2263202)). Qed.
Lemma lem2263204 : term377.
Proof. exact (EQ_MP (@lem2263203) (@lem0)). Qed.
Lemma lem2263205 : term416.
Proof. exact (@lem2263194 (@lem2263204)). Qed.
Lemma lem2263207 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263208 : term377 = term383.
Proof. exact (@lem2263207 (NUMERAL 0) term32). Qed.
Lemma lem2263209 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263210 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263211 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263210 h1) (fun h1 : term383 = True => @lem2263209)). Qed.
Lemma lem2263212 : term383 = True.
Proof. exact (EQ_MP (@lem2263211) (@lem2263209)). Qed.
Lemma lem2263213 : term377 = True.
Proof. exact (TRANS (@lem2263208) (@lem2263212)). Qed.
Lemma lem2263214 : True = term377.
Proof. exact (SYM (@lem2263213)). Qed.
Lemma lem2263215 : term377.
Proof. exact (EQ_MP (@lem2263214) (@lem0)). Qed.
Lemma lem2263216 : term417.
Proof. exact (@lem2263205 (@lem2263215)). Qed.
Lemma lem2263218 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263219 : term41 = term42.
Proof. exact (@lem2263218 term32 term32). Qed.
Lemma lem2263220 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263221 : term44 = term32.
Proof. exact (EQ_MP (@lem2263220) (@lem940073)). Qed.
Lemma lem2263222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263223 : term42 = term38.
Proof. exact (MK_COMB (@lem2263222) (@lem2263221)). Qed.
Lemma lem2263224 : term41 = term38.
Proof. exact (TRANS (@lem2263219) (@lem2263223)). Qed.
Lemma lem2263226 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2263227 : term420 = term421.
Proof. exact (@lem2263226 term32 term32). Qed.
Lemma lem2263228 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263229 : term44 = term32.
Proof. exact (EQ_MP (@lem2263228) (@lem940073)). Qed.
Lemma lem2263230 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263231 : term42 = term38.
Proof. exact (MK_COMB (@lem2263230) (@lem2263229)). Qed.
Lemma lem2263232 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2263233 : term421 = term26.
Proof. exact (MK_COMB (@lem2263232) (@lem2263231)). Qed.
Lemma lem2263234 : term420 = term26.
Proof. exact (TRANS (@lem2263227) (@lem2263233)). Qed.
Lemma lem2263235 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263236 : term422 = term410.
Proof. exact (MK_COMB (@lem2263235) (@lem2263234)). Qed.
Lemma lem2263237 : term423 = term412.
Proof. exact (MK_COMB (@lem2263236) (@lem2263224)). Qed.
Lemma lem2263239 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2263240 : term412 = term14.
Proof. exact (@lem2263239 term32). Qed.
Lemma lem2263241 : term423 = term14.
Proof. exact (TRANS (@lem2263237) (@lem2263240)). Qed.
Lemma lem2263242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263243 : term425 = term426.
Proof. exact (MK_COMB (@lem2263242) (@lem2263241)). Qed.
Lemma lem2263244 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2263245 : term427 = term388.
Proof. exact (MK_COMB (@lem2263243) (@lem2263244)). Qed.
Lemma lem2263247 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263248 : term388 = term14.
Proof. exact (@lem2263247 term32). Qed.
Lemma lem2263249 : term427 = term14.
Proof. exact (TRANS (@lem2263245) (@lem2263248)). Qed.
Lemma lem2263251 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263252 : term41 = term42.
Proof. exact (@lem2263251 term32 term32). Qed.
Lemma lem2263253 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263254 : term44 = term32.
Proof. exact (EQ_MP (@lem2263253) (@lem940073)). Qed.
Lemma lem2263255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263256 : term42 = term38.
Proof. exact (MK_COMB (@lem2263255) (@lem2263254)). Qed.
Lemma lem2263257 : term41 = term38.
Proof. exact (TRANS (@lem2263252) (@lem2263256)). Qed.
Lemma lem2263258 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2263259 : term428 = term388.
Proof. exact (MK_COMB (@lem2263258) (@lem2263257)). Qed.
Lemma lem2263261 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263262 : term388 = term14.
Proof. exact (@lem2263261 term32). Qed.
Lemma lem2263263 : term428 = term14.
Proof. exact (TRANS (@lem2263259) (@lem2263262)). Qed.
Lemma lem2263264 : term14 = term428.
Proof. exact (SYM (@lem2263263)). Qed.
Lemma lem2263265 : term427 = term428.
Proof. exact (TRANS (@lem2263249) (@lem2263264)). Qed.
Lemma lem2263266 : term413 = term180.
Proof. exact (@lem2263216 (@lem2263265)). Qed.
Lemma lem2263267 : term412 = term180.
Proof. exact (TRANS (@lem2263182) (@lem2263266)). Qed.
Lemma lem2263269 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2263270 : term180 = term14.
Proof. exact (@lem2263269 term14). Qed.
Lemma lem2263271 : term412 = term14.
Proof. exact (TRANS (@lem2263267) (@lem2263270)). Qed.
Lemma lem2263272 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263273 : term429 = term426.
Proof. exact (MK_COMB (@lem2263272) (@lem2263271)). Qed.
Lemma lem2263274 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2263275 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2263273) (@lem2263274 n)). Qed.
Lemma lem2263276 (n : nat) : (term433 n) = (term387 n).
Proof. exact (TRANS (@lem2263173 n) (@lem2263275 n)). Qed.
Lemma lem2263277 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2263278 (n : nat) : (term433 n) = term14.
Proof. exact (TRANS (@lem2263276 n) (@lem2263277 n)). Qed.
Lemma lem2263279 (x : real) (n : nat) : (term492 x n) = term435.
Proof. exact (MK_COMB (@lem2263172 x) (@lem2263278 n)). Qed.
Lemma lem2263280 (x : real) (n : nat) : (term491 x n) = term435.
Proof. exact (TRANS (@lem2263064 x n) (@lem2263279 x n)). Qed.
Lemma lem2263281 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2263282 (x : real) (n : nat) : (term491 x n) = term14.
Proof. exact (TRANS (@lem2263280 x n) (@lem2263281)). Qed.
Lemma lem2263283 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2263284 (x : real) (n : nat) : (term493 x n) = term437.
Proof. exact (MK_COMB (@lem2263283) (@lem2263282 x n)). Qed.
Lemma lem2263285 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2263286 (x : real) (n : nat) : (term490 x n) = term438.
Proof. exact (MK_COMB (@lem2263284 x n) (@lem2263285)). Qed.
Lemma lem2263287 (x : real) (n : nat) (h1 : term277 x n) : term438.
Proof. exact (EQ_MP (@lem2263286 x n) (@lem2263063 x n h1)). Qed.
Lemma lem2263289 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2263290 : term438 = term439.
Proof. exact (@lem2263289 term14 term14). Qed.
Lemma lem2263292 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263293 : term14 = term180.
Proof. exact (@lem2263292 (NUMERAL 0)). Qed.
Lemma lem2263295 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263296 : term14 = term180.
Proof. exact (@lem2263295 (NUMERAL 0)). Qed.
Lemma lem2263297 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2263298 : term378 = term379.
Proof. exact (MK_COMB (@lem2263297) (@lem2263296)). Qed.
Lemma lem2263299 : term439 = term440.
Proof. exact (MK_COMB (@lem2263298) (@lem2263293)). Qed.
Lemma lem2263300 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2263302 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263303 : term377 = term383.
Proof. exact (@lem2263302 (NUMERAL 0) term32). Qed.
Lemma lem2263304 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263305 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263306 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263305 h1) (fun h1 : term383 = True => @lem2263304)). Qed.
Lemma lem2263307 : term383 = True.
Proof. exact (EQ_MP (@lem2263306) (@lem2263304)). Qed.
Lemma lem2263308 : term377 = True.
Proof. exact (TRANS (@lem2263303) (@lem2263307)). Qed.
Lemma lem2263309 : True = term377.
Proof. exact (SYM (@lem2263308)). Qed.
Lemma lem2263310 : term377.
Proof. exact (EQ_MP (@lem2263309) (@lem0)). Qed.
Lemma lem2263311 : term442.
Proof. exact (@lem2263300 (@lem2263310)). Qed.
Lemma lem2263313 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263314 : term377 = term383.
Proof. exact (@lem2263313 (NUMERAL 0) term32). Qed.
Lemma lem2263315 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263316 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263317 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263316 h1) (fun h1 : term383 = True => @lem2263315)). Qed.
Lemma lem2263318 : term383 = True.
Proof. exact (EQ_MP (@lem2263317) (@lem2263315)). Qed.
Lemma lem2263319 : term377 = True.
Proof. exact (TRANS (@lem2263314) (@lem2263318)). Qed.
Lemma lem2263320 : True = term377.
Proof. exact (SYM (@lem2263319)). Qed.
Lemma lem2263321 : term377.
Proof. exact (EQ_MP (@lem2263320) (@lem0)). Qed.
Lemma lem2263322 : term440 = term443.
Proof. exact (@lem2263311 (@lem2263321)). Qed.
Lemma lem2263324 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263325 : term388 = term14.
Proof. exact (@lem2263324 term32). Qed.
Lemma lem2263327 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263328 : term388 = term14.
Proof. exact (@lem2263327 term32). Qed.
Lemma lem2263329 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2263330 : term389 = term378.
Proof. exact (MK_COMB (@lem2263329) (@lem2263328)). Qed.
Lemma lem2263331 : term443 = term439.
Proof. exact (MK_COMB (@lem2263330) (@lem2263325)). Qed.
Lemma lem2263333 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263334 : term439 = term444.
Proof. exact (@lem2263333 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2263335 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2263336 : term439 = False.
Proof. exact (TRANS (@lem2263334) (@lem2263335)). Qed.
Lemma lem2263337 : term443 = False.
Proof. exact (TRANS (@lem2263331) (@lem2263336)). Qed.
Lemma lem2263338 : term440 = False.
Proof. exact (TRANS (@lem2263322) (@lem2263337)). Qed.
Lemma lem2263339 : term439 = False.
Proof. exact (TRANS (@lem2263299) (@lem2263338)). Qed.
Lemma lem2263340 : term438 = False.
Proof. exact (TRANS (@lem2263290) (@lem2263339)). Qed.
Lemma lem2263341 (x : real) (n : nat) (h1 : term277 x n) : False.
Proof. exact (EQ_MP (@lem2263340) (@lem2263287 x n h1)). Qed.
Lemma lem2263342 (x : real) (n : nat) (h1 : term278 x n) : False.
Proof. exact (or_elim (@lem2262447 x n h1) (fun h0 : term269 x n => @lem2262873 x n h0) (fun h0 : term277 x n => @lem2263341 x n h0)). Qed.
Lemma lem2263343 (x : real) (n : nat) (h1 : term297 x n) : term297 x n.
Proof. exact (h1). Qed.
Lemma lem2263344 (x : real) (n : nat) (h1 : term290 x n) : term290 x n.
Proof. exact (h1). Qed.
Lemma lem2263345 (x : real) (n : nat) (h1 : term290 x n) : term288 x n.
Proof. exact (proj2 (@lem2263344 x n h1)). Qed.
Lemma lem2263347 (x : real) (n : nat) (h1 : term290 x n) : term147 x n.
Proof. exact (proj2 (@lem2263345 x n h1)). Qed.
Lemma lem2263348 (x : real) (n : nat) (h1 : term290 x n) : (term21 x n) = term14.
Proof. exact (proj1 (@lem2263345 x n h1)). Qed.
Lemma lem2263350 (x : real) (n : nat) (h1 : term290 x n) : term59 x n.
Proof. exact (proj1 (@lem2263347 x n h1)). Qed.
Lemma lem2263353 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2263354 : term376 = term377.
Proof. exact (@lem2263353 term14 term38). Qed.
Lemma lem2263356 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263357 : term38 = term48.
Proof. exact (@lem2263356 term32). Qed.
Lemma lem2263359 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263360 : term14 = term180.
Proof. exact (@lem2263359 (NUMERAL 0)). Qed.
Lemma lem2263361 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2263362 : term378 = term379.
Proof. exact (MK_COMB (@lem2263361) (@lem2263360)). Qed.
Lemma lem2263363 : term377 = term380.
Proof. exact (MK_COMB (@lem2263362) (@lem2263357)). Qed.
Lemma lem2263364 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2263366 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263367 : term377 = term383.
Proof. exact (@lem2263366 (NUMERAL 0) term32). Qed.
Lemma lem2263368 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263369 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263370 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263369 h1) (fun h1 : term383 = True => @lem2263368)). Qed.
Lemma lem2263371 : term383 = True.
Proof. exact (EQ_MP (@lem2263370) (@lem2263368)). Qed.
Lemma lem2263372 : term377 = True.
Proof. exact (TRANS (@lem2263367) (@lem2263371)). Qed.
Lemma lem2263373 : True = term377.
Proof. exact (SYM (@lem2263372)). Qed.
Lemma lem2263374 : term377.
Proof. exact (EQ_MP (@lem2263373) (@lem0)). Qed.
Lemma lem2263375 : term385.
Proof. exact (@lem2263364 (@lem2263374)). Qed.
Lemma lem2263377 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263378 : term377 = term383.
Proof. exact (@lem2263377 (NUMERAL 0) term32). Qed.
Lemma lem2263379 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263380 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263381 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263380 h1) (fun h1 : term383 = True => @lem2263379)). Qed.
Lemma lem2263382 : term383 = True.
Proof. exact (EQ_MP (@lem2263381) (@lem2263379)). Qed.
Lemma lem2263383 : term377 = True.
Proof. exact (TRANS (@lem2263378) (@lem2263382)). Qed.
Lemma lem2263384 : True = term377.
Proof. exact (SYM (@lem2263383)). Qed.
Lemma lem2263385 : term377.
Proof. exact (EQ_MP (@lem2263384) (@lem0)). Qed.
Lemma lem2263386 : term380 = term386.
Proof. exact (@lem2263375 (@lem2263385)). Qed.
Lemma lem2263388 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263389 : term41 = term42.
Proof. exact (@lem2263388 term32 term32). Qed.
Lemma lem2263390 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263391 : term44 = term32.
Proof. exact (EQ_MP (@lem2263390) (@lem940073)). Qed.
Lemma lem2263392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263393 : term42 = term38.
Proof. exact (MK_COMB (@lem2263392) (@lem2263391)). Qed.
Lemma lem2263394 : term41 = term38.
Proof. exact (TRANS (@lem2263389) (@lem2263393)). Qed.
Lemma lem2263396 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263397 : term388 = term14.
Proof. exact (@lem2263396 term32). Qed.
Lemma lem2263398 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2263399 : term389 = term378.
Proof. exact (MK_COMB (@lem2263398) (@lem2263397)). Qed.
Lemma lem2263400 : term386 = term377.
Proof. exact (MK_COMB (@lem2263399) (@lem2263394)). Qed.
Lemma lem2263402 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263403 : term377 = term383.
Proof. exact (@lem2263402 (NUMERAL 0) term32). Qed.
Lemma lem2263404 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263405 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263406 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263405 h1) (fun h1 : term383 = True => @lem2263404)). Qed.
Lemma lem2263407 : term383 = True.
Proof. exact (EQ_MP (@lem2263406) (@lem2263404)). Qed.
Lemma lem2263408 : term377 = True.
Proof. exact (TRANS (@lem2263403) (@lem2263407)). Qed.
Lemma lem2263409 : term386 = True.
Proof. exact (TRANS (@lem2263400) (@lem2263408)). Qed.
Lemma lem2263410 : term380 = True.
Proof. exact (TRANS (@lem2263386) (@lem2263409)). Qed.
Lemma lem2263411 : term377 = True.
Proof. exact (TRANS (@lem2263363) (@lem2263410)). Qed.
Lemma lem2263412 : term376 = True.
Proof. exact (TRANS (@lem2263354) (@lem2263411)). Qed.
Lemma lem2263413 : True = term376.
Proof. exact (SYM (@lem2263412)). Qed.
Lemma lem2263414 : term376.
Proof. exact (EQ_MP (@lem2263413) (@lem0)). Qed.
Lemma lem2263415 (x : real) (n : nat) (h1 : term290 x n) : term462 x n.
Proof. exact (conj (@lem2263414) (@lem2263350 x n h1)). Qed.
Lemma lem2263417 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2263418 (x : real) (n : nat) : term463 x n.
Proof. exact (@lem2263417 term38 (term54 x n)). Qed.
Lemma lem2263419 (x : real) (n : nat) (h1 : term290 x n) : term464 x n.
Proof. exact (@lem2263418 x n (@lem2263415 x n h1)). Qed.
Lemma lem2263420 (x : real) (n : nat) : (term465 x n) = (term54 x n).
Proof. exact (@lem1982733 (term54 x n)). Qed.
Lemma lem2263421 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2263422 (x : real) (n : nat) : (term466 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem2263421) (@lem2263420 x n)). Qed.
Lemma lem2263423 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2263424 (x : real) (n : nat) : (term464 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem2263422 x n) (@lem2263423)). Qed.
Lemma lem2263425 (x : real) (n : nat) (h1 : term290 x n) : term59 x n.
Proof. exact (EQ_MP (@lem2263424 x n) (@lem2263419 x n h1)). Qed.
Lemma lem2263427 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2263428 (x : real) (n : nat) : term397 x n.
Proof. exact (@lem2263427 (term21 x n)). Qed.
Lemma lem2263429 (x : real) (n : nat) (h1 : term290 x n) : term398 x n.
Proof. exact (@lem2263428 x n (@lem2263348 x n h1)). Qed.
Lemma lem2263430 (x : real) (n : nat) (h1 : term290 x n) : term467 x n.
Proof. exact (@lem2263429 x n h1 term38). Qed.
Lemma lem2263431 (x : real) (n : nat) : (term467 x n) = ((term394 x n) = term14).
Proof. exact (eq_refl (term467 x n)). Qed.
Lemma lem2263432 (x : real) (n : nat) (h1 : term290 x n) : (term394 x n) = term14.
Proof. exact (EQ_MP (@lem2263431 x n) (@lem2263430 x n h1)). Qed.
Lemma lem2263433 (x : real) (n : nat) : (term394 x n) = (term21 x n).
Proof. exact (@lem1982733 (term21 x n)). Qed.
Lemma lem2263434 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2263435 (x : real) (n : nat) : (term468 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2263434) (@lem2263433 x n)). Qed.
Lemma lem2263436 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2263437 (x : real) (n : nat) : ((term394 x n) = term14) = ((term21 x n) = term14).
Proof. exact (MK_COMB (@lem2263435 x n) (@lem2263436)). Qed.
Lemma lem2263438 (x : real) (n : nat) (h1 : term290 x n) : (term21 x n) = term14.
Proof. exact (EQ_MP (@lem2263437 x n) (@lem2263432 x n h1)). Qed.
Lemma lem2263439 (x : real) (n : nat) (h1 : term290 x n) : term469 x n.
Proof. exact (conj (@lem2263438 x n h1) (@lem2263425 x n h1)). Qed.
Lemma lem2263441 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2263442 (x : real) (n : nat) : term470 x n.
Proof. exact (@lem2263441 (term21 x n) (term54 x n)). Qed.
Lemma lem2263443 (x : real) (n : nat) (h1 : term290 x n) : term471 x n.
Proof. exact (@lem2263442 x n (@lem2263439 x n h1)). Qed.
Lemma lem2263444 (x : real) (n : nat) : (term472 x n) = (term473 x n).
Proof. exact (@lem1982753 x (term208 x) (term27 n) (real_of_num n)). Qed.
Lemma lem2263445 (x : real) : (term474 x) = (term409 x).
Proof. exact (@lem1982715 term26 x). Qed.
Lemma lem2263447 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263448 : term38 = term48.
Proof. exact (@lem2263447 term32). Qed.
Lemma lem2263450 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263451 : term26 = term31.
Proof. exact (@lem2263450 term32). Qed.
Lemma lem2263452 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263453 : term410 = term411.
Proof. exact (MK_COMB (@lem2263452) (@lem2263451)). Qed.
Lemma lem2263454 : term412 = term413.
Proof. exact (MK_COMB (@lem2263453) (@lem2263448)). Qed.
Lemma lem2263455 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2263457 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263458 : term377 = term383.
Proof. exact (@lem2263457 (NUMERAL 0) term32). Qed.
Lemma lem2263459 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263460 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263461 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263460 h1) (fun h1 : term383 = True => @lem2263459)). Qed.
Lemma lem2263462 : term383 = True.
Proof. exact (EQ_MP (@lem2263461) (@lem2263459)). Qed.
Lemma lem2263463 : term377 = True.
Proof. exact (TRANS (@lem2263458) (@lem2263462)). Qed.
Lemma lem2263464 : True = term377.
Proof. exact (SYM (@lem2263463)). Qed.
Lemma lem2263465 : term377.
Proof. exact (EQ_MP (@lem2263464) (@lem0)). Qed.
Lemma lem2263466 : term415.
Proof. exact (@lem2263455 (@lem2263465)). Qed.
Lemma lem2263468 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263469 : term377 = term383.
Proof. exact (@lem2263468 (NUMERAL 0) term32). Qed.
Lemma lem2263470 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263471 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263472 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263471 h1) (fun h1 : term383 = True => @lem2263470)). Qed.
Lemma lem2263473 : term383 = True.
Proof. exact (EQ_MP (@lem2263472) (@lem2263470)). Qed.
Lemma lem2263474 : term377 = True.
Proof. exact (TRANS (@lem2263469) (@lem2263473)). Qed.
Lemma lem2263475 : True = term377.
Proof. exact (SYM (@lem2263474)). Qed.
Lemma lem2263476 : term377.
Proof. exact (EQ_MP (@lem2263475) (@lem0)). Qed.
Lemma lem2263477 : term416.
Proof. exact (@lem2263466 (@lem2263476)). Qed.
Lemma lem2263479 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263480 : term377 = term383.
Proof. exact (@lem2263479 (NUMERAL 0) term32). Qed.
Lemma lem2263481 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263482 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263483 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263482 h1) (fun h1 : term383 = True => @lem2263481)). Qed.
Lemma lem2263484 : term383 = True.
Proof. exact (EQ_MP (@lem2263483) (@lem2263481)). Qed.
Lemma lem2263485 : term377 = True.
Proof. exact (TRANS (@lem2263480) (@lem2263484)). Qed.
Lemma lem2263486 : True = term377.
Proof. exact (SYM (@lem2263485)). Qed.
Lemma lem2263487 : term377.
Proof. exact (EQ_MP (@lem2263486) (@lem0)). Qed.
Lemma lem2263488 : term417.
Proof. exact (@lem2263477 (@lem2263487)). Qed.
Lemma lem2263490 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263491 : term41 = term42.
Proof. exact (@lem2263490 term32 term32). Qed.
Lemma lem2263492 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263493 : term44 = term32.
Proof. exact (EQ_MP (@lem2263492) (@lem940073)). Qed.
Lemma lem2263494 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263495 : term42 = term38.
Proof. exact (MK_COMB (@lem2263494) (@lem2263493)). Qed.
Lemma lem2263496 : term41 = term38.
Proof. exact (TRANS (@lem2263491) (@lem2263495)). Qed.
Lemma lem2263498 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2263499 : term420 = term421.
Proof. exact (@lem2263498 term32 term32). Qed.
Lemma lem2263500 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263501 : term44 = term32.
Proof. exact (EQ_MP (@lem2263500) (@lem940073)). Qed.
Lemma lem2263502 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263503 : term42 = term38.
Proof. exact (MK_COMB (@lem2263502) (@lem2263501)). Qed.
Lemma lem2263504 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2263505 : term421 = term26.
Proof. exact (MK_COMB (@lem2263504) (@lem2263503)). Qed.
Lemma lem2263506 : term420 = term26.
Proof. exact (TRANS (@lem2263499) (@lem2263505)). Qed.
Lemma lem2263507 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263508 : term422 = term410.
Proof. exact (MK_COMB (@lem2263507) (@lem2263506)). Qed.
Lemma lem2263509 : term423 = term412.
Proof. exact (MK_COMB (@lem2263508) (@lem2263496)). Qed.
Lemma lem2263511 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2263512 : term412 = term14.
Proof. exact (@lem2263511 term32). Qed.
Lemma lem2263513 : term423 = term14.
Proof. exact (TRANS (@lem2263509) (@lem2263512)). Qed.
Lemma lem2263514 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263515 : term425 = term426.
Proof. exact (MK_COMB (@lem2263514) (@lem2263513)). Qed.
Lemma lem2263516 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2263517 : term427 = term388.
Proof. exact (MK_COMB (@lem2263515) (@lem2263516)). Qed.
Lemma lem2263519 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263520 : term388 = term14.
Proof. exact (@lem2263519 term32). Qed.
Lemma lem2263521 : term427 = term14.
Proof. exact (TRANS (@lem2263517) (@lem2263520)). Qed.
Lemma lem2263523 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263524 : term41 = term42.
Proof. exact (@lem2263523 term32 term32). Qed.
Lemma lem2263525 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263526 : term44 = term32.
Proof. exact (EQ_MP (@lem2263525) (@lem940073)). Qed.
Lemma lem2263527 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263528 : term42 = term38.
Proof. exact (MK_COMB (@lem2263527) (@lem2263526)). Qed.
Lemma lem2263529 : term41 = term38.
Proof. exact (TRANS (@lem2263524) (@lem2263528)). Qed.
Lemma lem2263530 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2263531 : term428 = term388.
Proof. exact (MK_COMB (@lem2263530) (@lem2263529)). Qed.
Lemma lem2263533 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263534 : term388 = term14.
Proof. exact (@lem2263533 term32). Qed.
Lemma lem2263535 : term428 = term14.
Proof. exact (TRANS (@lem2263531) (@lem2263534)). Qed.
Lemma lem2263536 : term14 = term428.
Proof. exact (SYM (@lem2263535)). Qed.
Lemma lem2263537 : term427 = term428.
Proof. exact (TRANS (@lem2263521) (@lem2263536)). Qed.
Lemma lem2263538 : term413 = term180.
Proof. exact (@lem2263488 (@lem2263537)). Qed.
Lemma lem2263539 : term412 = term180.
Proof. exact (TRANS (@lem2263454) (@lem2263538)). Qed.
Lemma lem2263541 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2263542 : term180 = term14.
Proof. exact (@lem2263541 term14). Qed.
Lemma lem2263543 : term412 = term14.
Proof. exact (TRANS (@lem2263539) (@lem2263542)). Qed.
Lemma lem2263544 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263545 : term429 = term426.
Proof. exact (MK_COMB (@lem2263544) (@lem2263543)). Qed.
Lemma lem2263546 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2263547 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2263545) (@lem2263546 x)). Qed.
Lemma lem2263548 (x : real) : (term474 x) = (term430 x).
Proof. exact (TRANS (@lem2263445 x) (@lem2263547 x)). Qed.
Lemma lem2263549 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2263550 (x : real) : (term474 x) = term14.
Proof. exact (TRANS (@lem2263548 x) (@lem2263549 x)). Qed.
Lemma lem2263551 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263552 (x : real) : (term475 x) = term432.
Proof. exact (MK_COMB (@lem2263551) (@lem2263550 x)). Qed.
Lemma lem2263553 (n : nat) : (term460 n) = (term434 n).
Proof. exact (@lem1982713 term26 (real_of_num n)). Qed.
Lemma lem2263555 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263556 : term38 = term48.
Proof. exact (@lem2263555 term32). Qed.
Lemma lem2263558 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263559 : term26 = term31.
Proof. exact (@lem2263558 term32). Qed.
Lemma lem2263560 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263561 : term410 = term411.
Proof. exact (MK_COMB (@lem2263560) (@lem2263559)). Qed.
Lemma lem2263562 : term412 = term413.
Proof. exact (MK_COMB (@lem2263561) (@lem2263556)). Qed.
Lemma lem2263563 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2263565 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263566 : term377 = term383.
Proof. exact (@lem2263565 (NUMERAL 0) term32). Qed.
Lemma lem2263567 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263568 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263569 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263568 h1) (fun h1 : term383 = True => @lem2263567)). Qed.
Lemma lem2263570 : term383 = True.
Proof. exact (EQ_MP (@lem2263569) (@lem2263567)). Qed.
Lemma lem2263571 : term377 = True.
Proof. exact (TRANS (@lem2263566) (@lem2263570)). Qed.
Lemma lem2263572 : True = term377.
Proof. exact (SYM (@lem2263571)). Qed.
Lemma lem2263573 : term377.
Proof. exact (EQ_MP (@lem2263572) (@lem0)). Qed.
Lemma lem2263574 : term415.
Proof. exact (@lem2263563 (@lem2263573)). Qed.
Lemma lem2263576 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263577 : term377 = term383.
Proof. exact (@lem2263576 (NUMERAL 0) term32). Qed.
Lemma lem2263578 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263579 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263580 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263579 h1) (fun h1 : term383 = True => @lem2263578)). Qed.
Lemma lem2263581 : term383 = True.
Proof. exact (EQ_MP (@lem2263580) (@lem2263578)). Qed.
Lemma lem2263582 : term377 = True.
Proof. exact (TRANS (@lem2263577) (@lem2263581)). Qed.
Lemma lem2263583 : True = term377.
Proof. exact (SYM (@lem2263582)). Qed.
Lemma lem2263584 : term377.
Proof. exact (EQ_MP (@lem2263583) (@lem0)). Qed.
Lemma lem2263585 : term416.
Proof. exact (@lem2263574 (@lem2263584)). Qed.
Lemma lem2263587 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263588 : term377 = term383.
Proof. exact (@lem2263587 (NUMERAL 0) term32). Qed.
Lemma lem2263589 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263590 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263591 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263590 h1) (fun h1 : term383 = True => @lem2263589)). Qed.
Lemma lem2263592 : term383 = True.
Proof. exact (EQ_MP (@lem2263591) (@lem2263589)). Qed.
Lemma lem2263593 : term377 = True.
Proof. exact (TRANS (@lem2263588) (@lem2263592)). Qed.
Lemma lem2263594 : True = term377.
Proof. exact (SYM (@lem2263593)). Qed.
Lemma lem2263595 : term377.
Proof. exact (EQ_MP (@lem2263594) (@lem0)). Qed.
Lemma lem2263596 : term417.
Proof. exact (@lem2263585 (@lem2263595)). Qed.
Lemma lem2263598 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263599 : term41 = term42.
Proof. exact (@lem2263598 term32 term32). Qed.
Lemma lem2263600 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263601 : term44 = term32.
Proof. exact (EQ_MP (@lem2263600) (@lem940073)). Qed.
Lemma lem2263602 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263603 : term42 = term38.
Proof. exact (MK_COMB (@lem2263602) (@lem2263601)). Qed.
Lemma lem2263604 : term41 = term38.
Proof. exact (TRANS (@lem2263599) (@lem2263603)). Qed.
Lemma lem2263606 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2263607 : term420 = term421.
Proof. exact (@lem2263606 term32 term32). Qed.
Lemma lem2263608 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263609 : term44 = term32.
Proof. exact (EQ_MP (@lem2263608) (@lem940073)). Qed.
Lemma lem2263610 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263611 : term42 = term38.
Proof. exact (MK_COMB (@lem2263610) (@lem2263609)). Qed.
Lemma lem2263612 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2263613 : term421 = term26.
Proof. exact (MK_COMB (@lem2263612) (@lem2263611)). Qed.
Lemma lem2263614 : term420 = term26.
Proof. exact (TRANS (@lem2263607) (@lem2263613)). Qed.
Lemma lem2263615 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263616 : term422 = term410.
Proof. exact (MK_COMB (@lem2263615) (@lem2263614)). Qed.
Lemma lem2263617 : term423 = term412.
Proof. exact (MK_COMB (@lem2263616) (@lem2263604)). Qed.
Lemma lem2263619 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2263620 : term412 = term14.
Proof. exact (@lem2263619 term32). Qed.
Lemma lem2263621 : term423 = term14.
Proof. exact (TRANS (@lem2263617) (@lem2263620)). Qed.
Lemma lem2263622 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263623 : term425 = term426.
Proof. exact (MK_COMB (@lem2263622) (@lem2263621)). Qed.
Lemma lem2263624 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2263625 : term427 = term388.
Proof. exact (MK_COMB (@lem2263623) (@lem2263624)). Qed.
Lemma lem2263627 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263628 : term388 = term14.
Proof. exact (@lem2263627 term32). Qed.
Lemma lem2263629 : term427 = term14.
Proof. exact (TRANS (@lem2263625) (@lem2263628)). Qed.
Lemma lem2263631 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263632 : term41 = term42.
Proof. exact (@lem2263631 term32 term32). Qed.
Lemma lem2263633 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263634 : term44 = term32.
Proof. exact (EQ_MP (@lem2263633) (@lem940073)). Qed.
Lemma lem2263635 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263636 : term42 = term38.
Proof. exact (MK_COMB (@lem2263635) (@lem2263634)). Qed.
Lemma lem2263637 : term41 = term38.
Proof. exact (TRANS (@lem2263632) (@lem2263636)). Qed.
Lemma lem2263638 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2263639 : term428 = term388.
Proof. exact (MK_COMB (@lem2263638) (@lem2263637)). Qed.
Lemma lem2263641 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263642 : term388 = term14.
Proof. exact (@lem2263641 term32). Qed.
Lemma lem2263643 : term428 = term14.
Proof. exact (TRANS (@lem2263639) (@lem2263642)). Qed.
Lemma lem2263644 : term14 = term428.
Proof. exact (SYM (@lem2263643)). Qed.
Lemma lem2263645 : term427 = term428.
Proof. exact (TRANS (@lem2263629) (@lem2263644)). Qed.
Lemma lem2263646 : term413 = term180.
Proof. exact (@lem2263596 (@lem2263645)). Qed.
Lemma lem2263647 : term412 = term180.
Proof. exact (TRANS (@lem2263562) (@lem2263646)). Qed.
Lemma lem2263649 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2263650 : term180 = term14.
Proof. exact (@lem2263649 term14). Qed.
Lemma lem2263651 : term412 = term14.
Proof. exact (TRANS (@lem2263647) (@lem2263650)). Qed.
Lemma lem2263652 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263653 : term429 = term426.
Proof. exact (MK_COMB (@lem2263652) (@lem2263651)). Qed.
Lemma lem2263654 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2263655 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2263653) (@lem2263654 n)). Qed.
Lemma lem2263656 (n : nat) : (term460 n) = (term387 n).
Proof. exact (TRANS (@lem2263553 n) (@lem2263655 n)). Qed.
Lemma lem2263657 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2263658 (n : nat) : (term460 n) = term14.
Proof. exact (TRANS (@lem2263656 n) (@lem2263657 n)). Qed.
Lemma lem2263659 (x : real) (n : nat) : (term473 x n) = term435.
Proof. exact (MK_COMB (@lem2263552 x) (@lem2263658 n)). Qed.
Lemma lem2263660 (x : real) (n : nat) : (term472 x n) = term435.
Proof. exact (TRANS (@lem2263444 x n) (@lem2263659 x n)). Qed.
Lemma lem2263661 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2263662 (x : real) (n : nat) : (term472 x n) = term14.
Proof. exact (TRANS (@lem2263660 x n) (@lem2263661)). Qed.
Lemma lem2263663 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2263664 (x : real) (n : nat) : (term476 x n) = term437.
Proof. exact (MK_COMB (@lem2263663) (@lem2263662 x n)). Qed.
Lemma lem2263665 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2263666 (x : real) (n : nat) : (term471 x n) = term438.
Proof. exact (MK_COMB (@lem2263664 x n) (@lem2263665)). Qed.
Lemma lem2263667 (x : real) (n : nat) (h1 : term290 x n) : term438.
Proof. exact (EQ_MP (@lem2263666 x n) (@lem2263443 x n h1)). Qed.
Lemma lem2263669 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2263670 : term438 = term439.
Proof. exact (@lem2263669 term14 term14). Qed.
Lemma lem2263672 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263673 : term14 = term180.
Proof. exact (@lem2263672 (NUMERAL 0)). Qed.
Lemma lem2263675 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263676 : term14 = term180.
Proof. exact (@lem2263675 (NUMERAL 0)). Qed.
Lemma lem2263677 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2263678 : term378 = term379.
Proof. exact (MK_COMB (@lem2263677) (@lem2263676)). Qed.
Lemma lem2263679 : term439 = term440.
Proof. exact (MK_COMB (@lem2263678) (@lem2263673)). Qed.
Lemma lem2263680 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2263682 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263683 : term377 = term383.
Proof. exact (@lem2263682 (NUMERAL 0) term32). Qed.
Lemma lem2263684 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263685 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263686 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263685 h1) (fun h1 : term383 = True => @lem2263684)). Qed.
Lemma lem2263687 : term383 = True.
Proof. exact (EQ_MP (@lem2263686) (@lem2263684)). Qed.
Lemma lem2263688 : term377 = True.
Proof. exact (TRANS (@lem2263683) (@lem2263687)). Qed.
Lemma lem2263689 : True = term377.
Proof. exact (SYM (@lem2263688)). Qed.
Lemma lem2263690 : term377.
Proof. exact (EQ_MP (@lem2263689) (@lem0)). Qed.
Lemma lem2263691 : term442.
Proof. exact (@lem2263680 (@lem2263690)). Qed.
Lemma lem2263693 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263694 : term377 = term383.
Proof. exact (@lem2263693 (NUMERAL 0) term32). Qed.
Lemma lem2263695 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263696 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263697 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263696 h1) (fun h1 : term383 = True => @lem2263695)). Qed.
Lemma lem2263698 : term383 = True.
Proof. exact (EQ_MP (@lem2263697) (@lem2263695)). Qed.
Lemma lem2263699 : term377 = True.
Proof. exact (TRANS (@lem2263694) (@lem2263698)). Qed.
Lemma lem2263700 : True = term377.
Proof. exact (SYM (@lem2263699)). Qed.
Lemma lem2263701 : term377.
Proof. exact (EQ_MP (@lem2263700) (@lem0)). Qed.
Lemma lem2263702 : term440 = term443.
Proof. exact (@lem2263691 (@lem2263701)). Qed.
Lemma lem2263704 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263705 : term388 = term14.
Proof. exact (@lem2263704 term32). Qed.
Lemma lem2263707 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263708 : term388 = term14.
Proof. exact (@lem2263707 term32). Qed.
Lemma lem2263709 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2263710 : term389 = term378.
Proof. exact (MK_COMB (@lem2263709) (@lem2263708)). Qed.
Lemma lem2263711 : term443 = term439.
Proof. exact (MK_COMB (@lem2263710) (@lem2263705)). Qed.
Lemma lem2263713 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263714 : term439 = term444.
Proof. exact (@lem2263713 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2263715 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2263716 : term439 = False.
Proof. exact (TRANS (@lem2263714) (@lem2263715)). Qed.
Lemma lem2263717 : term443 = False.
Proof. exact (TRANS (@lem2263711) (@lem2263716)). Qed.
Lemma lem2263718 : term440 = False.
Proof. exact (TRANS (@lem2263702) (@lem2263717)). Qed.
Lemma lem2263719 : term439 = False.
Proof. exact (TRANS (@lem2263679) (@lem2263718)). Qed.
Lemma lem2263720 : term438 = False.
Proof. exact (TRANS (@lem2263670) (@lem2263719)). Qed.
Lemma lem2263721 (x : real) (n : nat) (h1 : term290 x n) : False.
Proof. exact (EQ_MP (@lem2263720) (@lem2263667 x n h1)). Qed.
Lemma lem2263722 (x : real) (n : nat) (h1 : term296 x n) : term296 x n.
Proof. exact (h1). Qed.
Lemma lem2263723 (x : real) (n : nat) (h1 : term296 x n) : term295 x n.
Proof. exact (proj2 (@lem2263722 x n h1)). Qed.
Lemma lem2263725 (x : real) (n : nat) (h1 : term296 x n) : term147 x n.
Proof. exact (proj2 (@lem2263723 x n h1)). Qed.
Lemma lem2263726 (x : real) (n : nat) (h1 : term296 x n) : (term76 x n) = term14.
Proof. exact (proj1 (@lem2263723 x n h1)). Qed.
Lemma lem2263727 (x : real) (n : nat) (h1 : term296 x n) : term81 x n.
Proof. exact (proj2 (@lem2263725 x n h1)). Qed.
Lemma lem2263731 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2263732 : term376 = term377.
Proof. exact (@lem2263731 term14 term38). Qed.
Lemma lem2263734 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263735 : term38 = term48.
Proof. exact (@lem2263734 term32). Qed.
Lemma lem2263737 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263738 : term14 = term180.
Proof. exact (@lem2263737 (NUMERAL 0)). Qed.
Lemma lem2263739 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2263740 : term378 = term379.
Proof. exact (MK_COMB (@lem2263739) (@lem2263738)). Qed.
Lemma lem2263741 : term377 = term380.
Proof. exact (MK_COMB (@lem2263740) (@lem2263735)). Qed.
Lemma lem2263742 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2263744 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263745 : term377 = term383.
Proof. exact (@lem2263744 (NUMERAL 0) term32). Qed.
Lemma lem2263746 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263747 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263748 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263747 h1) (fun h1 : term383 = True => @lem2263746)). Qed.
Lemma lem2263749 : term383 = True.
Proof. exact (EQ_MP (@lem2263748) (@lem2263746)). Qed.
Lemma lem2263750 : term377 = True.
Proof. exact (TRANS (@lem2263745) (@lem2263749)). Qed.
Lemma lem2263751 : True = term377.
Proof. exact (SYM (@lem2263750)). Qed.
Lemma lem2263752 : term377.
Proof. exact (EQ_MP (@lem2263751) (@lem0)). Qed.
Lemma lem2263753 : term385.
Proof. exact (@lem2263742 (@lem2263752)). Qed.
Lemma lem2263755 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263756 : term377 = term383.
Proof. exact (@lem2263755 (NUMERAL 0) term32). Qed.
Lemma lem2263757 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263758 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263759 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263758 h1) (fun h1 : term383 = True => @lem2263757)). Qed.
Lemma lem2263760 : term383 = True.
Proof. exact (EQ_MP (@lem2263759) (@lem2263757)). Qed.
Lemma lem2263761 : term377 = True.
Proof. exact (TRANS (@lem2263756) (@lem2263760)). Qed.
Lemma lem2263762 : True = term377.
Proof. exact (SYM (@lem2263761)). Qed.
Lemma lem2263763 : term377.
Proof. exact (EQ_MP (@lem2263762) (@lem0)). Qed.
Lemma lem2263764 : term380 = term386.
Proof. exact (@lem2263753 (@lem2263763)). Qed.
Lemma lem2263766 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263767 : term41 = term42.
Proof. exact (@lem2263766 term32 term32). Qed.
Lemma lem2263768 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263769 : term44 = term32.
Proof. exact (EQ_MP (@lem2263768) (@lem940073)). Qed.
Lemma lem2263770 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263771 : term42 = term38.
Proof. exact (MK_COMB (@lem2263770) (@lem2263769)). Qed.
Lemma lem2263772 : term41 = term38.
Proof. exact (TRANS (@lem2263767) (@lem2263771)). Qed.
Lemma lem2263774 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263775 : term388 = term14.
Proof. exact (@lem2263774 term32). Qed.
Lemma lem2263776 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2263777 : term389 = term378.
Proof. exact (MK_COMB (@lem2263776) (@lem2263775)). Qed.
Lemma lem2263778 : term386 = term377.
Proof. exact (MK_COMB (@lem2263777) (@lem2263772)). Qed.
Lemma lem2263780 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263781 : term377 = term383.
Proof. exact (@lem2263780 (NUMERAL 0) term32). Qed.
Lemma lem2263782 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263783 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263784 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263783 h1) (fun h1 : term383 = True => @lem2263782)). Qed.
Lemma lem2263785 : term383 = True.
Proof. exact (EQ_MP (@lem2263784) (@lem2263782)). Qed.
Lemma lem2263786 : term377 = True.
Proof. exact (TRANS (@lem2263781) (@lem2263785)). Qed.
Lemma lem2263787 : term386 = True.
Proof. exact (TRANS (@lem2263778) (@lem2263786)). Qed.
Lemma lem2263788 : term380 = True.
Proof. exact (TRANS (@lem2263764) (@lem2263787)). Qed.
Lemma lem2263789 : term377 = True.
Proof. exact (TRANS (@lem2263741) (@lem2263788)). Qed.
Lemma lem2263790 : term376 = True.
Proof. exact (TRANS (@lem2263732) (@lem2263789)). Qed.
Lemma lem2263791 : True = term376.
Proof. exact (SYM (@lem2263790)). Qed.
Lemma lem2263792 : term376.
Proof. exact (EQ_MP (@lem2263791) (@lem0)). Qed.
Lemma lem2263793 (x : real) (n : nat) (h1 : term296 x n) : term477 x n.
Proof. exact (conj (@lem2263792) (@lem2263727 x n h1)). Qed.
Lemma lem2263795 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2263796 (x : real) (n : nat) : term478 x n.
Proof. exact (@lem2263795 term38 (term76 x n)). Qed.
Lemma lem2263797 (x : real) (n : nat) (h1 : term296 x n) : term479 x n.
Proof. exact (@lem2263796 x n (@lem2263793 x n h1)). Qed.
Lemma lem2263798 (x : real) (n : nat) : (term453 x n) = (term76 x n).
Proof. exact (@lem1982733 (term76 x n)). Qed.
Lemma lem2263799 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2263800 (x : real) (n : nat) : (term480 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem2263799) (@lem2263798 x n)). Qed.
Lemma lem2263801 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2263802 (x : real) (n : nat) : (term479 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2263800 x n) (@lem2263801)). Qed.
Lemma lem2263803 (x : real) (n : nat) (h1 : term296 x n) : term81 x n.
Proof. exact (EQ_MP (@lem2263802 x n) (@lem2263797 x n h1)). Qed.
Lemma lem2263805 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2263806 (x : real) (n : nat) : term450 x n.
Proof. exact (@lem2263805 (term76 x n)). Qed.
Lemma lem2263807 (x : real) (n : nat) (h1 : term296 x n) : term451 x n.
Proof. exact (@lem2263806 x n (@lem2263726 x n h1)). Qed.
Lemma lem2263808 (x : real) (n : nat) (h1 : term296 x n) : term481 x n.
Proof. exact (@lem2263807 x n h1 term26). Qed.
Lemma lem2263809 (x : real) (n : nat) : (term481 x n) = ((term482 x n) = term14).
Proof. exact (eq_refl (term481 x n)). Qed.
Lemma lem2263810 (x : real) (n : nat) (h1 : term296 x n) : (term482 x n) = term14.
Proof. exact (EQ_MP (@lem2263809 x n) (@lem2263808 x n h1)). Qed.
Lemma lem2263811 (x : real) (n : nat) : (term482 x n) = (term483 x n).
Proof. exact (@lem1982781 (term208 x) term26 (term27 n)). Qed.
Lemma lem2263812 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2263814 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263815 : term26 = term31.
Proof. exact (@lem2263814 term32). Qed.
Lemma lem2263817 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263818 : term26 = term31.
Proof. exact (@lem2263817 term32). Qed.
Lemma lem2263819 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263820 : term33 = term34.
Proof. exact (MK_COMB (@lem2263819) (@lem2263818)). Qed.
Lemma lem2263821 : term35 = term36.
Proof. exact (MK_COMB (@lem2263820) (@lem2263815)). Qed.
Lemma lem2263822 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2263824 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263825 : term41 = term42.
Proof. exact (@lem2263824 term32 term32). Qed.
Lemma lem2263826 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263827 : term44 = term32.
Proof. exact (EQ_MP (@lem2263826) (@lem940073)). Qed.
Lemma lem2263828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263829 : term42 = term38.
Proof. exact (MK_COMB (@lem2263828) (@lem2263827)). Qed.
Lemma lem2263830 : term41 = term38.
Proof. exact (TRANS (@lem2263825) (@lem2263829)). Qed.
Lemma lem2263832 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2263833 : term35 = term42.
Proof. exact (@lem2263832 term32 term32). Qed.
Lemma lem2263834 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263835 : term44 = term32.
Proof. exact (EQ_MP (@lem2263834) (@lem940073)). Qed.
Lemma lem2263836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263837 : term42 = term38.
Proof. exact (MK_COMB (@lem2263836) (@lem2263835)). Qed.
Lemma lem2263838 : term35 = term38.
Proof. exact (TRANS (@lem2263833) (@lem2263837)). Qed.
Lemma lem2263839 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2263840 : term46 = term47.
Proof. exact (MK_COMB (@lem2263839) (@lem2263838)). Qed.
Lemma lem2263841 : term37 = term48.
Proof. exact (MK_COMB (@lem2263840) (@lem2263830)). Qed.
Lemma lem2263842 : term36 = term48.
Proof. exact (TRANS (@lem2263822) (@lem2263841)). Qed.
Lemma lem2263843 : term35 = term48.
Proof. exact (TRANS (@lem2263821) (@lem2263842)). Qed.
Lemma lem2263845 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2263846 : term48 = term38.
Proof. exact (@lem2263845 term38). Qed.
Lemma lem2263847 : term35 = term38.
Proof. exact (TRANS (@lem2263843) (@lem2263846)). Qed.
Lemma lem2263848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263849 : term50 = term51.
Proof. exact (MK_COMB (@lem2263848) (@lem2263847)). Qed.
Lemma lem2263850 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2263851 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2263849) (@lem2263850 n)). Qed.
Lemma lem2263852 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2263812 n) (@lem2263851 n)). Qed.
Lemma lem2263853 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2263854 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2263852 n) (@lem2263853 n)). Qed.
Lemma lem2263855 (x : real) : (term484 x) = (term485 x).
Proof. exact (@lem1982749 term26 term26 x). Qed.
Lemma lem2263857 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263858 : term26 = term31.
Proof. exact (@lem2263857 term32). Qed.
Lemma lem2263860 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263861 : term26 = term31.
Proof. exact (@lem2263860 term32). Qed.
Lemma lem2263862 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263863 : term33 = term34.
Proof. exact (MK_COMB (@lem2263862) (@lem2263861)). Qed.
Lemma lem2263864 : term35 = term36.
Proof. exact (MK_COMB (@lem2263863) (@lem2263858)). Qed.
Lemma lem2263865 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2263867 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263868 : term41 = term42.
Proof. exact (@lem2263867 term32 term32). Qed.
Lemma lem2263869 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263870 : term44 = term32.
Proof. exact (EQ_MP (@lem2263869) (@lem940073)). Qed.
Lemma lem2263871 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263872 : term42 = term38.
Proof. exact (MK_COMB (@lem2263871) (@lem2263870)). Qed.
Lemma lem2263873 : term41 = term38.
Proof. exact (TRANS (@lem2263868) (@lem2263872)). Qed.
Lemma lem2263875 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2263876 : term35 = term42.
Proof. exact (@lem2263875 term32 term32). Qed.
Lemma lem2263877 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263878 : term44 = term32.
Proof. exact (EQ_MP (@lem2263877) (@lem940073)). Qed.
Lemma lem2263879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263880 : term42 = term38.
Proof. exact (MK_COMB (@lem2263879) (@lem2263878)). Qed.
Lemma lem2263881 : term35 = term38.
Proof. exact (TRANS (@lem2263876) (@lem2263880)). Qed.
Lemma lem2263882 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2263883 : term46 = term47.
Proof. exact (MK_COMB (@lem2263882) (@lem2263881)). Qed.
Lemma lem2263884 : term37 = term48.
Proof. exact (MK_COMB (@lem2263883) (@lem2263873)). Qed.
Lemma lem2263885 : term36 = term48.
Proof. exact (TRANS (@lem2263865) (@lem2263884)). Qed.
Lemma lem2263886 : term35 = term48.
Proof. exact (TRANS (@lem2263864) (@lem2263885)). Qed.
Lemma lem2263888 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2263889 : term48 = term38.
Proof. exact (@lem2263888 term38). Qed.
Lemma lem2263890 : term35 = term38.
Proof. exact (TRANS (@lem2263886) (@lem2263889)). Qed.
Lemma lem2263891 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263892 : term50 = term51.
Proof. exact (MK_COMB (@lem2263891) (@lem2263890)). Qed.
Lemma lem2263893 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2263894 (x : real) : (term485 x) = (term330 x).
Proof. exact (MK_COMB (@lem2263892) (@lem2263893 x)). Qed.
Lemma lem2263895 (x : real) : (term484 x) = (term330 x).
Proof. exact (TRANS (@lem2263855 x) (@lem2263894 x)). Qed.
Lemma lem2263896 (x : real) : (term330 x) = x.
Proof. exact (@lem1982709 x). Qed.
Lemma lem2263897 (x : real) : (term484 x) = x.
Proof. exact (TRANS (@lem2263895 x) (@lem2263896 x)). Qed.
Lemma lem2263898 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263899 (x : real) : (term486 x) = (real_add x).
Proof. exact (MK_COMB (@lem2263898) (@lem2263897 x)). Qed.
Lemma lem2263900 (x : real) (n : nat) : (term483 x n) = (term72 x n).
Proof. exact (MK_COMB (@lem2263899 x) (@lem2263854 n)). Qed.
Lemma lem2263901 (x : real) (n : nat) : (term482 x n) = (term72 x n).
Proof. exact (TRANS (@lem2263811 x n) (@lem2263900 x n)). Qed.
Lemma lem2263902 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2263903 (x : real) (n : nat) : (term487 x n) = (term117 x n).
Proof. exact (MK_COMB (@lem2263902) (@lem2263901 x n)). Qed.
Lemma lem2263904 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2263905 (x : real) (n : nat) : ((term482 x n) = term14) = ((term72 x n) = term14).
Proof. exact (MK_COMB (@lem2263903 x n) (@lem2263904)). Qed.
Lemma lem2263906 (x : real) (n : nat) (h1 : term296 x n) : (term72 x n) = term14.
Proof. exact (EQ_MP (@lem2263905 x n) (@lem2263810 x n h1)). Qed.
Lemma lem2263907 (x : real) (n : nat) (h1 : term296 x n) : term488 x n.
Proof. exact (conj (@lem2263906 x n h1) (@lem2263803 x n h1)). Qed.
Lemma lem2263909 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2263910 (x : real) (n : nat) : term489 x n.
Proof. exact (@lem2263909 (term72 x n) (term76 x n)). Qed.
Lemma lem2263911 (x : real) (n : nat) (h1 : term296 x n) : term490 x n.
Proof. exact (@lem2263910 x n (@lem2263907 x n h1)). Qed.
Lemma lem2263912 (x : real) (n : nat) : (term491 x n) = (term492 x n).
Proof. exact (@lem1982753 x (term208 x) (real_of_num n) (term27 n)). Qed.
Lemma lem2263913 (x : real) : (term474 x) = (term409 x).
Proof. exact (@lem1982715 term26 x). Qed.
Lemma lem2263915 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2263916 : term38 = term48.
Proof. exact (@lem2263915 term32). Qed.
Lemma lem2263918 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2263919 : term26 = term31.
Proof. exact (@lem2263918 term32). Qed.
Lemma lem2263920 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263921 : term410 = term411.
Proof. exact (MK_COMB (@lem2263920) (@lem2263919)). Qed.
Lemma lem2263922 : term412 = term413.
Proof. exact (MK_COMB (@lem2263921) (@lem2263916)). Qed.
Lemma lem2263923 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2263925 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263926 : term377 = term383.
Proof. exact (@lem2263925 (NUMERAL 0) term32). Qed.
Lemma lem2263927 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263928 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263929 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263928 h1) (fun h1 : term383 = True => @lem2263927)). Qed.
Lemma lem2263930 : term383 = True.
Proof. exact (EQ_MP (@lem2263929) (@lem2263927)). Qed.
Lemma lem2263931 : term377 = True.
Proof. exact (TRANS (@lem2263926) (@lem2263930)). Qed.
Lemma lem2263932 : True = term377.
Proof. exact (SYM (@lem2263931)). Qed.
Lemma lem2263933 : term377.
Proof. exact (EQ_MP (@lem2263932) (@lem0)). Qed.
Lemma lem2263934 : term415.
Proof. exact (@lem2263923 (@lem2263933)). Qed.
Lemma lem2263936 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263937 : term377 = term383.
Proof. exact (@lem2263936 (NUMERAL 0) term32). Qed.
Lemma lem2263938 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263939 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263940 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263939 h1) (fun h1 : term383 = True => @lem2263938)). Qed.
Lemma lem2263941 : term383 = True.
Proof. exact (EQ_MP (@lem2263940) (@lem2263938)). Qed.
Lemma lem2263942 : term377 = True.
Proof. exact (TRANS (@lem2263937) (@lem2263941)). Qed.
Lemma lem2263943 : True = term377.
Proof. exact (SYM (@lem2263942)). Qed.
Lemma lem2263944 : term377.
Proof. exact (EQ_MP (@lem2263943) (@lem0)). Qed.
Lemma lem2263945 : term416.
Proof. exact (@lem2263934 (@lem2263944)). Qed.
Lemma lem2263947 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2263948 : term377 = term383.
Proof. exact (@lem2263947 (NUMERAL 0) term32). Qed.
Lemma lem2263949 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2263950 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2263951 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2263950 h1) (fun h1 : term383 = True => @lem2263949)). Qed.
Lemma lem2263952 : term383 = True.
Proof. exact (EQ_MP (@lem2263951) (@lem2263949)). Qed.
Lemma lem2263953 : term377 = True.
Proof. exact (TRANS (@lem2263948) (@lem2263952)). Qed.
Lemma lem2263954 : True = term377.
Proof. exact (SYM (@lem2263953)). Qed.
Lemma lem2263955 : term377.
Proof. exact (EQ_MP (@lem2263954) (@lem0)). Qed.
Lemma lem2263956 : term417.
Proof. exact (@lem2263945 (@lem2263955)). Qed.
Lemma lem2263958 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263959 : term41 = term42.
Proof. exact (@lem2263958 term32 term32). Qed.
Lemma lem2263960 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263961 : term44 = term32.
Proof. exact (EQ_MP (@lem2263960) (@lem940073)). Qed.
Lemma lem2263962 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263963 : term42 = term38.
Proof. exact (MK_COMB (@lem2263962) (@lem2263961)). Qed.
Lemma lem2263964 : term41 = term38.
Proof. exact (TRANS (@lem2263959) (@lem2263963)). Qed.
Lemma lem2263966 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2263967 : term420 = term421.
Proof. exact (@lem2263966 term32 term32). Qed.
Lemma lem2263968 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263969 : term44 = term32.
Proof. exact (EQ_MP (@lem2263968) (@lem940073)). Qed.
Lemma lem2263970 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263971 : term42 = term38.
Proof. exact (MK_COMB (@lem2263970) (@lem2263969)). Qed.
Lemma lem2263972 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2263973 : term421 = term26.
Proof. exact (MK_COMB (@lem2263972) (@lem2263971)). Qed.
Lemma lem2263974 : term420 = term26.
Proof. exact (TRANS (@lem2263967) (@lem2263973)). Qed.
Lemma lem2263975 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2263976 : term422 = term410.
Proof. exact (MK_COMB (@lem2263975) (@lem2263974)). Qed.
Lemma lem2263977 : term423 = term412.
Proof. exact (MK_COMB (@lem2263976) (@lem2263964)). Qed.
Lemma lem2263979 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2263980 : term412 = term14.
Proof. exact (@lem2263979 term32). Qed.
Lemma lem2263981 : term423 = term14.
Proof. exact (TRANS (@lem2263977) (@lem2263980)). Qed.
Lemma lem2263982 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2263983 : term425 = term426.
Proof. exact (MK_COMB (@lem2263982) (@lem2263981)). Qed.
Lemma lem2263984 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2263985 : term427 = term388.
Proof. exact (MK_COMB (@lem2263983) (@lem2263984)). Qed.
Lemma lem2263987 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2263988 : term388 = term14.
Proof. exact (@lem2263987 term32). Qed.
Lemma lem2263989 : term427 = term14.
Proof. exact (TRANS (@lem2263985) (@lem2263988)). Qed.
Lemma lem2263991 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2263992 : term41 = term42.
Proof. exact (@lem2263991 term32 term32). Qed.
Lemma lem2263993 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2263994 : term44 = term32.
Proof. exact (EQ_MP (@lem2263993) (@lem940073)). Qed.
Lemma lem2263995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2263996 : term42 = term38.
Proof. exact (MK_COMB (@lem2263995) (@lem2263994)). Qed.
Lemma lem2263997 : term41 = term38.
Proof. exact (TRANS (@lem2263992) (@lem2263996)). Qed.
Lemma lem2263998 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2263999 : term428 = term388.
Proof. exact (MK_COMB (@lem2263998) (@lem2263997)). Qed.
Lemma lem2264001 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264002 : term388 = term14.
Proof. exact (@lem2264001 term32). Qed.
Lemma lem2264003 : term428 = term14.
Proof. exact (TRANS (@lem2263999) (@lem2264002)). Qed.
Lemma lem2264004 : term14 = term428.
Proof. exact (SYM (@lem2264003)). Qed.
Lemma lem2264005 : term427 = term428.
Proof. exact (TRANS (@lem2263989) (@lem2264004)). Qed.
Lemma lem2264006 : term413 = term180.
Proof. exact (@lem2263956 (@lem2264005)). Qed.
Lemma lem2264007 : term412 = term180.
Proof. exact (TRANS (@lem2263922) (@lem2264006)). Qed.
Lemma lem2264009 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2264010 : term180 = term14.
Proof. exact (@lem2264009 term14). Qed.
Lemma lem2264011 : term412 = term14.
Proof. exact (TRANS (@lem2264007) (@lem2264010)). Qed.
Lemma lem2264012 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264013 : term429 = term426.
Proof. exact (MK_COMB (@lem2264012) (@lem2264011)). Qed.
Lemma lem2264014 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2264015 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2264013) (@lem2264014 x)). Qed.
Lemma lem2264016 (x : real) : (term474 x) = (term430 x).
Proof. exact (TRANS (@lem2263913 x) (@lem2264015 x)). Qed.
Lemma lem2264017 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2264018 (x : real) : (term474 x) = term14.
Proof. exact (TRANS (@lem2264016 x) (@lem2264017 x)). Qed.
Lemma lem2264019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264020 (x : real) : (term475 x) = term432.
Proof. exact (MK_COMB (@lem2264019) (@lem2264018 x)). Qed.
Lemma lem2264021 (n : nat) : (term433 n) = (term434 n).
Proof. exact (@lem1982715 term26 (real_of_num n)). Qed.
Lemma lem2264023 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264024 : term38 = term48.
Proof. exact (@lem2264023 term32). Qed.
Lemma lem2264026 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2264027 : term26 = term31.
Proof. exact (@lem2264026 term32). Qed.
Lemma lem2264028 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264029 : term410 = term411.
Proof. exact (MK_COMB (@lem2264028) (@lem2264027)). Qed.
Lemma lem2264030 : term412 = term413.
Proof. exact (MK_COMB (@lem2264029) (@lem2264024)). Qed.
Lemma lem2264031 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2264033 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264034 : term377 = term383.
Proof. exact (@lem2264033 (NUMERAL 0) term32). Qed.
Lemma lem2264035 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264036 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264037 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264036 h1) (fun h1 : term383 = True => @lem2264035)). Qed.
Lemma lem2264038 : term383 = True.
Proof. exact (EQ_MP (@lem2264037) (@lem2264035)). Qed.
Lemma lem2264039 : term377 = True.
Proof. exact (TRANS (@lem2264034) (@lem2264038)). Qed.
Lemma lem2264040 : True = term377.
Proof. exact (SYM (@lem2264039)). Qed.
Lemma lem2264041 : term377.
Proof. exact (EQ_MP (@lem2264040) (@lem0)). Qed.
Lemma lem2264042 : term415.
Proof. exact (@lem2264031 (@lem2264041)). Qed.
Lemma lem2264044 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264045 : term377 = term383.
Proof. exact (@lem2264044 (NUMERAL 0) term32). Qed.
Lemma lem2264046 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264047 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264048 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264047 h1) (fun h1 : term383 = True => @lem2264046)). Qed.
Lemma lem2264049 : term383 = True.
Proof. exact (EQ_MP (@lem2264048) (@lem2264046)). Qed.
Lemma lem2264050 : term377 = True.
Proof. exact (TRANS (@lem2264045) (@lem2264049)). Qed.
Lemma lem2264051 : True = term377.
Proof. exact (SYM (@lem2264050)). Qed.
Lemma lem2264052 : term377.
Proof. exact (EQ_MP (@lem2264051) (@lem0)). Qed.
Lemma lem2264053 : term416.
Proof. exact (@lem2264042 (@lem2264052)). Qed.
Lemma lem2264055 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264056 : term377 = term383.
Proof. exact (@lem2264055 (NUMERAL 0) term32). Qed.
Lemma lem2264057 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264058 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264059 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264058 h1) (fun h1 : term383 = True => @lem2264057)). Qed.
Lemma lem2264060 : term383 = True.
Proof. exact (EQ_MP (@lem2264059) (@lem2264057)). Qed.
Lemma lem2264061 : term377 = True.
Proof. exact (TRANS (@lem2264056) (@lem2264060)). Qed.
Lemma lem2264062 : True = term377.
Proof. exact (SYM (@lem2264061)). Qed.
Lemma lem2264063 : term377.
Proof. exact (EQ_MP (@lem2264062) (@lem0)). Qed.
Lemma lem2264064 : term417.
Proof. exact (@lem2264053 (@lem2264063)). Qed.
Lemma lem2264066 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264067 : term41 = term42.
Proof. exact (@lem2264066 term32 term32). Qed.
Lemma lem2264068 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264069 : term44 = term32.
Proof. exact (EQ_MP (@lem2264068) (@lem940073)). Qed.
Lemma lem2264070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264071 : term42 = term38.
Proof. exact (MK_COMB (@lem2264070) (@lem2264069)). Qed.
Lemma lem2264072 : term41 = term38.
Proof. exact (TRANS (@lem2264067) (@lem2264071)). Qed.
Lemma lem2264074 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2264075 : term420 = term421.
Proof. exact (@lem2264074 term32 term32). Qed.
Lemma lem2264076 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264077 : term44 = term32.
Proof. exact (EQ_MP (@lem2264076) (@lem940073)). Qed.
Lemma lem2264078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264079 : term42 = term38.
Proof. exact (MK_COMB (@lem2264078) (@lem2264077)). Qed.
Lemma lem2264080 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2264081 : term421 = term26.
Proof. exact (MK_COMB (@lem2264080) (@lem2264079)). Qed.
Lemma lem2264082 : term420 = term26.
Proof. exact (TRANS (@lem2264075) (@lem2264081)). Qed.
Lemma lem2264083 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264084 : term422 = term410.
Proof. exact (MK_COMB (@lem2264083) (@lem2264082)). Qed.
Lemma lem2264085 : term423 = term412.
Proof. exact (MK_COMB (@lem2264084) (@lem2264072)). Qed.
Lemma lem2264087 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2264088 : term412 = term14.
Proof. exact (@lem2264087 term32). Qed.
Lemma lem2264089 : term423 = term14.
Proof. exact (TRANS (@lem2264085) (@lem2264088)). Qed.
Lemma lem2264090 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264091 : term425 = term426.
Proof. exact (MK_COMB (@lem2264090) (@lem2264089)). Qed.
Lemma lem2264092 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2264093 : term427 = term388.
Proof. exact (MK_COMB (@lem2264091) (@lem2264092)). Qed.
Lemma lem2264095 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264096 : term388 = term14.
Proof. exact (@lem2264095 term32). Qed.
Lemma lem2264097 : term427 = term14.
Proof. exact (TRANS (@lem2264093) (@lem2264096)). Qed.
Lemma lem2264099 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264100 : term41 = term42.
Proof. exact (@lem2264099 term32 term32). Qed.
Lemma lem2264101 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264102 : term44 = term32.
Proof. exact (EQ_MP (@lem2264101) (@lem940073)). Qed.
Lemma lem2264103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264104 : term42 = term38.
Proof. exact (MK_COMB (@lem2264103) (@lem2264102)). Qed.
Lemma lem2264105 : term41 = term38.
Proof. exact (TRANS (@lem2264100) (@lem2264104)). Qed.
Lemma lem2264106 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2264107 : term428 = term388.
Proof. exact (MK_COMB (@lem2264106) (@lem2264105)). Qed.
Lemma lem2264109 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264110 : term388 = term14.
Proof. exact (@lem2264109 term32). Qed.
Lemma lem2264111 : term428 = term14.
Proof. exact (TRANS (@lem2264107) (@lem2264110)). Qed.
Lemma lem2264112 : term14 = term428.
Proof. exact (SYM (@lem2264111)). Qed.
Lemma lem2264113 : term427 = term428.
Proof. exact (TRANS (@lem2264097) (@lem2264112)). Qed.
Lemma lem2264114 : term413 = term180.
Proof. exact (@lem2264064 (@lem2264113)). Qed.
Lemma lem2264115 : term412 = term180.
Proof. exact (TRANS (@lem2264030) (@lem2264114)). Qed.
Lemma lem2264117 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2264118 : term180 = term14.
Proof. exact (@lem2264117 term14). Qed.
Lemma lem2264119 : term412 = term14.
Proof. exact (TRANS (@lem2264115) (@lem2264118)). Qed.
Lemma lem2264120 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264121 : term429 = term426.
Proof. exact (MK_COMB (@lem2264120) (@lem2264119)). Qed.
Lemma lem2264122 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2264123 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2264121) (@lem2264122 n)). Qed.
Lemma lem2264124 (n : nat) : (term433 n) = (term387 n).
Proof. exact (TRANS (@lem2264021 n) (@lem2264123 n)). Qed.
Lemma lem2264125 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2264126 (n : nat) : (term433 n) = term14.
Proof. exact (TRANS (@lem2264124 n) (@lem2264125 n)). Qed.
Lemma lem2264127 (x : real) (n : nat) : (term492 x n) = term435.
Proof. exact (MK_COMB (@lem2264020 x) (@lem2264126 n)). Qed.
Lemma lem2264128 (x : real) (n : nat) : (term491 x n) = term435.
Proof. exact (TRANS (@lem2263912 x n) (@lem2264127 x n)). Qed.
Lemma lem2264129 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2264130 (x : real) (n : nat) : (term491 x n) = term14.
Proof. exact (TRANS (@lem2264128 x n) (@lem2264129)). Qed.
Lemma lem2264131 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2264132 (x : real) (n : nat) : (term493 x n) = term437.
Proof. exact (MK_COMB (@lem2264131) (@lem2264130 x n)). Qed.
Lemma lem2264133 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2264134 (x : real) (n : nat) : (term490 x n) = term438.
Proof. exact (MK_COMB (@lem2264132 x n) (@lem2264133)). Qed.
Lemma lem2264135 (x : real) (n : nat) (h1 : term296 x n) : term438.
Proof. exact (EQ_MP (@lem2264134 x n) (@lem2263911 x n h1)). Qed.
Lemma lem2264137 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2264138 : term438 = term439.
Proof. exact (@lem2264137 term14 term14). Qed.
Lemma lem2264140 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264141 : term14 = term180.
Proof. exact (@lem2264140 (NUMERAL 0)). Qed.
Lemma lem2264143 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264144 : term14 = term180.
Proof. exact (@lem2264143 (NUMERAL 0)). Qed.
Lemma lem2264145 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264146 : term378 = term379.
Proof. exact (MK_COMB (@lem2264145) (@lem2264144)). Qed.
Lemma lem2264147 : term439 = term440.
Proof. exact (MK_COMB (@lem2264146) (@lem2264141)). Qed.
Lemma lem2264148 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2264150 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264151 : term377 = term383.
Proof. exact (@lem2264150 (NUMERAL 0) term32). Qed.
Lemma lem2264152 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264153 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264154 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264153 h1) (fun h1 : term383 = True => @lem2264152)). Qed.
Lemma lem2264155 : term383 = True.
Proof. exact (EQ_MP (@lem2264154) (@lem2264152)). Qed.
Lemma lem2264156 : term377 = True.
Proof. exact (TRANS (@lem2264151) (@lem2264155)). Qed.
Lemma lem2264157 : True = term377.
Proof. exact (SYM (@lem2264156)). Qed.
Lemma lem2264158 : term377.
Proof. exact (EQ_MP (@lem2264157) (@lem0)). Qed.
Lemma lem2264159 : term442.
Proof. exact (@lem2264148 (@lem2264158)). Qed.
Lemma lem2264161 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264162 : term377 = term383.
Proof. exact (@lem2264161 (NUMERAL 0) term32). Qed.
Lemma lem2264163 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264164 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264165 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264164 h1) (fun h1 : term383 = True => @lem2264163)). Qed.
Lemma lem2264166 : term383 = True.
Proof. exact (EQ_MP (@lem2264165) (@lem2264163)). Qed.
Lemma lem2264167 : term377 = True.
Proof. exact (TRANS (@lem2264162) (@lem2264166)). Qed.
Lemma lem2264168 : True = term377.
Proof. exact (SYM (@lem2264167)). Qed.
Lemma lem2264169 : term377.
Proof. exact (EQ_MP (@lem2264168) (@lem0)). Qed.
Lemma lem2264170 : term440 = term443.
Proof. exact (@lem2264159 (@lem2264169)). Qed.
Lemma lem2264172 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264173 : term388 = term14.
Proof. exact (@lem2264172 term32). Qed.
Lemma lem2264175 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264176 : term388 = term14.
Proof. exact (@lem2264175 term32). Qed.
Lemma lem2264177 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264178 : term389 = term378.
Proof. exact (MK_COMB (@lem2264177) (@lem2264176)). Qed.
Lemma lem2264179 : term443 = term439.
Proof. exact (MK_COMB (@lem2264178) (@lem2264173)). Qed.
Lemma lem2264181 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264182 : term439 = term444.
Proof. exact (@lem2264181 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2264183 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2264184 : term439 = False.
Proof. exact (TRANS (@lem2264182) (@lem2264183)). Qed.
Lemma lem2264185 : term443 = False.
Proof. exact (TRANS (@lem2264179) (@lem2264184)). Qed.
Lemma lem2264186 : term440 = False.
Proof. exact (TRANS (@lem2264170) (@lem2264185)). Qed.
Lemma lem2264187 : term439 = False.
Proof. exact (TRANS (@lem2264147) (@lem2264186)). Qed.
Lemma lem2264188 : term438 = False.
Proof. exact (TRANS (@lem2264138) (@lem2264187)). Qed.
Lemma lem2264189 (x : real) (n : nat) (h1 : term296 x n) : False.
Proof. exact (EQ_MP (@lem2264188) (@lem2264135 x n h1)). Qed.
Lemma lem2264190 (x : real) (n : nat) (h1 : term297 x n) : False.
Proof. exact (or_elim (@lem2263343 x n h1) (fun h0 : term290 x n => @lem2263721 x n h0) (fun h0 : term296 x n => @lem2264189 x n h0)). Qed.
Lemma lem2264191 (x : real) (n : nat) (h1 : term300 x n) : False.
Proof. exact (or_elim (@lem2262446 x n h1) (fun h0 : term278 x n => @lem2263342 x n h0) (fun h0 : term297 x n => @lem2264190 x n h0)). Qed.
Lemma lem2264192 (x : real) (n : nat) (h1 : term302 x n) : False.
Proof. exact (or_elim (@lem2260879 x n h1) (fun h0 : term257 x n => @lem2262445 x n h0) (fun h0 : term300 x n => @lem2264191 x n h0)). Qed.
Lemma lem2264193 (x : real) (n : nat) (h1 : term373 x n) : term373 x n.
Proof. exact (h1). Qed.
Lemma lem2264194 (x : real) (n : nat) (h1 : term346 x n) : term346 x n.
Proof. exact (h1). Qed.
Lemma lem2264195 (x : real) (n : nat) (h1 : term326 x n) : term326 x n.
Proof. exact (h1). Qed.
Lemma lem2264196 (x : real) (n : nat) (h1 : term314 x n) : term314 x n.
Proof. exact (h1). Qed.
Lemma lem2264197 (x : real) (n : nat) (h1 : term314 x n) : term312 x n.
Proof. exact (proj2 (@lem2264196 x n h1)). Qed.
Lemma lem2264199 (x : real) (n : nat) (h1 : term314 x n) : (term21 x n) = term14.
Proof. exact (proj2 (@lem2264197 x n h1)). Qed.
Lemma lem2264200 (x : real) (n : nat) (h1 : term314 x n) : term63 x n.
Proof. exact (proj1 (@lem2264197 x n h1)). Qed.
Lemma lem2264203 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2264204 : term376 = term377.
Proof. exact (@lem2264203 term14 term38). Qed.
Lemma lem2264206 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264207 : term38 = term48.
Proof. exact (@lem2264206 term32). Qed.
Lemma lem2264209 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264210 : term14 = term180.
Proof. exact (@lem2264209 (NUMERAL 0)). Qed.
Lemma lem2264211 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264212 : term378 = term379.
Proof. exact (MK_COMB (@lem2264211) (@lem2264210)). Qed.
Lemma lem2264213 : term377 = term380.
Proof. exact (MK_COMB (@lem2264212) (@lem2264207)). Qed.
Lemma lem2264214 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2264216 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264217 : term377 = term383.
Proof. exact (@lem2264216 (NUMERAL 0) term32). Qed.
Lemma lem2264218 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264219 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264220 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264219 h1) (fun h1 : term383 = True => @lem2264218)). Qed.
Lemma lem2264221 : term383 = True.
Proof. exact (EQ_MP (@lem2264220) (@lem2264218)). Qed.
Lemma lem2264222 : term377 = True.
Proof. exact (TRANS (@lem2264217) (@lem2264221)). Qed.
Lemma lem2264223 : True = term377.
Proof. exact (SYM (@lem2264222)). Qed.
Lemma lem2264224 : term377.
Proof. exact (EQ_MP (@lem2264223) (@lem0)). Qed.
Lemma lem2264225 : term385.
Proof. exact (@lem2264214 (@lem2264224)). Qed.
Lemma lem2264227 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264228 : term377 = term383.
Proof. exact (@lem2264227 (NUMERAL 0) term32). Qed.
Lemma lem2264229 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264230 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264231 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264230 h1) (fun h1 : term383 = True => @lem2264229)). Qed.
Lemma lem2264232 : term383 = True.
Proof. exact (EQ_MP (@lem2264231) (@lem2264229)). Qed.
Lemma lem2264233 : term377 = True.
Proof. exact (TRANS (@lem2264228) (@lem2264232)). Qed.
Lemma lem2264234 : True = term377.
Proof. exact (SYM (@lem2264233)). Qed.
Lemma lem2264235 : term377.
Proof. exact (EQ_MP (@lem2264234) (@lem0)). Qed.
Lemma lem2264236 : term380 = term386.
Proof. exact (@lem2264225 (@lem2264235)). Qed.
Lemma lem2264238 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264239 : term41 = term42.
Proof. exact (@lem2264238 term32 term32). Qed.
Lemma lem2264240 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264241 : term44 = term32.
Proof. exact (EQ_MP (@lem2264240) (@lem940073)). Qed.
Lemma lem2264242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264243 : term42 = term38.
Proof. exact (MK_COMB (@lem2264242) (@lem2264241)). Qed.
Lemma lem2264244 : term41 = term38.
Proof. exact (TRANS (@lem2264239) (@lem2264243)). Qed.
Lemma lem2264246 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264247 : term388 = term14.
Proof. exact (@lem2264246 term32). Qed.
Lemma lem2264248 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264249 : term389 = term378.
Proof. exact (MK_COMB (@lem2264248) (@lem2264247)). Qed.
Lemma lem2264250 : term386 = term377.
Proof. exact (MK_COMB (@lem2264249) (@lem2264244)). Qed.
Lemma lem2264252 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264253 : term377 = term383.
Proof. exact (@lem2264252 (NUMERAL 0) term32). Qed.
Lemma lem2264254 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264255 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264256 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264255 h1) (fun h1 : term383 = True => @lem2264254)). Qed.
Lemma lem2264257 : term383 = True.
Proof. exact (EQ_MP (@lem2264256) (@lem2264254)). Qed.
Lemma lem2264258 : term377 = True.
Proof. exact (TRANS (@lem2264253) (@lem2264257)). Qed.
Lemma lem2264259 : term386 = True.
Proof. exact (TRANS (@lem2264250) (@lem2264258)). Qed.
Lemma lem2264260 : term380 = True.
Proof. exact (TRANS (@lem2264236) (@lem2264259)). Qed.
Lemma lem2264261 : term377 = True.
Proof. exact (TRANS (@lem2264213) (@lem2264260)). Qed.
Lemma lem2264262 : term376 = True.
Proof. exact (TRANS (@lem2264204) (@lem2264261)). Qed.
Lemma lem2264263 : True = term376.
Proof. exact (SYM (@lem2264262)). Qed.
Lemma lem2264264 : term376.
Proof. exact (EQ_MP (@lem2264263) (@lem0)). Qed.
Lemma lem2264265 (x : real) (n : nat) (h1 : term314 x n) : term390 x n.
Proof. exact (conj (@lem2264264) (@lem2264200 x n h1)). Qed.
Lemma lem2264267 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2264268 (x : real) (n : nat) : term392 x n.
Proof. exact (@lem2264267 term38 (term21 x n)). Qed.
Lemma lem2264269 (x : real) (n : nat) (h1 : term314 x n) : term393 x n.
Proof. exact (@lem2264268 x n (@lem2264265 x n h1)). Qed.
Lemma lem2264270 (x : real) (n : nat) : (term394 x n) = (term21 x n).
Proof. exact (@lem1982733 (term21 x n)). Qed.
Lemma lem2264271 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2264272 (x : real) (n : nat) : (term395 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem2264271) (@lem2264270 x n)). Qed.
Lemma lem2264273 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2264274 (x : real) (n : nat) : (term393 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem2264272 x n) (@lem2264273)). Qed.
Lemma lem2264275 (x : real) (n : nat) (h1 : term314 x n) : term63 x n.
Proof. exact (EQ_MP (@lem2264274 x n) (@lem2264269 x n h1)). Qed.
Lemma lem2264277 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2264278 (x : real) (n : nat) : term397 x n.
Proof. exact (@lem2264277 (term21 x n)). Qed.
Lemma lem2264279 (x : real) (n : nat) (h1 : term314 x n) : term398 x n.
Proof. exact (@lem2264278 x n (@lem2264199 x n h1)). Qed.
Lemma lem2264280 (x : real) (n : nat) (h1 : term314 x n) : term399 x n.
Proof. exact (@lem2264279 x n h1 term26). Qed.
Lemma lem2264281 (x : real) (n : nat) : (term399 x n) = ((term24 x n) = term14).
Proof. exact (eq_refl (term399 x n)). Qed.
Lemma lem2264282 (x : real) (n : nat) (h1 : term314 x n) : (term24 x n) = term14.
Proof. exact (EQ_MP (@lem2264281 x n) (@lem2264280 x n h1)). Qed.
Lemma lem2264283 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (@lem1982781 x term26 (term27 n)). Qed.
Lemma lem2264284 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2264286 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2264287 : term26 = term31.
Proof. exact (@lem2264286 term32). Qed.
Lemma lem2264289 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2264290 : term26 = term31.
Proof. exact (@lem2264289 term32). Qed.
Lemma lem2264291 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264292 : term33 = term34.
Proof. exact (MK_COMB (@lem2264291) (@lem2264290)). Qed.
Lemma lem2264293 : term35 = term36.
Proof. exact (MK_COMB (@lem2264292) (@lem2264287)). Qed.
Lemma lem2264294 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2264296 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264297 : term41 = term42.
Proof. exact (@lem2264296 term32 term32). Qed.
Lemma lem2264298 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264299 : term44 = term32.
Proof. exact (EQ_MP (@lem2264298) (@lem940073)). Qed.
Lemma lem2264300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264301 : term42 = term38.
Proof. exact (MK_COMB (@lem2264300) (@lem2264299)). Qed.
Lemma lem2264302 : term41 = term38.
Proof. exact (TRANS (@lem2264297) (@lem2264301)). Qed.
Lemma lem2264304 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2264305 : term35 = term42.
Proof. exact (@lem2264304 term32 term32). Qed.
Lemma lem2264306 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264307 : term44 = term32.
Proof. exact (EQ_MP (@lem2264306) (@lem940073)). Qed.
Lemma lem2264308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264309 : term42 = term38.
Proof. exact (MK_COMB (@lem2264308) (@lem2264307)). Qed.
Lemma lem2264310 : term35 = term38.
Proof. exact (TRANS (@lem2264305) (@lem2264309)). Qed.
Lemma lem2264311 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2264312 : term46 = term47.
Proof. exact (MK_COMB (@lem2264311) (@lem2264310)). Qed.
Lemma lem2264313 : term37 = term48.
Proof. exact (MK_COMB (@lem2264312) (@lem2264302)). Qed.
Lemma lem2264314 : term36 = term48.
Proof. exact (TRANS (@lem2264294) (@lem2264313)). Qed.
Lemma lem2264315 : term35 = term48.
Proof. exact (TRANS (@lem2264293) (@lem2264314)). Qed.
Lemma lem2264317 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2264318 : term48 = term38.
Proof. exact (@lem2264317 term38). Qed.
Lemma lem2264319 : term35 = term38.
Proof. exact (TRANS (@lem2264315) (@lem2264318)). Qed.
Lemma lem2264320 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264321 : term50 = term51.
Proof. exact (MK_COMB (@lem2264320) (@lem2264319)). Qed.
Lemma lem2264322 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2264323 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2264321) (@lem2264322 n)). Qed.
Lemma lem2264324 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2264284 n) (@lem2264323 n)). Qed.
Lemma lem2264325 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2264326 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2264324 n) (@lem2264325 n)). Qed.
Lemma lem2264329 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2264330 (x : real) (n : nat) : (term25 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem2264329 x) (@lem2264326 n)). Qed.
Lemma lem2264331 (x : real) (n : nat) : (term24 x n) = (term54 x n).
Proof. exact (TRANS (@lem2264283 x n) (@lem2264330 x n)). Qed.
Lemma lem2264332 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2264333 (x : real) (n : nat) : (term400 x n) = (term401 x n).
Proof. exact (MK_COMB (@lem2264332) (@lem2264331 x n)). Qed.
Lemma lem2264334 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2264335 (x : real) (n : nat) : ((term24 x n) = term14) = ((term54 x n) = term14).
Proof. exact (MK_COMB (@lem2264333 x n) (@lem2264334)). Qed.
Lemma lem2264336 (x : real) (n : nat) (h1 : term314 x n) : (term54 x n) = term14.
Proof. exact (EQ_MP (@lem2264335 x n) (@lem2264282 x n h1)). Qed.
Lemma lem2264337 (x : real) (n : nat) (h1 : term314 x n) : term402 x n.
Proof. exact (conj (@lem2264336 x n h1) (@lem2264275 x n h1)). Qed.
Lemma lem2264339 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2264340 (x : real) (n : nat) : term404 x n.
Proof. exact (@lem2264339 (term54 x n) (term21 x n)). Qed.
Lemma lem2264341 (x : real) (n : nat) (h1 : term314 x n) : term405 x n.
Proof. exact (@lem2264340 x n (@lem2264337 x n h1)). Qed.
Lemma lem2264342 (x : real) (n : nat) : (term406 x n) = (term407 x n).
Proof. exact (@lem1982753 (term208 x) x (real_of_num n) (term27 n)). Qed.
Lemma lem2264343 (x : real) : (term408 x) = (term409 x).
Proof. exact (@lem1982713 term26 x). Qed.
Lemma lem2264345 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264346 : term38 = term48.
Proof. exact (@lem2264345 term32). Qed.
Lemma lem2264348 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2264349 : term26 = term31.
Proof. exact (@lem2264348 term32). Qed.
Lemma lem2264350 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264351 : term410 = term411.
Proof. exact (MK_COMB (@lem2264350) (@lem2264349)). Qed.
Lemma lem2264352 : term412 = term413.
Proof. exact (MK_COMB (@lem2264351) (@lem2264346)). Qed.
Lemma lem2264353 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2264355 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264356 : term377 = term383.
Proof. exact (@lem2264355 (NUMERAL 0) term32). Qed.
Lemma lem2264357 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264358 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264359 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264358 h1) (fun h1 : term383 = True => @lem2264357)). Qed.
Lemma lem2264360 : term383 = True.
Proof. exact (EQ_MP (@lem2264359) (@lem2264357)). Qed.
Lemma lem2264361 : term377 = True.
Proof. exact (TRANS (@lem2264356) (@lem2264360)). Qed.
Lemma lem2264362 : True = term377.
Proof. exact (SYM (@lem2264361)). Qed.
Lemma lem2264363 : term377.
Proof. exact (EQ_MP (@lem2264362) (@lem0)). Qed.
Lemma lem2264364 : term415.
Proof. exact (@lem2264353 (@lem2264363)). Qed.
Lemma lem2264366 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264367 : term377 = term383.
Proof. exact (@lem2264366 (NUMERAL 0) term32). Qed.
Lemma lem2264368 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264369 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264370 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264369 h1) (fun h1 : term383 = True => @lem2264368)). Qed.
Lemma lem2264371 : term383 = True.
Proof. exact (EQ_MP (@lem2264370) (@lem2264368)). Qed.
Lemma lem2264372 : term377 = True.
Proof. exact (TRANS (@lem2264367) (@lem2264371)). Qed.
Lemma lem2264373 : True = term377.
Proof. exact (SYM (@lem2264372)). Qed.
Lemma lem2264374 : term377.
Proof. exact (EQ_MP (@lem2264373) (@lem0)). Qed.
Lemma lem2264375 : term416.
Proof. exact (@lem2264364 (@lem2264374)). Qed.
Lemma lem2264377 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264378 : term377 = term383.
Proof. exact (@lem2264377 (NUMERAL 0) term32). Qed.
Lemma lem2264379 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264380 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264381 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264380 h1) (fun h1 : term383 = True => @lem2264379)). Qed.
Lemma lem2264382 : term383 = True.
Proof. exact (EQ_MP (@lem2264381) (@lem2264379)). Qed.
Lemma lem2264383 : term377 = True.
Proof. exact (TRANS (@lem2264378) (@lem2264382)). Qed.
Lemma lem2264384 : True = term377.
Proof. exact (SYM (@lem2264383)). Qed.
Lemma lem2264385 : term377.
Proof. exact (EQ_MP (@lem2264384) (@lem0)). Qed.
Lemma lem2264386 : term417.
Proof. exact (@lem2264375 (@lem2264385)). Qed.
Lemma lem2264388 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264389 : term41 = term42.
Proof. exact (@lem2264388 term32 term32). Qed.
Lemma lem2264390 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264391 : term44 = term32.
Proof. exact (EQ_MP (@lem2264390) (@lem940073)). Qed.
Lemma lem2264392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264393 : term42 = term38.
Proof. exact (MK_COMB (@lem2264392) (@lem2264391)). Qed.
Lemma lem2264394 : term41 = term38.
Proof. exact (TRANS (@lem2264389) (@lem2264393)). Qed.
Lemma lem2264396 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2264397 : term420 = term421.
Proof. exact (@lem2264396 term32 term32). Qed.
Lemma lem2264398 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264399 : term44 = term32.
Proof. exact (EQ_MP (@lem2264398) (@lem940073)). Qed.
Lemma lem2264400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264401 : term42 = term38.
Proof. exact (MK_COMB (@lem2264400) (@lem2264399)). Qed.
Lemma lem2264402 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2264403 : term421 = term26.
Proof. exact (MK_COMB (@lem2264402) (@lem2264401)). Qed.
Lemma lem2264404 : term420 = term26.
Proof. exact (TRANS (@lem2264397) (@lem2264403)). Qed.
Lemma lem2264405 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264406 : term422 = term410.
Proof. exact (MK_COMB (@lem2264405) (@lem2264404)). Qed.
Lemma lem2264407 : term423 = term412.
Proof. exact (MK_COMB (@lem2264406) (@lem2264394)). Qed.
Lemma lem2264409 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2264410 : term412 = term14.
Proof. exact (@lem2264409 term32). Qed.
Lemma lem2264411 : term423 = term14.
Proof. exact (TRANS (@lem2264407) (@lem2264410)). Qed.
Lemma lem2264412 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264413 : term425 = term426.
Proof. exact (MK_COMB (@lem2264412) (@lem2264411)). Qed.
Lemma lem2264414 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2264415 : term427 = term388.
Proof. exact (MK_COMB (@lem2264413) (@lem2264414)). Qed.
Lemma lem2264417 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264418 : term388 = term14.
Proof. exact (@lem2264417 term32). Qed.
Lemma lem2264419 : term427 = term14.
Proof. exact (TRANS (@lem2264415) (@lem2264418)). Qed.
Lemma lem2264421 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264422 : term41 = term42.
Proof. exact (@lem2264421 term32 term32). Qed.
Lemma lem2264423 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264424 : term44 = term32.
Proof. exact (EQ_MP (@lem2264423) (@lem940073)). Qed.
Lemma lem2264425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264426 : term42 = term38.
Proof. exact (MK_COMB (@lem2264425) (@lem2264424)). Qed.
Lemma lem2264427 : term41 = term38.
Proof. exact (TRANS (@lem2264422) (@lem2264426)). Qed.
Lemma lem2264428 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2264429 : term428 = term388.
Proof. exact (MK_COMB (@lem2264428) (@lem2264427)). Qed.
Lemma lem2264431 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264432 : term388 = term14.
Proof. exact (@lem2264431 term32). Qed.
Lemma lem2264433 : term428 = term14.
Proof. exact (TRANS (@lem2264429) (@lem2264432)). Qed.
Lemma lem2264434 : term14 = term428.
Proof. exact (SYM (@lem2264433)). Qed.
Lemma lem2264435 : term427 = term428.
Proof. exact (TRANS (@lem2264419) (@lem2264434)). Qed.
Lemma lem2264436 : term413 = term180.
Proof. exact (@lem2264386 (@lem2264435)). Qed.
Lemma lem2264437 : term412 = term180.
Proof. exact (TRANS (@lem2264352) (@lem2264436)). Qed.
Lemma lem2264439 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2264440 : term180 = term14.
Proof. exact (@lem2264439 term14). Qed.
Lemma lem2264441 : term412 = term14.
Proof. exact (TRANS (@lem2264437) (@lem2264440)). Qed.
Lemma lem2264442 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264443 : term429 = term426.
Proof. exact (MK_COMB (@lem2264442) (@lem2264441)). Qed.
Lemma lem2264444 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2264445 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2264443) (@lem2264444 x)). Qed.
Lemma lem2264446 (x : real) : (term408 x) = (term430 x).
Proof. exact (TRANS (@lem2264343 x) (@lem2264445 x)). Qed.
Lemma lem2264447 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2264448 (x : real) : (term408 x) = term14.
Proof. exact (TRANS (@lem2264446 x) (@lem2264447 x)). Qed.
Lemma lem2264449 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264450 (x : real) : (term431 x) = term432.
Proof. exact (MK_COMB (@lem2264449) (@lem2264448 x)). Qed.
Lemma lem2264451 (n : nat) : (term433 n) = (term434 n).
Proof. exact (@lem1982715 term26 (real_of_num n)). Qed.
Lemma lem2264453 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264454 : term38 = term48.
Proof. exact (@lem2264453 term32). Qed.
Lemma lem2264456 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2264457 : term26 = term31.
Proof. exact (@lem2264456 term32). Qed.
Lemma lem2264458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264459 : term410 = term411.
Proof. exact (MK_COMB (@lem2264458) (@lem2264457)). Qed.
Lemma lem2264460 : term412 = term413.
Proof. exact (MK_COMB (@lem2264459) (@lem2264454)). Qed.
Lemma lem2264461 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2264463 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264464 : term377 = term383.
Proof. exact (@lem2264463 (NUMERAL 0) term32). Qed.
Lemma lem2264465 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264466 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264467 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264466 h1) (fun h1 : term383 = True => @lem2264465)). Qed.
Lemma lem2264468 : term383 = True.
Proof. exact (EQ_MP (@lem2264467) (@lem2264465)). Qed.
Lemma lem2264469 : term377 = True.
Proof. exact (TRANS (@lem2264464) (@lem2264468)). Qed.
Lemma lem2264470 : True = term377.
Proof. exact (SYM (@lem2264469)). Qed.
Lemma lem2264471 : term377.
Proof. exact (EQ_MP (@lem2264470) (@lem0)). Qed.
Lemma lem2264472 : term415.
Proof. exact (@lem2264461 (@lem2264471)). Qed.
Lemma lem2264474 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264475 : term377 = term383.
Proof. exact (@lem2264474 (NUMERAL 0) term32). Qed.
Lemma lem2264476 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264477 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264478 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264477 h1) (fun h1 : term383 = True => @lem2264476)). Qed.
Lemma lem2264479 : term383 = True.
Proof. exact (EQ_MP (@lem2264478) (@lem2264476)). Qed.
Lemma lem2264480 : term377 = True.
Proof. exact (TRANS (@lem2264475) (@lem2264479)). Qed.
Lemma lem2264481 : True = term377.
Proof. exact (SYM (@lem2264480)). Qed.
Lemma lem2264482 : term377.
Proof. exact (EQ_MP (@lem2264481) (@lem0)). Qed.
Lemma lem2264483 : term416.
Proof. exact (@lem2264472 (@lem2264482)). Qed.
Lemma lem2264485 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264486 : term377 = term383.
Proof. exact (@lem2264485 (NUMERAL 0) term32). Qed.
Lemma lem2264487 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264488 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264489 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264488 h1) (fun h1 : term383 = True => @lem2264487)). Qed.
Lemma lem2264490 : term383 = True.
Proof. exact (EQ_MP (@lem2264489) (@lem2264487)). Qed.
Lemma lem2264491 : term377 = True.
Proof. exact (TRANS (@lem2264486) (@lem2264490)). Qed.
Lemma lem2264492 : True = term377.
Proof. exact (SYM (@lem2264491)). Qed.
Lemma lem2264493 : term377.
Proof. exact (EQ_MP (@lem2264492) (@lem0)). Qed.
Lemma lem2264494 : term417.
Proof. exact (@lem2264483 (@lem2264493)). Qed.
Lemma lem2264496 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264497 : term41 = term42.
Proof. exact (@lem2264496 term32 term32). Qed.
Lemma lem2264498 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264499 : term44 = term32.
Proof. exact (EQ_MP (@lem2264498) (@lem940073)). Qed.
Lemma lem2264500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264501 : term42 = term38.
Proof. exact (MK_COMB (@lem2264500) (@lem2264499)). Qed.
Lemma lem2264502 : term41 = term38.
Proof. exact (TRANS (@lem2264497) (@lem2264501)). Qed.
Lemma lem2264504 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2264505 : term420 = term421.
Proof. exact (@lem2264504 term32 term32). Qed.
Lemma lem2264506 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264507 : term44 = term32.
Proof. exact (EQ_MP (@lem2264506) (@lem940073)). Qed.
Lemma lem2264508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264509 : term42 = term38.
Proof. exact (MK_COMB (@lem2264508) (@lem2264507)). Qed.
Lemma lem2264510 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2264511 : term421 = term26.
Proof. exact (MK_COMB (@lem2264510) (@lem2264509)). Qed.
Lemma lem2264512 : term420 = term26.
Proof. exact (TRANS (@lem2264505) (@lem2264511)). Qed.
Lemma lem2264513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264514 : term422 = term410.
Proof. exact (MK_COMB (@lem2264513) (@lem2264512)). Qed.
Lemma lem2264515 : term423 = term412.
Proof. exact (MK_COMB (@lem2264514) (@lem2264502)). Qed.
Lemma lem2264517 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2264518 : term412 = term14.
Proof. exact (@lem2264517 term32). Qed.
Lemma lem2264519 : term423 = term14.
Proof. exact (TRANS (@lem2264515) (@lem2264518)). Qed.
Lemma lem2264520 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264521 : term425 = term426.
Proof. exact (MK_COMB (@lem2264520) (@lem2264519)). Qed.
Lemma lem2264522 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2264523 : term427 = term388.
Proof. exact (MK_COMB (@lem2264521) (@lem2264522)). Qed.
Lemma lem2264525 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264526 : term388 = term14.
Proof. exact (@lem2264525 term32). Qed.
Lemma lem2264527 : term427 = term14.
Proof. exact (TRANS (@lem2264523) (@lem2264526)). Qed.
Lemma lem2264529 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264530 : term41 = term42.
Proof. exact (@lem2264529 term32 term32). Qed.
Lemma lem2264531 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264532 : term44 = term32.
Proof. exact (EQ_MP (@lem2264531) (@lem940073)). Qed.
Lemma lem2264533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264534 : term42 = term38.
Proof. exact (MK_COMB (@lem2264533) (@lem2264532)). Qed.
Lemma lem2264535 : term41 = term38.
Proof. exact (TRANS (@lem2264530) (@lem2264534)). Qed.
Lemma lem2264536 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2264537 : term428 = term388.
Proof. exact (MK_COMB (@lem2264536) (@lem2264535)). Qed.
Lemma lem2264539 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264540 : term388 = term14.
Proof. exact (@lem2264539 term32). Qed.
Lemma lem2264541 : term428 = term14.
Proof. exact (TRANS (@lem2264537) (@lem2264540)). Qed.
Lemma lem2264542 : term14 = term428.
Proof. exact (SYM (@lem2264541)). Qed.
Lemma lem2264543 : term427 = term428.
Proof. exact (TRANS (@lem2264527) (@lem2264542)). Qed.
Lemma lem2264544 : term413 = term180.
Proof. exact (@lem2264494 (@lem2264543)). Qed.
Lemma lem2264545 : term412 = term180.
Proof. exact (TRANS (@lem2264460) (@lem2264544)). Qed.
Lemma lem2264547 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2264548 : term180 = term14.
Proof. exact (@lem2264547 term14). Qed.
Lemma lem2264549 : term412 = term14.
Proof. exact (TRANS (@lem2264545) (@lem2264548)). Qed.
Lemma lem2264550 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264551 : term429 = term426.
Proof. exact (MK_COMB (@lem2264550) (@lem2264549)). Qed.
Lemma lem2264552 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2264553 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2264551) (@lem2264552 n)). Qed.
Lemma lem2264554 (n : nat) : (term433 n) = (term387 n).
Proof. exact (TRANS (@lem2264451 n) (@lem2264553 n)). Qed.
Lemma lem2264555 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2264556 (n : nat) : (term433 n) = term14.
Proof. exact (TRANS (@lem2264554 n) (@lem2264555 n)). Qed.
Lemma lem2264557 (x : real) (n : nat) : (term407 x n) = term435.
Proof. exact (MK_COMB (@lem2264450 x) (@lem2264556 n)). Qed.
Lemma lem2264558 (x : real) (n : nat) : (term406 x n) = term435.
Proof. exact (TRANS (@lem2264342 x n) (@lem2264557 x n)). Qed.
Lemma lem2264559 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2264560 (x : real) (n : nat) : (term406 x n) = term14.
Proof. exact (TRANS (@lem2264558 x n) (@lem2264559)). Qed.
Lemma lem2264561 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2264562 (x : real) (n : nat) : (term436 x n) = term437.
Proof. exact (MK_COMB (@lem2264561) (@lem2264560 x n)). Qed.
Lemma lem2264563 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2264564 (x : real) (n : nat) : (term405 x n) = term438.
Proof. exact (MK_COMB (@lem2264562 x n) (@lem2264563)). Qed.
Lemma lem2264565 (x : real) (n : nat) (h1 : term314 x n) : term438.
Proof. exact (EQ_MP (@lem2264564 x n) (@lem2264341 x n h1)). Qed.
Lemma lem2264567 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2264568 : term438 = term439.
Proof. exact (@lem2264567 term14 term14). Qed.
Lemma lem2264570 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264571 : term14 = term180.
Proof. exact (@lem2264570 (NUMERAL 0)). Qed.
Lemma lem2264573 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264574 : term14 = term180.
Proof. exact (@lem2264573 (NUMERAL 0)). Qed.
Lemma lem2264575 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264576 : term378 = term379.
Proof. exact (MK_COMB (@lem2264575) (@lem2264574)). Qed.
Lemma lem2264577 : term439 = term440.
Proof. exact (MK_COMB (@lem2264576) (@lem2264571)). Qed.
Lemma lem2264578 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2264580 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264581 : term377 = term383.
Proof. exact (@lem2264580 (NUMERAL 0) term32). Qed.
Lemma lem2264582 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264583 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264584 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264583 h1) (fun h1 : term383 = True => @lem2264582)). Qed.
Lemma lem2264585 : term383 = True.
Proof. exact (EQ_MP (@lem2264584) (@lem2264582)). Qed.
Lemma lem2264586 : term377 = True.
Proof. exact (TRANS (@lem2264581) (@lem2264585)). Qed.
Lemma lem2264587 : True = term377.
Proof. exact (SYM (@lem2264586)). Qed.
Lemma lem2264588 : term377.
Proof. exact (EQ_MP (@lem2264587) (@lem0)). Qed.
Lemma lem2264589 : term442.
Proof. exact (@lem2264578 (@lem2264588)). Qed.
Lemma lem2264591 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264592 : term377 = term383.
Proof. exact (@lem2264591 (NUMERAL 0) term32). Qed.
Lemma lem2264593 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264594 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264595 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264594 h1) (fun h1 : term383 = True => @lem2264593)). Qed.
Lemma lem2264596 : term383 = True.
Proof. exact (EQ_MP (@lem2264595) (@lem2264593)). Qed.
Lemma lem2264597 : term377 = True.
Proof. exact (TRANS (@lem2264592) (@lem2264596)). Qed.
Lemma lem2264598 : True = term377.
Proof. exact (SYM (@lem2264597)). Qed.
Lemma lem2264599 : term377.
Proof. exact (EQ_MP (@lem2264598) (@lem0)). Qed.
Lemma lem2264600 : term440 = term443.
Proof. exact (@lem2264589 (@lem2264599)). Qed.
Lemma lem2264602 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264603 : term388 = term14.
Proof. exact (@lem2264602 term32). Qed.
Lemma lem2264605 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264606 : term388 = term14.
Proof. exact (@lem2264605 term32). Qed.
Lemma lem2264607 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264608 : term389 = term378.
Proof. exact (MK_COMB (@lem2264607) (@lem2264606)). Qed.
Lemma lem2264609 : term443 = term439.
Proof. exact (MK_COMB (@lem2264608) (@lem2264603)). Qed.
Lemma lem2264611 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264612 : term439 = term444.
Proof. exact (@lem2264611 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2264613 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2264614 : term439 = False.
Proof. exact (TRANS (@lem2264612) (@lem2264613)). Qed.
Lemma lem2264615 : term443 = False.
Proof. exact (TRANS (@lem2264609) (@lem2264614)). Qed.
Lemma lem2264616 : term440 = False.
Proof. exact (TRANS (@lem2264600) (@lem2264615)). Qed.
Lemma lem2264617 : term439 = False.
Proof. exact (TRANS (@lem2264577) (@lem2264616)). Qed.
Lemma lem2264618 : term438 = False.
Proof. exact (TRANS (@lem2264568) (@lem2264617)). Qed.
Lemma lem2264619 (x : real) (n : nat) (h1 : term314 x n) : False.
Proof. exact (EQ_MP (@lem2264618) (@lem2264565 x n h1)). Qed.
Lemma lem2264620 (x : real) (n : nat) (h1 : term325 x n) : term325 x n.
Proof. exact (h1). Qed.
Lemma lem2264621 (x : real) (n : nat) (h1 : term325 x n) : term324 x n.
Proof. exact (proj2 (@lem2264620 x n h1)). Qed.
Lemma lem2264623 (x : real) (n : nat) (h1 : term325 x n) : (term21 x n) = term14.
Proof. exact (proj2 (@lem2264621 x n h1)). Qed.
Lemma lem2264624 (x : real) (n : nat) (h1 : term325 x n) : term81 x n.
Proof. exact (proj1 (@lem2264621 x n h1)). Qed.
Lemma lem2264625 (n : nat) : term494 n.
Proof. exact (@lem1396812 n). Qed.
Lemma lem2264627 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2264628 : term376 = term377.
Proof. exact (@lem2264627 term14 term38). Qed.
Lemma lem2264630 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264631 : term38 = term48.
Proof. exact (@lem2264630 term32). Qed.
Lemma lem2264633 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264634 : term14 = term180.
Proof. exact (@lem2264633 (NUMERAL 0)). Qed.
Lemma lem2264635 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264636 : term378 = term379.
Proof. exact (MK_COMB (@lem2264635) (@lem2264634)). Qed.
Lemma lem2264637 : term377 = term380.
Proof. exact (MK_COMB (@lem2264636) (@lem2264631)). Qed.
Lemma lem2264638 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2264640 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264641 : term377 = term383.
Proof. exact (@lem2264640 (NUMERAL 0) term32). Qed.
Lemma lem2264642 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264643 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264644 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264643 h1) (fun h1 : term383 = True => @lem2264642)). Qed.
Lemma lem2264645 : term383 = True.
Proof. exact (EQ_MP (@lem2264644) (@lem2264642)). Qed.
Lemma lem2264646 : term377 = True.
Proof. exact (TRANS (@lem2264641) (@lem2264645)). Qed.
Lemma lem2264647 : True = term377.
Proof. exact (SYM (@lem2264646)). Qed.
Lemma lem2264648 : term377.
Proof. exact (EQ_MP (@lem2264647) (@lem0)). Qed.
Lemma lem2264649 : term385.
Proof. exact (@lem2264638 (@lem2264648)). Qed.
Lemma lem2264651 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264652 : term377 = term383.
Proof. exact (@lem2264651 (NUMERAL 0) term32). Qed.
Lemma lem2264653 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264654 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264655 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264654 h1) (fun h1 : term383 = True => @lem2264653)). Qed.
Lemma lem2264656 : term383 = True.
Proof. exact (EQ_MP (@lem2264655) (@lem2264653)). Qed.
Lemma lem2264657 : term377 = True.
Proof. exact (TRANS (@lem2264652) (@lem2264656)). Qed.
Lemma lem2264658 : True = term377.
Proof. exact (SYM (@lem2264657)). Qed.
Lemma lem2264659 : term377.
Proof. exact (EQ_MP (@lem2264658) (@lem0)). Qed.
Lemma lem2264660 : term380 = term386.
Proof. exact (@lem2264649 (@lem2264659)). Qed.
Lemma lem2264662 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264663 : term41 = term42.
Proof. exact (@lem2264662 term32 term32). Qed.
Lemma lem2264664 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264665 : term44 = term32.
Proof. exact (EQ_MP (@lem2264664) (@lem940073)). Qed.
Lemma lem2264666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264667 : term42 = term38.
Proof. exact (MK_COMB (@lem2264666) (@lem2264665)). Qed.
Lemma lem2264668 : term41 = term38.
Proof. exact (TRANS (@lem2264663) (@lem2264667)). Qed.
Lemma lem2264670 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264671 : term388 = term14.
Proof. exact (@lem2264670 term32). Qed.
Lemma lem2264672 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264673 : term389 = term378.
Proof. exact (MK_COMB (@lem2264672) (@lem2264671)). Qed.
Lemma lem2264674 : term386 = term377.
Proof. exact (MK_COMB (@lem2264673) (@lem2264668)). Qed.
Lemma lem2264676 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264677 : term377 = term383.
Proof. exact (@lem2264676 (NUMERAL 0) term32). Qed.
Lemma lem2264678 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264679 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264680 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264679 h1) (fun h1 : term383 = True => @lem2264678)). Qed.
Lemma lem2264681 : term383 = True.
Proof. exact (EQ_MP (@lem2264680) (@lem2264678)). Qed.
Lemma lem2264682 : term377 = True.
Proof. exact (TRANS (@lem2264677) (@lem2264681)). Qed.
Lemma lem2264683 : term386 = True.
Proof. exact (TRANS (@lem2264674) (@lem2264682)). Qed.
Lemma lem2264684 : term380 = True.
Proof. exact (TRANS (@lem2264660) (@lem2264683)). Qed.
Lemma lem2264685 : term377 = True.
Proof. exact (TRANS (@lem2264637) (@lem2264684)). Qed.
Lemma lem2264686 : term376 = True.
Proof. exact (TRANS (@lem2264628) (@lem2264685)). Qed.
Lemma lem2264687 : True = term376.
Proof. exact (SYM (@lem2264686)). Qed.
Lemma lem2264688 : term376.
Proof. exact (EQ_MP (@lem2264687) (@lem0)). Qed.
Lemma lem2264689 (n : nat) : term495 n.
Proof. exact (conj (@lem2264688) (@lem2264625 n)). Qed.
Lemma lem2264691 (x : real) (y : real) : term496 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2264692 (n : nat) : term497 n.
Proof. exact (@lem2264691 term38 (real_of_num n)). Qed.
Lemma lem2264693 (n : nat) : term498 n.
Proof. exact (@lem2264692 n (@lem2264689 n)). Qed.
Lemma lem2264694 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982733 (real_of_num n)). Qed.
Lemma lem2264695 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2264696 (n : nat) : (term499 n) = (term500 n).
Proof. exact (MK_COMB (@lem2264695) (@lem2264694 n)). Qed.
Lemma lem2264697 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2264698 (n : nat) : (term498 n) = (term494 n).
Proof. exact (MK_COMB (@lem2264696 n) (@lem2264697)). Qed.
Lemma lem2264699 (n : nat) : term494 n.
Proof. exact (EQ_MP (@lem2264698 n) (@lem2264693 n)). Qed.
Lemma lem2264701 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2264702 (x : real) (n : nat) : term397 x n.
Proof. exact (@lem2264701 (term21 x n)). Qed.
Lemma lem2264703 (x : real) (n : nat) (h1 : term325 x n) : term398 x n.
Proof. exact (@lem2264702 x n (@lem2264623 x n h1)). Qed.
Lemma lem2264704 (x : real) (n : nat) (h1 : term325 x n) : term467 x n.
Proof. exact (@lem2264703 x n h1 term38). Qed.
Lemma lem2264705 (x : real) (n : nat) : (term467 x n) = ((term394 x n) = term14).
Proof. exact (eq_refl (term467 x n)). Qed.
Lemma lem2264706 (x : real) (n : nat) (h1 : term325 x n) : (term394 x n) = term14.
Proof. exact (EQ_MP (@lem2264705 x n) (@lem2264704 x n h1)). Qed.
Lemma lem2264707 (x : real) (n : nat) : (term394 x n) = (term21 x n).
Proof. exact (@lem1982733 (term21 x n)). Qed.
Lemma lem2264708 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2264709 (x : real) (n : nat) : (term468 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2264708) (@lem2264707 x n)). Qed.
Lemma lem2264710 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2264711 (x : real) (n : nat) : ((term394 x n) = term14) = ((term21 x n) = term14).
Proof. exact (MK_COMB (@lem2264709 x n) (@lem2264710)). Qed.
Lemma lem2264712 (x : real) (n : nat) (h1 : term325 x n) : (term21 x n) = term14.
Proof. exact (EQ_MP (@lem2264711 x n) (@lem2264706 x n h1)). Qed.
Lemma lem2264713 (x : real) (n : nat) (h1 : term325 x n) : term501 x n.
Proof. exact (conj (@lem2264712 x n h1) (@lem2264699 n)). Qed.
Lemma lem2264715 (x : real) (y : real) : term502 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2264716 (x : real) (n : nat) : term503 x n.
Proof. exact (@lem2264715 (term21 x n) (real_of_num n)). Qed.
Lemma lem2264717 (x : real) (n : nat) (h1 : term325 x n) : term504 x n.
Proof. exact (@lem2264716 x n (@lem2264713 x n h1)). Qed.
Lemma lem2264718 (x : real) (n : nat) : (term505 x n) = (term506 x n).
Proof. exact (@lem1982755 x (term27 n) (real_of_num n)). Qed.
Lemma lem2264719 (n : nat) : (term460 n) = (term434 n).
Proof. exact (@lem1982713 term26 (real_of_num n)). Qed.
Lemma lem2264721 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264722 : term38 = term48.
Proof. exact (@lem2264721 term32). Qed.
Lemma lem2264724 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2264725 : term26 = term31.
Proof. exact (@lem2264724 term32). Qed.
Lemma lem2264726 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264727 : term410 = term411.
Proof. exact (MK_COMB (@lem2264726) (@lem2264725)). Qed.
Lemma lem2264728 : term412 = term413.
Proof. exact (MK_COMB (@lem2264727) (@lem2264722)). Qed.
Lemma lem2264729 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2264731 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264732 : term377 = term383.
Proof. exact (@lem2264731 (NUMERAL 0) term32). Qed.
Lemma lem2264733 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264734 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264735 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264734 h1) (fun h1 : term383 = True => @lem2264733)). Qed.
Lemma lem2264736 : term383 = True.
Proof. exact (EQ_MP (@lem2264735) (@lem2264733)). Qed.
Lemma lem2264737 : term377 = True.
Proof. exact (TRANS (@lem2264732) (@lem2264736)). Qed.
Lemma lem2264738 : True = term377.
Proof. exact (SYM (@lem2264737)). Qed.
Lemma lem2264739 : term377.
Proof. exact (EQ_MP (@lem2264738) (@lem0)). Qed.
Lemma lem2264740 : term415.
Proof. exact (@lem2264729 (@lem2264739)). Qed.
Lemma lem2264742 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264743 : term377 = term383.
Proof. exact (@lem2264742 (NUMERAL 0) term32). Qed.
Lemma lem2264744 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264745 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264746 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264745 h1) (fun h1 : term383 = True => @lem2264744)). Qed.
Lemma lem2264747 : term383 = True.
Proof. exact (EQ_MP (@lem2264746) (@lem2264744)). Qed.
Lemma lem2264748 : term377 = True.
Proof. exact (TRANS (@lem2264743) (@lem2264747)). Qed.
Lemma lem2264749 : True = term377.
Proof. exact (SYM (@lem2264748)). Qed.
Lemma lem2264750 : term377.
Proof. exact (EQ_MP (@lem2264749) (@lem0)). Qed.
Lemma lem2264751 : term416.
Proof. exact (@lem2264740 (@lem2264750)). Qed.
Lemma lem2264753 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264754 : term377 = term383.
Proof. exact (@lem2264753 (NUMERAL 0) term32). Qed.
Lemma lem2264755 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264756 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264757 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264756 h1) (fun h1 : term383 = True => @lem2264755)). Qed.
Lemma lem2264758 : term383 = True.
Proof. exact (EQ_MP (@lem2264757) (@lem2264755)). Qed.
Lemma lem2264759 : term377 = True.
Proof. exact (TRANS (@lem2264754) (@lem2264758)). Qed.
Lemma lem2264760 : True = term377.
Proof. exact (SYM (@lem2264759)). Qed.
Lemma lem2264761 : term377.
Proof. exact (EQ_MP (@lem2264760) (@lem0)). Qed.
Lemma lem2264762 : term417.
Proof. exact (@lem2264751 (@lem2264761)). Qed.
Lemma lem2264764 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264765 : term41 = term42.
Proof. exact (@lem2264764 term32 term32). Qed.
Lemma lem2264766 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264767 : term44 = term32.
Proof. exact (EQ_MP (@lem2264766) (@lem940073)). Qed.
Lemma lem2264768 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264769 : term42 = term38.
Proof. exact (MK_COMB (@lem2264768) (@lem2264767)). Qed.
Lemma lem2264770 : term41 = term38.
Proof. exact (TRANS (@lem2264765) (@lem2264769)). Qed.
Lemma lem2264772 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2264773 : term420 = term421.
Proof. exact (@lem2264772 term32 term32). Qed.
Lemma lem2264774 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264775 : term44 = term32.
Proof. exact (EQ_MP (@lem2264774) (@lem940073)). Qed.
Lemma lem2264776 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264777 : term42 = term38.
Proof. exact (MK_COMB (@lem2264776) (@lem2264775)). Qed.
Lemma lem2264778 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2264779 : term421 = term26.
Proof. exact (MK_COMB (@lem2264778) (@lem2264777)). Qed.
Lemma lem2264780 : term420 = term26.
Proof. exact (TRANS (@lem2264773) (@lem2264779)). Qed.
Lemma lem2264781 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2264782 : term422 = term410.
Proof. exact (MK_COMB (@lem2264781) (@lem2264780)). Qed.
Lemma lem2264783 : term423 = term412.
Proof. exact (MK_COMB (@lem2264782) (@lem2264770)). Qed.
Lemma lem2264785 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2264786 : term412 = term14.
Proof. exact (@lem2264785 term32). Qed.
Lemma lem2264787 : term423 = term14.
Proof. exact (TRANS (@lem2264783) (@lem2264786)). Qed.
Lemma lem2264788 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264789 : term425 = term426.
Proof. exact (MK_COMB (@lem2264788) (@lem2264787)). Qed.
Lemma lem2264790 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2264791 : term427 = term388.
Proof. exact (MK_COMB (@lem2264789) (@lem2264790)). Qed.
Lemma lem2264793 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264794 : term388 = term14.
Proof. exact (@lem2264793 term32). Qed.
Lemma lem2264795 : term427 = term14.
Proof. exact (TRANS (@lem2264791) (@lem2264794)). Qed.
Lemma lem2264797 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264798 : term41 = term42.
Proof. exact (@lem2264797 term32 term32). Qed.
Lemma lem2264799 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264800 : term44 = term32.
Proof. exact (EQ_MP (@lem2264799) (@lem940073)). Qed.
Lemma lem2264801 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264802 : term42 = term38.
Proof. exact (MK_COMB (@lem2264801) (@lem2264800)). Qed.
Lemma lem2264803 : term41 = term38.
Proof. exact (TRANS (@lem2264798) (@lem2264802)). Qed.
Lemma lem2264804 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2264805 : term428 = term388.
Proof. exact (MK_COMB (@lem2264804) (@lem2264803)). Qed.
Lemma lem2264807 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264808 : term388 = term14.
Proof. exact (@lem2264807 term32). Qed.
Lemma lem2264809 : term428 = term14.
Proof. exact (TRANS (@lem2264805) (@lem2264808)). Qed.
Lemma lem2264810 : term14 = term428.
Proof. exact (SYM (@lem2264809)). Qed.
Lemma lem2264811 : term427 = term428.
Proof. exact (TRANS (@lem2264795) (@lem2264810)). Qed.
Lemma lem2264812 : term413 = term180.
Proof. exact (@lem2264762 (@lem2264811)). Qed.
Lemma lem2264813 : term412 = term180.
Proof. exact (TRANS (@lem2264728) (@lem2264812)). Qed.
Lemma lem2264815 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2264816 : term180 = term14.
Proof. exact (@lem2264815 term14). Qed.
Lemma lem2264817 : term412 = term14.
Proof. exact (TRANS (@lem2264813) (@lem2264816)). Qed.
Lemma lem2264818 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2264819 : term429 = term426.
Proof. exact (MK_COMB (@lem2264818) (@lem2264817)). Qed.
Lemma lem2264820 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2264821 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2264819) (@lem2264820 n)). Qed.
Lemma lem2264822 (n : nat) : (term460 n) = (term387 n).
Proof. exact (TRANS (@lem2264719 n) (@lem2264821 n)). Qed.
Lemma lem2264823 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2264824 (n : nat) : (term460 n) = term14.
Proof. exact (TRANS (@lem2264822 n) (@lem2264823 n)). Qed.
Lemma lem2264825 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem2264826 (n : nat) (x : real) : (term506 x n) = (term187 x).
Proof. exact (MK_COMB (@lem2264825 x) (@lem2264824 n)). Qed.
Lemma lem2264827 (n : nat) (x : real) : (term505 x n) = (term187 x).
Proof. exact (TRANS (@lem2264718 x n) (@lem2264826 n x)). Qed.
Lemma lem2264828 (x : real) : (term187 x) = x.
Proof. exact (@lem1982723 x). Qed.
Lemma lem2264829 (n : nat) (x : real) : (term505 x n) = x.
Proof. exact (TRANS (@lem2264827 n x) (@lem2264828 x)). Qed.
Lemma lem2264830 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2264831 (n : nat) (x : real) : (term507 x n) = (real_ge x).
Proof. exact (MK_COMB (@lem2264830) (@lem2264829 n x)). Qed.
Lemma lem2264832 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2264833 (n : nat) (x : real) : (term504 x n) = (term175 x).
Proof. exact (MK_COMB (@lem2264831 n x) (@lem2264832)). Qed.
Lemma lem2264834 (x : real) (n : nat) (h1 : term325 x n) : term175 x.
Proof. exact (EQ_MP (@lem2264833 n x) (@lem2264717 x n h1)). Qed.
Lemma lem2264836 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2264837 : term508 = term509.
Proof. exact (@lem2264836 term14 term510). Qed.
Lemma lem2264839 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264840 : term510 = term511.
Proof. exact (@lem2264839 term512). Qed.
Lemma lem2264842 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264843 : term14 = term180.
Proof. exact (@lem2264842 (NUMERAL 0)). Qed.
Lemma lem2264844 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264845 : term378 = term379.
Proof. exact (MK_COMB (@lem2264844) (@lem2264843)). Qed.
Lemma lem2264846 : term509 = term513.
Proof. exact (MK_COMB (@lem2264845) (@lem2264840)). Qed.
Lemma lem2264847 : term514.
Proof. exact (@lem1980255 term14 term38 term510 term38). Qed.
Lemma lem2264849 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264850 : term377 = term383.
Proof. exact (@lem2264849 (NUMERAL 0) term32). Qed.
Lemma lem2264851 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264852 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264853 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264852 h1) (fun h1 : term383 = True => @lem2264851)). Qed.
Lemma lem2264854 : term383 = True.
Proof. exact (EQ_MP (@lem2264853) (@lem2264851)). Qed.
Lemma lem2264855 : term377 = True.
Proof. exact (TRANS (@lem2264850) (@lem2264854)). Qed.
Lemma lem2264856 : True = term377.
Proof. exact (SYM (@lem2264855)). Qed.
Lemma lem2264857 : term377.
Proof. exact (EQ_MP (@lem2264856) (@lem0)). Qed.
Lemma lem2264858 : term515.
Proof. exact (@lem2264847 (@lem2264857)). Qed.
Lemma lem2264860 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264861 : term377 = term383.
Proof. exact (@lem2264860 (NUMERAL 0) term32). Qed.
Lemma lem2264862 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264863 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264864 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264863 h1) (fun h1 : term383 = True => @lem2264862)). Qed.
Lemma lem2264865 : term383 = True.
Proof. exact (EQ_MP (@lem2264864) (@lem2264862)). Qed.
Lemma lem2264866 : term377 = True.
Proof. exact (TRANS (@lem2264861) (@lem2264865)). Qed.
Lemma lem2264867 : True = term377.
Proof. exact (SYM (@lem2264866)). Qed.
Lemma lem2264868 : term377.
Proof. exact (EQ_MP (@lem2264867) (@lem0)). Qed.
Lemma lem2264869 : term513 = term516.
Proof. exact (@lem2264858 (@lem2264868)). Qed.
Lemma lem2264871 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264872 : term517 = term518.
Proof. exact (@lem2264871 term512 term32). Qed.
Lemma lem2264873 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2264874 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2264875 : term521 = term512.
Proof. exact (EQ_MP (@lem2264874) (@lem2264873)). Qed.
Lemma lem2264876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264877 : term518 = term510.
Proof. exact (MK_COMB (@lem2264876) (@lem2264875)). Qed.
Lemma lem2264878 : term517 = term510.
Proof. exact (TRANS (@lem2264872) (@lem2264877)). Qed.
Lemma lem2264880 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264881 : term388 = term14.
Proof. exact (@lem2264880 term32). Qed.
Lemma lem2264882 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264883 : term389 = term378.
Proof. exact (MK_COMB (@lem2264882) (@lem2264881)). Qed.
Lemma lem2264884 : term516 = term509.
Proof. exact (MK_COMB (@lem2264883) (@lem2264878)). Qed.
Lemma lem2264886 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264887 : term509 = term522.
Proof. exact (@lem2264886 (NUMERAL 0) term512). Qed.
Lemma lem2264888 : term523 = term520.
Proof. exact (@lem912803). Qed.
Lemma lem2264889 (h1 : term523 = term520) : term522 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term520 h1). Qed.
Lemma lem2264890 : (term523 = term520) = (term522 = True).
Proof. exact (prop_ext (fun h1 : term523 = term520 => @lem2264889 h1) (fun h1 : term522 = True => @lem2264888)). Qed.
Lemma lem2264891 : term522 = True.
Proof. exact (EQ_MP (@lem2264890) (@lem2264888)). Qed.
Lemma lem2264892 : term509 = True.
Proof. exact (TRANS (@lem2264887) (@lem2264891)). Qed.
Lemma lem2264893 : term516 = True.
Proof. exact (TRANS (@lem2264884) (@lem2264892)). Qed.
Lemma lem2264894 : term513 = True.
Proof. exact (TRANS (@lem2264869) (@lem2264893)). Qed.
Lemma lem2264895 : term509 = True.
Proof. exact (TRANS (@lem2264846) (@lem2264894)). Qed.
Lemma lem2264896 : term508 = True.
Proof. exact (TRANS (@lem2264837) (@lem2264895)). Qed.
Lemma lem2264897 : True = term508.
Proof. exact (SYM (@lem2264896)). Qed.
Lemma lem2264898 : term508.
Proof. exact (EQ_MP (@lem2264897) (@lem0)). Qed.
Lemma lem2264899 (x : real) (n : nat) (h1 : term325 x n) : term524 x.
Proof. exact (conj (@lem2264898) (@lem2264834 x n h1)). Qed.
Lemma lem2264901 (x : real) (y : real) : term496 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2264902 (x : real) : term525 x.
Proof. exact (@lem2264901 term510 x). Qed.
Lemma lem2264909 (x : real) (n : nat) (h1 : term325 x n) : term526 x.
Proof. exact (@lem2264902 x (@lem2264899 x n h1)). Qed.
Lemma lem2264911 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2264912 : term376 = term377.
Proof. exact (@lem2264911 term14 term38). Qed.
Lemma lem2264914 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264915 : term38 = term48.
Proof. exact (@lem2264914 term32). Qed.
Lemma lem2264917 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2264918 : term14 = term180.
Proof. exact (@lem2264917 (NUMERAL 0)). Qed.
Lemma lem2264919 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264920 : term378 = term379.
Proof. exact (MK_COMB (@lem2264919) (@lem2264918)). Qed.
Lemma lem2264921 : term377 = term380.
Proof. exact (MK_COMB (@lem2264920) (@lem2264915)). Qed.
Lemma lem2264922 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2264924 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264925 : term377 = term383.
Proof. exact (@lem2264924 (NUMERAL 0) term32). Qed.
Lemma lem2264926 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264927 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264928 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264927 h1) (fun h1 : term383 = True => @lem2264926)). Qed.
Lemma lem2264929 : term383 = True.
Proof. exact (EQ_MP (@lem2264928) (@lem2264926)). Qed.
Lemma lem2264930 : term377 = True.
Proof. exact (TRANS (@lem2264925) (@lem2264929)). Qed.
Lemma lem2264931 : True = term377.
Proof. exact (SYM (@lem2264930)). Qed.
Lemma lem2264932 : term377.
Proof. exact (EQ_MP (@lem2264931) (@lem0)). Qed.
Lemma lem2264933 : term385.
Proof. exact (@lem2264922 (@lem2264932)). Qed.
Lemma lem2264935 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264936 : term377 = term383.
Proof. exact (@lem2264935 (NUMERAL 0) term32). Qed.
Lemma lem2264937 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264938 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264939 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264938 h1) (fun h1 : term383 = True => @lem2264937)). Qed.
Lemma lem2264940 : term383 = True.
Proof. exact (EQ_MP (@lem2264939) (@lem2264937)). Qed.
Lemma lem2264941 : term377 = True.
Proof. exact (TRANS (@lem2264936) (@lem2264940)). Qed.
Lemma lem2264942 : True = term377.
Proof. exact (SYM (@lem2264941)). Qed.
Lemma lem2264943 : term377.
Proof. exact (EQ_MP (@lem2264942) (@lem0)). Qed.
Lemma lem2264944 : term380 = term386.
Proof. exact (@lem2264933 (@lem2264943)). Qed.
Lemma lem2264946 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2264947 : term41 = term42.
Proof. exact (@lem2264946 term32 term32). Qed.
Lemma lem2264948 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2264949 : term44 = term32.
Proof. exact (EQ_MP (@lem2264948) (@lem940073)). Qed.
Lemma lem2264950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2264951 : term42 = term38.
Proof. exact (MK_COMB (@lem2264950) (@lem2264949)). Qed.
Lemma lem2264952 : term41 = term38.
Proof. exact (TRANS (@lem2264947) (@lem2264951)). Qed.
Lemma lem2264954 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2264955 : term388 = term14.
Proof. exact (@lem2264954 term32). Qed.
Lemma lem2264956 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2264957 : term389 = term378.
Proof. exact (MK_COMB (@lem2264956) (@lem2264955)). Qed.
Lemma lem2264958 : term386 = term377.
Proof. exact (MK_COMB (@lem2264957) (@lem2264952)). Qed.
Lemma lem2264960 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2264961 : term377 = term383.
Proof. exact (@lem2264960 (NUMERAL 0) term32). Qed.
Lemma lem2264962 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2264963 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2264964 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2264963 h1) (fun h1 : term383 = True => @lem2264962)). Qed.
Lemma lem2264965 : term383 = True.
Proof. exact (EQ_MP (@lem2264964) (@lem2264962)). Qed.
Lemma lem2264966 : term377 = True.
Proof. exact (TRANS (@lem2264961) (@lem2264965)). Qed.
Lemma lem2264967 : term386 = True.
Proof. exact (TRANS (@lem2264958) (@lem2264966)). Qed.
Lemma lem2264968 : term380 = True.
Proof. exact (TRANS (@lem2264944) (@lem2264967)). Qed.
Lemma lem2264969 : term377 = True.
Proof. exact (TRANS (@lem2264921) (@lem2264968)). Qed.
Lemma lem2264970 : term376 = True.
Proof. exact (TRANS (@lem2264912) (@lem2264969)). Qed.
Lemma lem2264971 : True = term376.
Proof. exact (SYM (@lem2264970)). Qed.
Lemma lem2264972 : term376.
Proof. exact (EQ_MP (@lem2264971) (@lem0)). Qed.
Lemma lem2264973 (x : real) (n : nat) (h1 : term325 x n) : term477 x n.
Proof. exact (conj (@lem2264972) (@lem2264624 x n h1)). Qed.
Lemma lem2264975 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2264976 (x : real) (n : nat) : term478 x n.
Proof. exact (@lem2264975 term38 (term76 x n)). Qed.
Lemma lem2264977 (x : real) (n : nat) (h1 : term325 x n) : term479 x n.
Proof. exact (@lem2264976 x n (@lem2264973 x n h1)). Qed.
Lemma lem2264978 (x : real) (n : nat) : (term453 x n) = (term76 x n).
Proof. exact (@lem1982733 (term76 x n)). Qed.
Lemma lem2264979 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2264980 (x : real) (n : nat) : (term480 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem2264979) (@lem2264978 x n)). Qed.
Lemma lem2264981 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2264982 (x : real) (n : nat) : (term479 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2264980 x n) (@lem2264981)). Qed.
Lemma lem2264983 (x : real) (n : nat) (h1 : term325 x n) : term81 x n.
Proof. exact (EQ_MP (@lem2264982 x n) (@lem2264977 x n h1)). Qed.
Lemma lem2264985 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2264986 (x : real) (n : nat) : term397 x n.
Proof. exact (@lem2264985 (term21 x n)). Qed.
Lemma lem2264987 (x : real) (n : nat) (h1 : term325 x n) : term398 x n.
Proof. exact (@lem2264986 x n (@lem2264623 x n h1)). Qed.
Lemma lem2264988 (x : real) (n : nat) (h1 : term325 x n) : term399 x n.
Proof. exact (@lem2264987 x n h1 term26). Qed.
Lemma lem2264989 (x : real) (n : nat) : (term399 x n) = ((term24 x n) = term14).
Proof. exact (eq_refl (term399 x n)). Qed.
Lemma lem2264990 (x : real) (n : nat) (h1 : term325 x n) : (term24 x n) = term14.
Proof. exact (EQ_MP (@lem2264989 x n) (@lem2264988 x n h1)). Qed.
Lemma lem2264991 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (@lem1982781 x term26 (term27 n)). Qed.
Lemma lem2264992 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem1982749 term26 term26 (real_of_num n)). Qed.
Lemma lem2264994 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2264995 : term26 = term31.
Proof. exact (@lem2264994 term32). Qed.
Lemma lem2264997 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2264998 : term26 = term31.
Proof. exact (@lem2264997 term32). Qed.
Lemma lem2264999 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265000 : term33 = term34.
Proof. exact (MK_COMB (@lem2264999) (@lem2264998)). Qed.
Lemma lem2265001 : term35 = term36.
Proof. exact (MK_COMB (@lem2265000) (@lem2264995)). Qed.
Lemma lem2265002 : term36 = term37.
Proof. exact (@lem1981613 term26 term26 term38 term38). Qed.
Lemma lem2265004 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265005 : term41 = term42.
Proof. exact (@lem2265004 term32 term32). Qed.
Lemma lem2265006 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265007 : term44 = term32.
Proof. exact (EQ_MP (@lem2265006) (@lem940073)). Qed.
Lemma lem2265008 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265009 : term42 = term38.
Proof. exact (MK_COMB (@lem2265008) (@lem2265007)). Qed.
Lemma lem2265010 : term41 = term38.
Proof. exact (TRANS (@lem2265005) (@lem2265009)). Qed.
Lemma lem2265012 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2265013 : term35 = term42.
Proof. exact (@lem2265012 term32 term32). Qed.
Lemma lem2265014 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265015 : term44 = term32.
Proof. exact (EQ_MP (@lem2265014) (@lem940073)). Qed.
Lemma lem2265016 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265017 : term42 = term38.
Proof. exact (MK_COMB (@lem2265016) (@lem2265015)). Qed.
Lemma lem2265018 : term35 = term38.
Proof. exact (TRANS (@lem2265013) (@lem2265017)). Qed.
Lemma lem2265019 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2265020 : term46 = term47.
Proof. exact (MK_COMB (@lem2265019) (@lem2265018)). Qed.
Lemma lem2265021 : term37 = term48.
Proof. exact (MK_COMB (@lem2265020) (@lem2265010)). Qed.
Lemma lem2265022 : term36 = term48.
Proof. exact (TRANS (@lem2265002) (@lem2265021)). Qed.
Lemma lem2265023 : term35 = term48.
Proof. exact (TRANS (@lem2265001) (@lem2265022)). Qed.
Lemma lem2265025 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2265026 : term48 = term38.
Proof. exact (@lem2265025 term38). Qed.
Lemma lem2265027 : term35 = term38.
Proof. exact (TRANS (@lem2265023) (@lem2265026)). Qed.
Lemma lem2265028 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265029 : term50 = term51.
Proof. exact (MK_COMB (@lem2265028) (@lem2265027)). Qed.
Lemma lem2265030 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2265031 (n : nat) : (term29 n) = (term52 n).
Proof. exact (MK_COMB (@lem2265029) (@lem2265030 n)). Qed.
Lemma lem2265032 (n : nat) : (term28 n) = (term52 n).
Proof. exact (TRANS (@lem2264992 n) (@lem2265031 n)). Qed.
Lemma lem2265033 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem2265034 (n : nat) : (term28 n) = (real_of_num n).
Proof. exact (TRANS (@lem2265032 n) (@lem2265033 n)). Qed.
Lemma lem2265037 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2265038 (x : real) (n : nat) : (term25 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem2265037 x) (@lem2265034 n)). Qed.
Lemma lem2265039 (x : real) (n : nat) : (term24 x n) = (term54 x n).
Proof. exact (TRANS (@lem2264991 x n) (@lem2265038 x n)). Qed.
Lemma lem2265040 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2265041 (x : real) (n : nat) : (term400 x n) = (term401 x n).
Proof. exact (MK_COMB (@lem2265040) (@lem2265039 x n)). Qed.
Lemma lem2265042 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2265043 (x : real) (n : nat) : ((term24 x n) = term14) = ((term54 x n) = term14).
Proof. exact (MK_COMB (@lem2265041 x n) (@lem2265042)). Qed.
Lemma lem2265044 (x : real) (n : nat) (h1 : term325 x n) : (term54 x n) = term14.
Proof. exact (EQ_MP (@lem2265043 x n) (@lem2264990 x n h1)). Qed.
Lemma lem2265045 (x : real) (n : nat) (h1 : term325 x n) : term527 x n.
Proof. exact (conj (@lem2265044 x n h1) (@lem2264983 x n h1)). Qed.
Lemma lem2265047 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2265048 (x : real) (n : nat) : term528 x n.
Proof. exact (@lem2265047 (term54 x n) (term76 x n)). Qed.
Lemma lem2265049 (x : real) (n : nat) (h1 : term325 x n) : term529 x n.
Proof. exact (@lem2265048 x n (@lem2265045 x n h1)). Qed.
Lemma lem2265050 (x : real) (n : nat) : (term530 x n) = (term531 x n).
Proof. exact (@lem1982753 (term208 x) (term208 x) (real_of_num n) (term27 n)). Qed.
Lemma lem2265051 (x : real) : (term532 x) = (term533 x).
Proof. exact (@lem1982711 term26 term26 x). Qed.
Lemma lem2265053 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2265054 : term26 = term31.
Proof. exact (@lem2265053 term32). Qed.
Lemma lem2265056 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2265057 : term26 = term31.
Proof. exact (@lem2265056 term32). Qed.
Lemma lem2265058 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265059 : term410 = term411.
Proof. exact (MK_COMB (@lem2265058) (@lem2265057)). Qed.
Lemma lem2265060 : term534 = term535.
Proof. exact (MK_COMB (@lem2265059) (@lem2265054)). Qed.
Lemma lem2265061 : term536.
Proof. exact (@lem1981473 term26 term38 term26 term38 term537 term38). Qed.
Lemma lem2265063 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265064 : term377 = term383.
Proof. exact (@lem2265063 (NUMERAL 0) term32). Qed.
Lemma lem2265065 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265066 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265067 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265066 h1) (fun h1 : term383 = True => @lem2265065)). Qed.
Lemma lem2265068 : term383 = True.
Proof. exact (EQ_MP (@lem2265067) (@lem2265065)). Qed.
Lemma lem2265069 : term377 = True.
Proof. exact (TRANS (@lem2265064) (@lem2265068)). Qed.
Lemma lem2265070 : True = term377.
Proof. exact (SYM (@lem2265069)). Qed.
Lemma lem2265071 : term377.
Proof. exact (EQ_MP (@lem2265070) (@lem0)). Qed.
Lemma lem2265072 : term538.
Proof. exact (@lem2265061 (@lem2265071)). Qed.
Lemma lem2265074 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265075 : term377 = term383.
Proof. exact (@lem2265074 (NUMERAL 0) term32). Qed.
Lemma lem2265076 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265077 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265078 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265077 h1) (fun h1 : term383 = True => @lem2265076)). Qed.
Lemma lem2265079 : term383 = True.
Proof. exact (EQ_MP (@lem2265078) (@lem2265076)). Qed.
Lemma lem2265080 : term377 = True.
Proof. exact (TRANS (@lem2265075) (@lem2265079)). Qed.
Lemma lem2265081 : True = term377.
Proof. exact (SYM (@lem2265080)). Qed.
Lemma lem2265082 : term377.
Proof. exact (EQ_MP (@lem2265081) (@lem0)). Qed.
Lemma lem2265083 : term539.
Proof. exact (@lem2265072 (@lem2265082)). Qed.
Lemma lem2265085 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265086 : term377 = term383.
Proof. exact (@lem2265085 (NUMERAL 0) term32). Qed.
Lemma lem2265087 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265088 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265089 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265088 h1) (fun h1 : term383 = True => @lem2265087)). Qed.
Lemma lem2265090 : term383 = True.
Proof. exact (EQ_MP (@lem2265089) (@lem2265087)). Qed.
Lemma lem2265091 : term377 = True.
Proof. exact (TRANS (@lem2265086) (@lem2265090)). Qed.
Lemma lem2265092 : True = term377.
Proof. exact (SYM (@lem2265091)). Qed.
Lemma lem2265093 : term377.
Proof. exact (EQ_MP (@lem2265092) (@lem0)). Qed.
Lemma lem2265094 : term540.
Proof. exact (@lem2265083 (@lem2265093)). Qed.
Lemma lem2265096 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2265097 : term420 = term421.
Proof. exact (@lem2265096 term32 term32). Qed.
Lemma lem2265098 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265099 : term44 = term32.
Proof. exact (EQ_MP (@lem2265098) (@lem940073)). Qed.
Lemma lem2265100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265101 : term42 = term38.
Proof. exact (MK_COMB (@lem2265100) (@lem2265099)). Qed.
Lemma lem2265102 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265103 : term421 = term26.
Proof. exact (MK_COMB (@lem2265102) (@lem2265101)). Qed.
Lemma lem2265104 : term420 = term26.
Proof. exact (TRANS (@lem2265097) (@lem2265103)). Qed.
Lemma lem2265106 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2265107 : term420 = term421.
Proof. exact (@lem2265106 term32 term32). Qed.
Lemma lem2265108 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265109 : term44 = term32.
Proof. exact (EQ_MP (@lem2265108) (@lem940073)). Qed.
Lemma lem2265110 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265111 : term42 = term38.
Proof. exact (MK_COMB (@lem2265110) (@lem2265109)). Qed.
Lemma lem2265112 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265113 : term421 = term26.
Proof. exact (MK_COMB (@lem2265112) (@lem2265111)). Qed.
Lemma lem2265114 : term420 = term26.
Proof. exact (TRANS (@lem2265107) (@lem2265113)). Qed.
Lemma lem2265115 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265116 : term422 = term410.
Proof. exact (MK_COMB (@lem2265115) (@lem2265114)). Qed.
Lemma lem2265117 : term541 = term534.
Proof. exact (MK_COMB (@lem2265116) (@lem2265104)). Qed.
Lemma lem2265118 : term534 = term542.
Proof. exact (@lem1367763 term32 term32). Qed.
Lemma lem2265119 : term543 = term520.
Proof. exact (@lem706885). Qed.
Lemma lem2265120 : (term543 = term520) = (term544 = term512).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term520). Qed.
Lemma lem2265121 : term544 = term512.
Proof. exact (EQ_MP (@lem2265120) (@lem2265119)). Qed.
Lemma lem2265122 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265123 : term545 = term510.
Proof. exact (MK_COMB (@lem2265122) (@lem2265121)). Qed.
Lemma lem2265124 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265125 : term542 = term537.
Proof. exact (MK_COMB (@lem2265124) (@lem2265123)). Qed.
Lemma lem2265126 : term534 = term537.
Proof. exact (TRANS (@lem2265118) (@lem2265125)). Qed.
Lemma lem2265127 : term541 = term537.
Proof. exact (TRANS (@lem2265117) (@lem2265126)). Qed.
Lemma lem2265128 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265129 : term546 = term547.
Proof. exact (MK_COMB (@lem2265128) (@lem2265127)). Qed.
Lemma lem2265130 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2265131 : term548 = term549.
Proof. exact (MK_COMB (@lem2265129) (@lem2265130)). Qed.
Lemma lem2265133 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2265134 : term549 = term550.
Proof. exact (@lem2265133 term512 term32). Qed.
Lemma lem2265135 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2265136 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2265137 : term521 = term512.
Proof. exact (EQ_MP (@lem2265136) (@lem2265135)). Qed.
Lemma lem2265138 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265139 : term518 = term510.
Proof. exact (MK_COMB (@lem2265138) (@lem2265137)). Qed.
Lemma lem2265140 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265141 : term550 = term537.
Proof. exact (MK_COMB (@lem2265140) (@lem2265139)). Qed.
Lemma lem2265142 : term549 = term537.
Proof. exact (TRANS (@lem2265134) (@lem2265141)). Qed.
Lemma lem2265143 : term548 = term537.
Proof. exact (TRANS (@lem2265131) (@lem2265142)). Qed.
Lemma lem2265145 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265146 : term41 = term42.
Proof. exact (@lem2265145 term32 term32). Qed.
Lemma lem2265147 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265148 : term44 = term32.
Proof. exact (EQ_MP (@lem2265147) (@lem940073)). Qed.
Lemma lem2265149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265150 : term42 = term38.
Proof. exact (MK_COMB (@lem2265149) (@lem2265148)). Qed.
Lemma lem2265151 : term41 = term38.
Proof. exact (TRANS (@lem2265146) (@lem2265150)). Qed.
Lemma lem2265152 : term547 = term547.
Proof. exact (eq_refl term547). Qed.
Lemma lem2265153 : term551 = term549.
Proof. exact (MK_COMB (@lem2265152) (@lem2265151)). Qed.
Lemma lem2265155 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2265156 : term549 = term550.
Proof. exact (@lem2265155 term512 term32). Qed.
Lemma lem2265157 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2265158 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2265159 : term521 = term512.
Proof. exact (EQ_MP (@lem2265158) (@lem2265157)). Qed.
Lemma lem2265160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265161 : term518 = term510.
Proof. exact (MK_COMB (@lem2265160) (@lem2265159)). Qed.
Lemma lem2265162 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265163 : term550 = term537.
Proof. exact (MK_COMB (@lem2265162) (@lem2265161)). Qed.
Lemma lem2265164 : term549 = term537.
Proof. exact (TRANS (@lem2265156) (@lem2265163)). Qed.
Lemma lem2265165 : term551 = term537.
Proof. exact (TRANS (@lem2265153) (@lem2265164)). Qed.
Lemma lem2265166 : term537 = term551.
Proof. exact (SYM (@lem2265165)). Qed.
Lemma lem2265167 : term548 = term551.
Proof. exact (TRANS (@lem2265143) (@lem2265166)). Qed.
Lemma lem2265168 : term535 = term552.
Proof. exact (@lem2265094 (@lem2265167)). Qed.
Lemma lem2265169 : term534 = term552.
Proof. exact (TRANS (@lem2265060) (@lem2265168)). Qed.
Lemma lem2265171 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2265172 : term552 = term537.
Proof. exact (@lem2265171 term537). Qed.
Lemma lem2265173 : term534 = term537.
Proof. exact (TRANS (@lem2265169) (@lem2265172)). Qed.
Lemma lem2265174 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265175 : term553 = term547.
Proof. exact (MK_COMB (@lem2265174) (@lem2265173)). Qed.
Lemma lem2265176 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2265177 (x : real) : (term533 x) = (term554 x).
Proof. exact (MK_COMB (@lem2265175) (@lem2265176 x)). Qed.
Lemma lem2265178 (x : real) : (term532 x) = (term554 x).
Proof. exact (TRANS (@lem2265051 x) (@lem2265177 x)). Qed.
Lemma lem2265179 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265180 (x : real) : (term555 x) = (term556 x).
Proof. exact (MK_COMB (@lem2265179) (@lem2265178 x)). Qed.
Lemma lem2265181 (n : nat) : (term433 n) = (term434 n).
Proof. exact (@lem1982715 term26 (real_of_num n)). Qed.
Lemma lem2265183 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265184 : term38 = term48.
Proof. exact (@lem2265183 term32). Qed.
Lemma lem2265186 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2265187 : term26 = term31.
Proof. exact (@lem2265186 term32). Qed.
Lemma lem2265188 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265189 : term410 = term411.
Proof. exact (MK_COMB (@lem2265188) (@lem2265187)). Qed.
Lemma lem2265190 : term412 = term413.
Proof. exact (MK_COMB (@lem2265189) (@lem2265184)). Qed.
Lemma lem2265191 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2265193 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265194 : term377 = term383.
Proof. exact (@lem2265193 (NUMERAL 0) term32). Qed.
Lemma lem2265195 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265196 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265197 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265196 h1) (fun h1 : term383 = True => @lem2265195)). Qed.
Lemma lem2265198 : term383 = True.
Proof. exact (EQ_MP (@lem2265197) (@lem2265195)). Qed.
Lemma lem2265199 : term377 = True.
Proof. exact (TRANS (@lem2265194) (@lem2265198)). Qed.
Lemma lem2265200 : True = term377.
Proof. exact (SYM (@lem2265199)). Qed.
Lemma lem2265201 : term377.
Proof. exact (EQ_MP (@lem2265200) (@lem0)). Qed.
Lemma lem2265202 : term415.
Proof. exact (@lem2265191 (@lem2265201)). Qed.
Lemma lem2265204 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265205 : term377 = term383.
Proof. exact (@lem2265204 (NUMERAL 0) term32). Qed.
Lemma lem2265206 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265207 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265208 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265207 h1) (fun h1 : term383 = True => @lem2265206)). Qed.
Lemma lem2265209 : term383 = True.
Proof. exact (EQ_MP (@lem2265208) (@lem2265206)). Qed.
Lemma lem2265210 : term377 = True.
Proof. exact (TRANS (@lem2265205) (@lem2265209)). Qed.
Lemma lem2265211 : True = term377.
Proof. exact (SYM (@lem2265210)). Qed.
Lemma lem2265212 : term377.
Proof. exact (EQ_MP (@lem2265211) (@lem0)). Qed.
Lemma lem2265213 : term416.
Proof. exact (@lem2265202 (@lem2265212)). Qed.
Lemma lem2265215 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265216 : term377 = term383.
Proof. exact (@lem2265215 (NUMERAL 0) term32). Qed.
Lemma lem2265217 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265218 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265219 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265218 h1) (fun h1 : term383 = True => @lem2265217)). Qed.
Lemma lem2265220 : term383 = True.
Proof. exact (EQ_MP (@lem2265219) (@lem2265217)). Qed.
Lemma lem2265221 : term377 = True.
Proof. exact (TRANS (@lem2265216) (@lem2265220)). Qed.
Lemma lem2265222 : True = term377.
Proof. exact (SYM (@lem2265221)). Qed.
Lemma lem2265223 : term377.
Proof. exact (EQ_MP (@lem2265222) (@lem0)). Qed.
Lemma lem2265224 : term417.
Proof. exact (@lem2265213 (@lem2265223)). Qed.
Lemma lem2265226 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265227 : term41 = term42.
Proof. exact (@lem2265226 term32 term32). Qed.
Lemma lem2265228 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265229 : term44 = term32.
Proof. exact (EQ_MP (@lem2265228) (@lem940073)). Qed.
Lemma lem2265230 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265231 : term42 = term38.
Proof. exact (MK_COMB (@lem2265230) (@lem2265229)). Qed.
Lemma lem2265232 : term41 = term38.
Proof. exact (TRANS (@lem2265227) (@lem2265231)). Qed.
Lemma lem2265234 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2265235 : term420 = term421.
Proof. exact (@lem2265234 term32 term32). Qed.
Lemma lem2265236 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265237 : term44 = term32.
Proof. exact (EQ_MP (@lem2265236) (@lem940073)). Qed.
Lemma lem2265238 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265239 : term42 = term38.
Proof. exact (MK_COMB (@lem2265238) (@lem2265237)). Qed.
Lemma lem2265240 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265241 : term421 = term26.
Proof. exact (MK_COMB (@lem2265240) (@lem2265239)). Qed.
Lemma lem2265242 : term420 = term26.
Proof. exact (TRANS (@lem2265235) (@lem2265241)). Qed.
Lemma lem2265243 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265244 : term422 = term410.
Proof. exact (MK_COMB (@lem2265243) (@lem2265242)). Qed.
Lemma lem2265245 : term423 = term412.
Proof. exact (MK_COMB (@lem2265244) (@lem2265232)). Qed.
Lemma lem2265247 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2265248 : term412 = term14.
Proof. exact (@lem2265247 term32). Qed.
Lemma lem2265249 : term423 = term14.
Proof. exact (TRANS (@lem2265245) (@lem2265248)). Qed.
Lemma lem2265250 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265251 : term425 = term426.
Proof. exact (MK_COMB (@lem2265250) (@lem2265249)). Qed.
Lemma lem2265252 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2265253 : term427 = term388.
Proof. exact (MK_COMB (@lem2265251) (@lem2265252)). Qed.
Lemma lem2265255 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265256 : term388 = term14.
Proof. exact (@lem2265255 term32). Qed.
Lemma lem2265257 : term427 = term14.
Proof. exact (TRANS (@lem2265253) (@lem2265256)). Qed.
Lemma lem2265259 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265260 : term41 = term42.
Proof. exact (@lem2265259 term32 term32). Qed.
Lemma lem2265261 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265262 : term44 = term32.
Proof. exact (EQ_MP (@lem2265261) (@lem940073)). Qed.
Lemma lem2265263 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265264 : term42 = term38.
Proof. exact (MK_COMB (@lem2265263) (@lem2265262)). Qed.
Lemma lem2265265 : term41 = term38.
Proof. exact (TRANS (@lem2265260) (@lem2265264)). Qed.
Lemma lem2265266 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2265267 : term428 = term388.
Proof. exact (MK_COMB (@lem2265266) (@lem2265265)). Qed.
Lemma lem2265269 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265270 : term388 = term14.
Proof. exact (@lem2265269 term32). Qed.
Lemma lem2265271 : term428 = term14.
Proof. exact (TRANS (@lem2265267) (@lem2265270)). Qed.
Lemma lem2265272 : term14 = term428.
Proof. exact (SYM (@lem2265271)). Qed.
Lemma lem2265273 : term427 = term428.
Proof. exact (TRANS (@lem2265257) (@lem2265272)). Qed.
Lemma lem2265274 : term413 = term180.
Proof. exact (@lem2265224 (@lem2265273)). Qed.
Lemma lem2265275 : term412 = term180.
Proof. exact (TRANS (@lem2265190) (@lem2265274)). Qed.
Lemma lem2265277 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2265278 : term180 = term14.
Proof. exact (@lem2265277 term14). Qed.
Lemma lem2265279 : term412 = term14.
Proof. exact (TRANS (@lem2265275) (@lem2265278)). Qed.
Lemma lem2265280 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265281 : term429 = term426.
Proof. exact (MK_COMB (@lem2265280) (@lem2265279)). Qed.
Lemma lem2265282 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2265283 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2265281) (@lem2265282 n)). Qed.
Lemma lem2265284 (n : nat) : (term433 n) = (term387 n).
Proof. exact (TRANS (@lem2265181 n) (@lem2265283 n)). Qed.
Lemma lem2265285 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2265286 (n : nat) : (term433 n) = term14.
Proof. exact (TRANS (@lem2265284 n) (@lem2265285 n)). Qed.
Lemma lem2265287 (n : nat) (x : real) : (term531 x n) = (term557 x).
Proof. exact (MK_COMB (@lem2265180 x) (@lem2265286 n)). Qed.
Lemma lem2265288 (n : nat) (x : real) : (term530 x n) = (term557 x).
Proof. exact (TRANS (@lem2265050 x n) (@lem2265287 n x)). Qed.
Lemma lem2265289 (x : real) : (term557 x) = (term554 x).
Proof. exact (@lem1982723 (term554 x)). Qed.
Lemma lem2265290 (n : nat) (x : real) : (term530 x n) = (term554 x).
Proof. exact (TRANS (@lem2265288 n x) (@lem2265289 x)). Qed.
Lemma lem2265291 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2265292 (n : nat) (x : real) : (term558 x n) = (term559 x).
Proof. exact (MK_COMB (@lem2265291) (@lem2265290 n x)). Qed.
Lemma lem2265293 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2265294 (n : nat) (x : real) : (term529 x n) = (term560 x).
Proof. exact (MK_COMB (@lem2265292 n x) (@lem2265293)). Qed.
Lemma lem2265295 (x : real) (n : nat) (h1 : term325 x n) : term560 x.
Proof. exact (EQ_MP (@lem2265294 n x) (@lem2265049 x n h1)). Qed.
Lemma lem2265297 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2265298 : term376 = term377.
Proof. exact (@lem2265297 term14 term38). Qed.
Lemma lem2265300 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265301 : term38 = term48.
Proof. exact (@lem2265300 term32). Qed.
Lemma lem2265303 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265304 : term14 = term180.
Proof. exact (@lem2265303 (NUMERAL 0)). Qed.
Lemma lem2265305 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265306 : term378 = term379.
Proof. exact (MK_COMB (@lem2265305) (@lem2265304)). Qed.
Lemma lem2265307 : term377 = term380.
Proof. exact (MK_COMB (@lem2265306) (@lem2265301)). Qed.
Lemma lem2265308 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2265310 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265311 : term377 = term383.
Proof. exact (@lem2265310 (NUMERAL 0) term32). Qed.
Lemma lem2265312 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265313 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265314 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265313 h1) (fun h1 : term383 = True => @lem2265312)). Qed.
Lemma lem2265315 : term383 = True.
Proof. exact (EQ_MP (@lem2265314) (@lem2265312)). Qed.
Lemma lem2265316 : term377 = True.
Proof. exact (TRANS (@lem2265311) (@lem2265315)). Qed.
Lemma lem2265317 : True = term377.
Proof. exact (SYM (@lem2265316)). Qed.
Lemma lem2265318 : term377.
Proof. exact (EQ_MP (@lem2265317) (@lem0)). Qed.
Lemma lem2265319 : term385.
Proof. exact (@lem2265308 (@lem2265318)). Qed.
Lemma lem2265321 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265322 : term377 = term383.
Proof. exact (@lem2265321 (NUMERAL 0) term32). Qed.
Lemma lem2265323 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265324 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265325 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265324 h1) (fun h1 : term383 = True => @lem2265323)). Qed.
Lemma lem2265326 : term383 = True.
Proof. exact (EQ_MP (@lem2265325) (@lem2265323)). Qed.
Lemma lem2265327 : term377 = True.
Proof. exact (TRANS (@lem2265322) (@lem2265326)). Qed.
Lemma lem2265328 : True = term377.
Proof. exact (SYM (@lem2265327)). Qed.
Lemma lem2265329 : term377.
Proof. exact (EQ_MP (@lem2265328) (@lem0)). Qed.
Lemma lem2265330 : term380 = term386.
Proof. exact (@lem2265319 (@lem2265329)). Qed.
Lemma lem2265332 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265333 : term41 = term42.
Proof. exact (@lem2265332 term32 term32). Qed.
Lemma lem2265334 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265335 : term44 = term32.
Proof. exact (EQ_MP (@lem2265334) (@lem940073)). Qed.
Lemma lem2265336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265337 : term42 = term38.
Proof. exact (MK_COMB (@lem2265336) (@lem2265335)). Qed.
Lemma lem2265338 : term41 = term38.
Proof. exact (TRANS (@lem2265333) (@lem2265337)). Qed.
Lemma lem2265340 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265341 : term388 = term14.
Proof. exact (@lem2265340 term32). Qed.
Lemma lem2265342 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265343 : term389 = term378.
Proof. exact (MK_COMB (@lem2265342) (@lem2265341)). Qed.
Lemma lem2265344 : term386 = term377.
Proof. exact (MK_COMB (@lem2265343) (@lem2265338)). Qed.
Lemma lem2265346 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265347 : term377 = term383.
Proof. exact (@lem2265346 (NUMERAL 0) term32). Qed.
Lemma lem2265348 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265349 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265350 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265349 h1) (fun h1 : term383 = True => @lem2265348)). Qed.
Lemma lem2265351 : term383 = True.
Proof. exact (EQ_MP (@lem2265350) (@lem2265348)). Qed.
Lemma lem2265352 : term377 = True.
Proof. exact (TRANS (@lem2265347) (@lem2265351)). Qed.
Lemma lem2265353 : term386 = True.
Proof. exact (TRANS (@lem2265344) (@lem2265352)). Qed.
Lemma lem2265354 : term380 = True.
Proof. exact (TRANS (@lem2265330) (@lem2265353)). Qed.
Lemma lem2265355 : term377 = True.
Proof. exact (TRANS (@lem2265307) (@lem2265354)). Qed.
Lemma lem2265356 : term376 = True.
Proof. exact (TRANS (@lem2265298) (@lem2265355)). Qed.
Lemma lem2265357 : True = term376.
Proof. exact (SYM (@lem2265356)). Qed.
Lemma lem2265358 : term376.
Proof. exact (EQ_MP (@lem2265357) (@lem0)). Qed.
Lemma lem2265359 (x : real) (n : nat) (h1 : term325 x n) : term561 x.
Proof. exact (conj (@lem2265358) (@lem2265295 x n h1)). Qed.
Lemma lem2265361 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2265362 (x : real) : term562 x.
Proof. exact (@lem2265361 term38 (term554 x)). Qed.
Lemma lem2265363 (x : real) (n : nat) (h1 : term325 x n) : term563 x.
Proof. exact (@lem2265362 x (@lem2265359 x n h1)). Qed.
Lemma lem2265364 (x : real) : (term564 x) = (term554 x).
Proof. exact (@lem1982733 (term554 x)). Qed.
Lemma lem2265365 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2265366 (x : real) : (term565 x) = (term559 x).
Proof. exact (MK_COMB (@lem2265365) (@lem2265364 x)). Qed.
Lemma lem2265367 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2265368 (x : real) : (term563 x) = (term560 x).
Proof. exact (MK_COMB (@lem2265366 x) (@lem2265367)). Qed.
Lemma lem2265369 (x : real) (n : nat) (h1 : term325 x n) : term560 x.
Proof. exact (EQ_MP (@lem2265368 x) (@lem2265363 x n h1)). Qed.
Lemma lem2265370 (x : real) (n : nat) (h1 : term325 x n) : term566 x.
Proof. exact (conj (@lem2265369 x n h1) (@lem2264909 x n h1)). Qed.
Lemma lem2265372 (x : real) (y : real) : term567 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem2265373 (x : real) : term568 x.
Proof. exact (@lem2265372 (term554 x) (term569 x)). Qed.
Lemma lem2265374 (x : real) (n : nat) (h1 : term325 x n) : term570 x.
Proof. exact (@lem2265373 x (@lem2265370 x n h1)). Qed.
Lemma lem2265375 (x : real) : (term571 x) = (term572 x).
Proof. exact (@lem1982711 term537 term510 x). Qed.
Lemma lem2265377 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265378 : term510 = term511.
Proof. exact (@lem2265377 term512). Qed.
Lemma lem2265380 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2265381 : term537 = term552.
Proof. exact (@lem2265380 term512). Qed.
Lemma lem2265382 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265383 : term573 = term574.
Proof. exact (MK_COMB (@lem2265382) (@lem2265381)). Qed.
Lemma lem2265384 : term575 = term576.
Proof. exact (MK_COMB (@lem2265383) (@lem2265378)). Qed.
Lemma lem2265385 : term577.
Proof. exact (@lem1981473 term537 term38 term510 term38 term14 term38). Qed.
Lemma lem2265387 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265388 : term377 = term383.
Proof. exact (@lem2265387 (NUMERAL 0) term32). Qed.
Lemma lem2265389 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265390 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265391 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265390 h1) (fun h1 : term383 = True => @lem2265389)). Qed.
Lemma lem2265392 : term383 = True.
Proof. exact (EQ_MP (@lem2265391) (@lem2265389)). Qed.
Lemma lem2265393 : term377 = True.
Proof. exact (TRANS (@lem2265388) (@lem2265392)). Qed.
Lemma lem2265394 : True = term377.
Proof. exact (SYM (@lem2265393)). Qed.
Lemma lem2265395 : term377.
Proof. exact (EQ_MP (@lem2265394) (@lem0)). Qed.
Lemma lem2265396 : term578.
Proof. exact (@lem2265385 (@lem2265395)). Qed.
Lemma lem2265398 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265399 : term377 = term383.
Proof. exact (@lem2265398 (NUMERAL 0) term32). Qed.
Lemma lem2265400 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265401 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265402 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265401 h1) (fun h1 : term383 = True => @lem2265400)). Qed.
Lemma lem2265403 : term383 = True.
Proof. exact (EQ_MP (@lem2265402) (@lem2265400)). Qed.
Lemma lem2265404 : term377 = True.
Proof. exact (TRANS (@lem2265399) (@lem2265403)). Qed.
Lemma lem2265405 : True = term377.
Proof. exact (SYM (@lem2265404)). Qed.
Lemma lem2265406 : term377.
Proof. exact (EQ_MP (@lem2265405) (@lem0)). Qed.
Lemma lem2265407 : term579.
Proof. exact (@lem2265396 (@lem2265406)). Qed.
Lemma lem2265409 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265410 : term377 = term383.
Proof. exact (@lem2265409 (NUMERAL 0) term32). Qed.
Lemma lem2265411 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265412 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265413 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265412 h1) (fun h1 : term383 = True => @lem2265411)). Qed.
Lemma lem2265414 : term383 = True.
Proof. exact (EQ_MP (@lem2265413) (@lem2265411)). Qed.
Lemma lem2265415 : term377 = True.
Proof. exact (TRANS (@lem2265410) (@lem2265414)). Qed.
Lemma lem2265416 : True = term377.
Proof. exact (SYM (@lem2265415)). Qed.
Lemma lem2265417 : term377.
Proof. exact (EQ_MP (@lem2265416) (@lem0)). Qed.
Lemma lem2265418 : term580.
Proof. exact (@lem2265407 (@lem2265417)). Qed.
Lemma lem2265420 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265421 : term517 = term518.
Proof. exact (@lem2265420 term512 term32). Qed.
Lemma lem2265422 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2265423 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2265424 : term521 = term512.
Proof. exact (EQ_MP (@lem2265423) (@lem2265422)). Qed.
Lemma lem2265425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265426 : term518 = term510.
Proof. exact (MK_COMB (@lem2265425) (@lem2265424)). Qed.
Lemma lem2265427 : term517 = term510.
Proof. exact (TRANS (@lem2265421) (@lem2265426)). Qed.
Lemma lem2265429 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2265430 : term549 = term550.
Proof. exact (@lem2265429 term512 term32). Qed.
Lemma lem2265431 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2265432 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2265433 : term521 = term512.
Proof. exact (EQ_MP (@lem2265432) (@lem2265431)). Qed.
Lemma lem2265434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265435 : term518 = term510.
Proof. exact (MK_COMB (@lem2265434) (@lem2265433)). Qed.
Lemma lem2265436 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265437 : term550 = term537.
Proof. exact (MK_COMB (@lem2265436) (@lem2265435)). Qed.
Lemma lem2265438 : term549 = term537.
Proof. exact (TRANS (@lem2265430) (@lem2265437)). Qed.
Lemma lem2265439 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265440 : term581 = term573.
Proof. exact (MK_COMB (@lem2265439) (@lem2265438)). Qed.
Lemma lem2265441 : term582 = term575.
Proof. exact (MK_COMB (@lem2265440) (@lem2265427)). Qed.
Lemma lem2265443 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2265444 : term575 = term14.
Proof. exact (@lem2265443 term512). Qed.
Lemma lem2265445 : term582 = term14.
Proof. exact (TRANS (@lem2265441) (@lem2265444)). Qed.
Lemma lem2265446 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265447 : term583 = term426.
Proof. exact (MK_COMB (@lem2265446) (@lem2265445)). Qed.
Lemma lem2265448 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2265449 : term584 = term388.
Proof. exact (MK_COMB (@lem2265447) (@lem2265448)). Qed.
Lemma lem2265451 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265452 : term388 = term14.
Proof. exact (@lem2265451 term32). Qed.
Lemma lem2265453 : term584 = term14.
Proof. exact (TRANS (@lem2265449) (@lem2265452)). Qed.
Lemma lem2265455 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265456 : term41 = term42.
Proof. exact (@lem2265455 term32 term32). Qed.
Lemma lem2265457 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265458 : term44 = term32.
Proof. exact (EQ_MP (@lem2265457) (@lem940073)). Qed.
Lemma lem2265459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265460 : term42 = term38.
Proof. exact (MK_COMB (@lem2265459) (@lem2265458)). Qed.
Lemma lem2265461 : term41 = term38.
Proof. exact (TRANS (@lem2265456) (@lem2265460)). Qed.
Lemma lem2265462 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2265463 : term428 = term388.
Proof. exact (MK_COMB (@lem2265462) (@lem2265461)). Qed.
Lemma lem2265465 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265466 : term388 = term14.
Proof. exact (@lem2265465 term32). Qed.
Lemma lem2265467 : term428 = term14.
Proof. exact (TRANS (@lem2265463) (@lem2265466)). Qed.
Lemma lem2265468 : term14 = term428.
Proof. exact (SYM (@lem2265467)). Qed.
Lemma lem2265469 : term584 = term428.
Proof. exact (TRANS (@lem2265453) (@lem2265468)). Qed.
Lemma lem2265470 : term576 = term180.
Proof. exact (@lem2265418 (@lem2265469)). Qed.
Lemma lem2265471 : term575 = term180.
Proof. exact (TRANS (@lem2265384) (@lem2265470)). Qed.
Lemma lem2265473 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2265474 : term180 = term14.
Proof. exact (@lem2265473 term14). Qed.
Lemma lem2265475 : term575 = term14.
Proof. exact (TRANS (@lem2265471) (@lem2265474)). Qed.
Lemma lem2265476 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265477 : term585 = term426.
Proof. exact (MK_COMB (@lem2265476) (@lem2265475)). Qed.
Lemma lem2265478 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2265479 (x : real) : (term572 x) = (term430 x).
Proof. exact (MK_COMB (@lem2265477) (@lem2265478 x)). Qed.
Lemma lem2265480 (x : real) : (term571 x) = (term430 x).
Proof. exact (TRANS (@lem2265375 x) (@lem2265479 x)). Qed.
Lemma lem2265481 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2265482 (x : real) : (term571 x) = term14.
Proof. exact (TRANS (@lem2265480 x) (@lem2265481 x)). Qed.
Lemma lem2265483 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2265484 (x : real) : (term586 x) = term437.
Proof. exact (MK_COMB (@lem2265483) (@lem2265482 x)). Qed.
Lemma lem2265485 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2265486 (x : real) : (term570 x) = term438.
Proof. exact (MK_COMB (@lem2265484 x) (@lem2265485)). Qed.
Lemma lem2265487 (x : real) (n : nat) (h1 : term325 x n) : term438.
Proof. exact (EQ_MP (@lem2265486 x) (@lem2265374 x n h1)). Qed.
Lemma lem2265489 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2265490 : term438 = term439.
Proof. exact (@lem2265489 term14 term14). Qed.
Lemma lem2265492 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265493 : term14 = term180.
Proof. exact (@lem2265492 (NUMERAL 0)). Qed.
Lemma lem2265495 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265496 : term14 = term180.
Proof. exact (@lem2265495 (NUMERAL 0)). Qed.
Lemma lem2265497 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265498 : term378 = term379.
Proof. exact (MK_COMB (@lem2265497) (@lem2265496)). Qed.
Lemma lem2265499 : term439 = term440.
Proof. exact (MK_COMB (@lem2265498) (@lem2265493)). Qed.
Lemma lem2265500 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2265502 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265503 : term377 = term383.
Proof. exact (@lem2265502 (NUMERAL 0) term32). Qed.
Lemma lem2265504 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265505 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265506 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265505 h1) (fun h1 : term383 = True => @lem2265504)). Qed.
Lemma lem2265507 : term383 = True.
Proof. exact (EQ_MP (@lem2265506) (@lem2265504)). Qed.
Lemma lem2265508 : term377 = True.
Proof. exact (TRANS (@lem2265503) (@lem2265507)). Qed.
Lemma lem2265509 : True = term377.
Proof. exact (SYM (@lem2265508)). Qed.
Lemma lem2265510 : term377.
Proof. exact (EQ_MP (@lem2265509) (@lem0)). Qed.
Lemma lem2265511 : term442.
Proof. exact (@lem2265500 (@lem2265510)). Qed.
Lemma lem2265513 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265514 : term377 = term383.
Proof. exact (@lem2265513 (NUMERAL 0) term32). Qed.
Lemma lem2265515 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265516 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265517 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265516 h1) (fun h1 : term383 = True => @lem2265515)). Qed.
Lemma lem2265518 : term383 = True.
Proof. exact (EQ_MP (@lem2265517) (@lem2265515)). Qed.
Lemma lem2265519 : term377 = True.
Proof. exact (TRANS (@lem2265514) (@lem2265518)). Qed.
Lemma lem2265520 : True = term377.
Proof. exact (SYM (@lem2265519)). Qed.
Lemma lem2265521 : term377.
Proof. exact (EQ_MP (@lem2265520) (@lem0)). Qed.
Lemma lem2265522 : term440 = term443.
Proof. exact (@lem2265511 (@lem2265521)). Qed.
Lemma lem2265524 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265525 : term388 = term14.
Proof. exact (@lem2265524 term32). Qed.
Lemma lem2265527 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265528 : term388 = term14.
Proof. exact (@lem2265527 term32). Qed.
Lemma lem2265529 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265530 : term389 = term378.
Proof. exact (MK_COMB (@lem2265529) (@lem2265528)). Qed.
Lemma lem2265531 : term443 = term439.
Proof. exact (MK_COMB (@lem2265530) (@lem2265525)). Qed.
Lemma lem2265533 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265534 : term439 = term444.
Proof. exact (@lem2265533 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2265535 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2265536 : term439 = False.
Proof. exact (TRANS (@lem2265534) (@lem2265535)). Qed.
Lemma lem2265537 : term443 = False.
Proof. exact (TRANS (@lem2265531) (@lem2265536)). Qed.
Lemma lem2265538 : term440 = False.
Proof. exact (TRANS (@lem2265522) (@lem2265537)). Qed.
Lemma lem2265539 : term439 = False.
Proof. exact (TRANS (@lem2265499) (@lem2265538)). Qed.
Lemma lem2265540 : term438 = False.
Proof. exact (TRANS (@lem2265490) (@lem2265539)). Qed.
Lemma lem2265541 (x : real) (n : nat) (h1 : term325 x n) : False.
Proof. exact (EQ_MP (@lem2265540) (@lem2265487 x n h1)). Qed.
Lemma lem2265542 (x : real) (n : nat) (h1 : term326 x n) : False.
Proof. exact (or_elim (@lem2264195 x n h1) (fun h0 : term314 x n => @lem2264619 x n h0) (fun h0 : term325 x n => @lem2265541 x n h0)). Qed.
Lemma lem2265543 (x : real) (n : nat) (h1 : term343 x n) : term343 x n.
Proof. exact (h1). Qed.
Lemma lem2265544 (x : real) (n : nat) (h1 : term343 x n) : (term21 x n) = term14.
Proof. exact (proj2 (@lem2265543 x n h1)). Qed.
Lemma lem2265545 (x : real) (n : nat) (h1 : term343 x n) : term151 x n.
Proof. exact (proj1 (@lem2265543 x n h1)). Qed.
Lemma lem2265547 (x : real) (n : nat) (h1 : term343 x n) : term59 x n.
Proof. exact (proj1 (@lem2265545 x n h1)). Qed.
Lemma lem2265550 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2265551 : term376 = term377.
Proof. exact (@lem2265550 term14 term38). Qed.
Lemma lem2265553 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265554 : term38 = term48.
Proof. exact (@lem2265553 term32). Qed.
Lemma lem2265556 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265557 : term14 = term180.
Proof. exact (@lem2265556 (NUMERAL 0)). Qed.
Lemma lem2265558 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265559 : term378 = term379.
Proof. exact (MK_COMB (@lem2265558) (@lem2265557)). Qed.
Lemma lem2265560 : term377 = term380.
Proof. exact (MK_COMB (@lem2265559) (@lem2265554)). Qed.
Lemma lem2265561 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2265563 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265564 : term377 = term383.
Proof. exact (@lem2265563 (NUMERAL 0) term32). Qed.
Lemma lem2265565 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265566 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265567 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265566 h1) (fun h1 : term383 = True => @lem2265565)). Qed.
Lemma lem2265568 : term383 = True.
Proof. exact (EQ_MP (@lem2265567) (@lem2265565)). Qed.
Lemma lem2265569 : term377 = True.
Proof. exact (TRANS (@lem2265564) (@lem2265568)). Qed.
Lemma lem2265570 : True = term377.
Proof. exact (SYM (@lem2265569)). Qed.
Lemma lem2265571 : term377.
Proof. exact (EQ_MP (@lem2265570) (@lem0)). Qed.
Lemma lem2265572 : term385.
Proof. exact (@lem2265561 (@lem2265571)). Qed.
Lemma lem2265574 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265575 : term377 = term383.
Proof. exact (@lem2265574 (NUMERAL 0) term32). Qed.
Lemma lem2265576 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265577 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265578 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265577 h1) (fun h1 : term383 = True => @lem2265576)). Qed.
Lemma lem2265579 : term383 = True.
Proof. exact (EQ_MP (@lem2265578) (@lem2265576)). Qed.
Lemma lem2265580 : term377 = True.
Proof. exact (TRANS (@lem2265575) (@lem2265579)). Qed.
Lemma lem2265581 : True = term377.
Proof. exact (SYM (@lem2265580)). Qed.
Lemma lem2265582 : term377.
Proof. exact (EQ_MP (@lem2265581) (@lem0)). Qed.
Lemma lem2265583 : term380 = term386.
Proof. exact (@lem2265572 (@lem2265582)). Qed.
Lemma lem2265585 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265586 : term41 = term42.
Proof. exact (@lem2265585 term32 term32). Qed.
Lemma lem2265587 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265588 : term44 = term32.
Proof. exact (EQ_MP (@lem2265587) (@lem940073)). Qed.
Lemma lem2265589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265590 : term42 = term38.
Proof. exact (MK_COMB (@lem2265589) (@lem2265588)). Qed.
Lemma lem2265591 : term41 = term38.
Proof. exact (TRANS (@lem2265586) (@lem2265590)). Qed.
Lemma lem2265593 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265594 : term388 = term14.
Proof. exact (@lem2265593 term32). Qed.
Lemma lem2265595 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265596 : term389 = term378.
Proof. exact (MK_COMB (@lem2265595) (@lem2265594)). Qed.
Lemma lem2265597 : term386 = term377.
Proof. exact (MK_COMB (@lem2265596) (@lem2265591)). Qed.
Lemma lem2265599 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265600 : term377 = term383.
Proof. exact (@lem2265599 (NUMERAL 0) term32). Qed.
Lemma lem2265601 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265602 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265603 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265602 h1) (fun h1 : term383 = True => @lem2265601)). Qed.
Lemma lem2265604 : term383 = True.
Proof. exact (EQ_MP (@lem2265603) (@lem2265601)). Qed.
Lemma lem2265605 : term377 = True.
Proof. exact (TRANS (@lem2265600) (@lem2265604)). Qed.
Lemma lem2265606 : term386 = True.
Proof. exact (TRANS (@lem2265597) (@lem2265605)). Qed.
Lemma lem2265607 : term380 = True.
Proof. exact (TRANS (@lem2265583) (@lem2265606)). Qed.
Lemma lem2265608 : term377 = True.
Proof. exact (TRANS (@lem2265560) (@lem2265607)). Qed.
Lemma lem2265609 : term376 = True.
Proof. exact (TRANS (@lem2265551) (@lem2265608)). Qed.
Lemma lem2265610 : True = term376.
Proof. exact (SYM (@lem2265609)). Qed.
Lemma lem2265611 : term376.
Proof. exact (EQ_MP (@lem2265610) (@lem0)). Qed.
Lemma lem2265612 (x : real) (n : nat) (h1 : term343 x n) : term462 x n.
Proof. exact (conj (@lem2265611) (@lem2265547 x n h1)). Qed.
Lemma lem2265614 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2265615 (x : real) (n : nat) : term463 x n.
Proof. exact (@lem2265614 term38 (term54 x n)). Qed.
Lemma lem2265616 (x : real) (n : nat) (h1 : term343 x n) : term464 x n.
Proof. exact (@lem2265615 x n (@lem2265612 x n h1)). Qed.
Lemma lem2265617 (x : real) (n : nat) : (term465 x n) = (term54 x n).
Proof. exact (@lem1982733 (term54 x n)). Qed.
Lemma lem2265618 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2265619 (x : real) (n : nat) : (term466 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem2265618) (@lem2265617 x n)). Qed.
Lemma lem2265620 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2265621 (x : real) (n : nat) : (term464 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem2265619 x n) (@lem2265620)). Qed.
Lemma lem2265622 (x : real) (n : nat) (h1 : term343 x n) : term59 x n.
Proof. exact (EQ_MP (@lem2265621 x n) (@lem2265616 x n h1)). Qed.
Lemma lem2265624 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2265625 (x : real) (n : nat) : term397 x n.
Proof. exact (@lem2265624 (term21 x n)). Qed.
Lemma lem2265626 (x : real) (n : nat) (h1 : term343 x n) : term398 x n.
Proof. exact (@lem2265625 x n (@lem2265544 x n h1)). Qed.
Lemma lem2265627 (x : real) (n : nat) (h1 : term343 x n) : term467 x n.
Proof. exact (@lem2265626 x n h1 term38). Qed.
Lemma lem2265628 (x : real) (n : nat) : (term467 x n) = ((term394 x n) = term14).
Proof. exact (eq_refl (term467 x n)). Qed.
Lemma lem2265629 (x : real) (n : nat) (h1 : term343 x n) : (term394 x n) = term14.
Proof. exact (EQ_MP (@lem2265628 x n) (@lem2265627 x n h1)). Qed.
Lemma lem2265630 (x : real) (n : nat) : (term394 x n) = (term21 x n).
Proof. exact (@lem1982733 (term21 x n)). Qed.
Lemma lem2265631 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2265632 (x : real) (n : nat) : (term468 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2265631) (@lem2265630 x n)). Qed.
Lemma lem2265633 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2265634 (x : real) (n : nat) : ((term394 x n) = term14) = ((term21 x n) = term14).
Proof. exact (MK_COMB (@lem2265632 x n) (@lem2265633)). Qed.
Lemma lem2265635 (x : real) (n : nat) (h1 : term343 x n) : (term21 x n) = term14.
Proof. exact (EQ_MP (@lem2265634 x n) (@lem2265629 x n h1)). Qed.
Lemma lem2265636 (x : real) (n : nat) (h1 : term343 x n) : term469 x n.
Proof. exact (conj (@lem2265635 x n h1) (@lem2265622 x n h1)). Qed.
Lemma lem2265638 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2265639 (x : real) (n : nat) : term470 x n.
Proof. exact (@lem2265638 (term21 x n) (term54 x n)). Qed.
Lemma lem2265640 (x : real) (n : nat) (h1 : term343 x n) : term471 x n.
Proof. exact (@lem2265639 x n (@lem2265636 x n h1)). Qed.
Lemma lem2265641 (x : real) (n : nat) : (term472 x n) = (term473 x n).
Proof. exact (@lem1982753 x (term208 x) (term27 n) (real_of_num n)). Qed.
Lemma lem2265642 (x : real) : (term474 x) = (term409 x).
Proof. exact (@lem1982715 term26 x). Qed.
Lemma lem2265644 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265645 : term38 = term48.
Proof. exact (@lem2265644 term32). Qed.
Lemma lem2265647 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2265648 : term26 = term31.
Proof. exact (@lem2265647 term32). Qed.
Lemma lem2265649 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265650 : term410 = term411.
Proof. exact (MK_COMB (@lem2265649) (@lem2265648)). Qed.
Lemma lem2265651 : term412 = term413.
Proof. exact (MK_COMB (@lem2265650) (@lem2265645)). Qed.
Lemma lem2265652 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2265654 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265655 : term377 = term383.
Proof. exact (@lem2265654 (NUMERAL 0) term32). Qed.
Lemma lem2265656 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265657 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265658 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265657 h1) (fun h1 : term383 = True => @lem2265656)). Qed.
Lemma lem2265659 : term383 = True.
Proof. exact (EQ_MP (@lem2265658) (@lem2265656)). Qed.
Lemma lem2265660 : term377 = True.
Proof. exact (TRANS (@lem2265655) (@lem2265659)). Qed.
Lemma lem2265661 : True = term377.
Proof. exact (SYM (@lem2265660)). Qed.
Lemma lem2265662 : term377.
Proof. exact (EQ_MP (@lem2265661) (@lem0)). Qed.
Lemma lem2265663 : term415.
Proof. exact (@lem2265652 (@lem2265662)). Qed.
Lemma lem2265665 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265666 : term377 = term383.
Proof. exact (@lem2265665 (NUMERAL 0) term32). Qed.
Lemma lem2265667 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265668 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265669 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265668 h1) (fun h1 : term383 = True => @lem2265667)). Qed.
Lemma lem2265670 : term383 = True.
Proof. exact (EQ_MP (@lem2265669) (@lem2265667)). Qed.
Lemma lem2265671 : term377 = True.
Proof. exact (TRANS (@lem2265666) (@lem2265670)). Qed.
Lemma lem2265672 : True = term377.
Proof. exact (SYM (@lem2265671)). Qed.
Lemma lem2265673 : term377.
Proof. exact (EQ_MP (@lem2265672) (@lem0)). Qed.
Lemma lem2265674 : term416.
Proof. exact (@lem2265663 (@lem2265673)). Qed.
Lemma lem2265676 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265677 : term377 = term383.
Proof. exact (@lem2265676 (NUMERAL 0) term32). Qed.
Lemma lem2265678 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265679 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265680 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265679 h1) (fun h1 : term383 = True => @lem2265678)). Qed.
Lemma lem2265681 : term383 = True.
Proof. exact (EQ_MP (@lem2265680) (@lem2265678)). Qed.
Lemma lem2265682 : term377 = True.
Proof. exact (TRANS (@lem2265677) (@lem2265681)). Qed.
Lemma lem2265683 : True = term377.
Proof. exact (SYM (@lem2265682)). Qed.
Lemma lem2265684 : term377.
Proof. exact (EQ_MP (@lem2265683) (@lem0)). Qed.
Lemma lem2265685 : term417.
Proof. exact (@lem2265674 (@lem2265684)). Qed.
Lemma lem2265687 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265688 : term41 = term42.
Proof. exact (@lem2265687 term32 term32). Qed.
Lemma lem2265689 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265690 : term44 = term32.
Proof. exact (EQ_MP (@lem2265689) (@lem940073)). Qed.
Lemma lem2265691 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265692 : term42 = term38.
Proof. exact (MK_COMB (@lem2265691) (@lem2265690)). Qed.
Lemma lem2265693 : term41 = term38.
Proof. exact (TRANS (@lem2265688) (@lem2265692)). Qed.
Lemma lem2265695 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2265696 : term420 = term421.
Proof. exact (@lem2265695 term32 term32). Qed.
Lemma lem2265697 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265698 : term44 = term32.
Proof. exact (EQ_MP (@lem2265697) (@lem940073)). Qed.
Lemma lem2265699 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265700 : term42 = term38.
Proof. exact (MK_COMB (@lem2265699) (@lem2265698)). Qed.
Lemma lem2265701 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265702 : term421 = term26.
Proof. exact (MK_COMB (@lem2265701) (@lem2265700)). Qed.
Lemma lem2265703 : term420 = term26.
Proof. exact (TRANS (@lem2265696) (@lem2265702)). Qed.
Lemma lem2265704 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265705 : term422 = term410.
Proof. exact (MK_COMB (@lem2265704) (@lem2265703)). Qed.
Lemma lem2265706 : term423 = term412.
Proof. exact (MK_COMB (@lem2265705) (@lem2265693)). Qed.
Lemma lem2265708 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2265709 : term412 = term14.
Proof. exact (@lem2265708 term32). Qed.
Lemma lem2265710 : term423 = term14.
Proof. exact (TRANS (@lem2265706) (@lem2265709)). Qed.
Lemma lem2265711 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265712 : term425 = term426.
Proof. exact (MK_COMB (@lem2265711) (@lem2265710)). Qed.
Lemma lem2265713 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2265714 : term427 = term388.
Proof. exact (MK_COMB (@lem2265712) (@lem2265713)). Qed.
Lemma lem2265716 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265717 : term388 = term14.
Proof. exact (@lem2265716 term32). Qed.
Lemma lem2265718 : term427 = term14.
Proof. exact (TRANS (@lem2265714) (@lem2265717)). Qed.
Lemma lem2265720 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265721 : term41 = term42.
Proof. exact (@lem2265720 term32 term32). Qed.
Lemma lem2265722 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265723 : term44 = term32.
Proof. exact (EQ_MP (@lem2265722) (@lem940073)). Qed.
Lemma lem2265724 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265725 : term42 = term38.
Proof. exact (MK_COMB (@lem2265724) (@lem2265723)). Qed.
Lemma lem2265726 : term41 = term38.
Proof. exact (TRANS (@lem2265721) (@lem2265725)). Qed.
Lemma lem2265727 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2265728 : term428 = term388.
Proof. exact (MK_COMB (@lem2265727) (@lem2265726)). Qed.
Lemma lem2265730 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265731 : term388 = term14.
Proof. exact (@lem2265730 term32). Qed.
Lemma lem2265732 : term428 = term14.
Proof. exact (TRANS (@lem2265728) (@lem2265731)). Qed.
Lemma lem2265733 : term14 = term428.
Proof. exact (SYM (@lem2265732)). Qed.
Lemma lem2265734 : term427 = term428.
Proof. exact (TRANS (@lem2265718) (@lem2265733)). Qed.
Lemma lem2265735 : term413 = term180.
Proof. exact (@lem2265685 (@lem2265734)). Qed.
Lemma lem2265736 : term412 = term180.
Proof. exact (TRANS (@lem2265651) (@lem2265735)). Qed.
Lemma lem2265738 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2265739 : term180 = term14.
Proof. exact (@lem2265738 term14). Qed.
Lemma lem2265740 : term412 = term14.
Proof. exact (TRANS (@lem2265736) (@lem2265739)). Qed.
Lemma lem2265741 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265742 : term429 = term426.
Proof. exact (MK_COMB (@lem2265741) (@lem2265740)). Qed.
Lemma lem2265743 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2265744 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2265742) (@lem2265743 x)). Qed.
Lemma lem2265745 (x : real) : (term474 x) = (term430 x).
Proof. exact (TRANS (@lem2265642 x) (@lem2265744 x)). Qed.
Lemma lem2265746 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2265747 (x : real) : (term474 x) = term14.
Proof. exact (TRANS (@lem2265745 x) (@lem2265746 x)). Qed.
Lemma lem2265748 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265749 (x : real) : (term475 x) = term432.
Proof. exact (MK_COMB (@lem2265748) (@lem2265747 x)). Qed.
Lemma lem2265750 (n : nat) : (term460 n) = (term434 n).
Proof. exact (@lem1982713 term26 (real_of_num n)). Qed.
Lemma lem2265752 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265753 : term38 = term48.
Proof. exact (@lem2265752 term32). Qed.
Lemma lem2265755 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2265756 : term26 = term31.
Proof. exact (@lem2265755 term32). Qed.
Lemma lem2265757 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265758 : term410 = term411.
Proof. exact (MK_COMB (@lem2265757) (@lem2265756)). Qed.
Lemma lem2265759 : term412 = term413.
Proof. exact (MK_COMB (@lem2265758) (@lem2265753)). Qed.
Lemma lem2265760 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2265762 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265763 : term377 = term383.
Proof. exact (@lem2265762 (NUMERAL 0) term32). Qed.
Lemma lem2265764 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265765 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265766 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265765 h1) (fun h1 : term383 = True => @lem2265764)). Qed.
Lemma lem2265767 : term383 = True.
Proof. exact (EQ_MP (@lem2265766) (@lem2265764)). Qed.
Lemma lem2265768 : term377 = True.
Proof. exact (TRANS (@lem2265763) (@lem2265767)). Qed.
Lemma lem2265769 : True = term377.
Proof. exact (SYM (@lem2265768)). Qed.
Lemma lem2265770 : term377.
Proof. exact (EQ_MP (@lem2265769) (@lem0)). Qed.
Lemma lem2265771 : term415.
Proof. exact (@lem2265760 (@lem2265770)). Qed.
Lemma lem2265773 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265774 : term377 = term383.
Proof. exact (@lem2265773 (NUMERAL 0) term32). Qed.
Lemma lem2265775 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265776 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265777 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265776 h1) (fun h1 : term383 = True => @lem2265775)). Qed.
Lemma lem2265778 : term383 = True.
Proof. exact (EQ_MP (@lem2265777) (@lem2265775)). Qed.
Lemma lem2265779 : term377 = True.
Proof. exact (TRANS (@lem2265774) (@lem2265778)). Qed.
Lemma lem2265780 : True = term377.
Proof. exact (SYM (@lem2265779)). Qed.
Lemma lem2265781 : term377.
Proof. exact (EQ_MP (@lem2265780) (@lem0)). Qed.
Lemma lem2265782 : term416.
Proof. exact (@lem2265771 (@lem2265781)). Qed.
Lemma lem2265784 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265785 : term377 = term383.
Proof. exact (@lem2265784 (NUMERAL 0) term32). Qed.
Lemma lem2265786 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265787 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265788 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265787 h1) (fun h1 : term383 = True => @lem2265786)). Qed.
Lemma lem2265789 : term383 = True.
Proof. exact (EQ_MP (@lem2265788) (@lem2265786)). Qed.
Lemma lem2265790 : term377 = True.
Proof. exact (TRANS (@lem2265785) (@lem2265789)). Qed.
Lemma lem2265791 : True = term377.
Proof. exact (SYM (@lem2265790)). Qed.
Lemma lem2265792 : term377.
Proof. exact (EQ_MP (@lem2265791) (@lem0)). Qed.
Lemma lem2265793 : term417.
Proof. exact (@lem2265782 (@lem2265792)). Qed.
Lemma lem2265795 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265796 : term41 = term42.
Proof. exact (@lem2265795 term32 term32). Qed.
Lemma lem2265797 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265798 : term44 = term32.
Proof. exact (EQ_MP (@lem2265797) (@lem940073)). Qed.
Lemma lem2265799 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265800 : term42 = term38.
Proof. exact (MK_COMB (@lem2265799) (@lem2265798)). Qed.
Lemma lem2265801 : term41 = term38.
Proof. exact (TRANS (@lem2265796) (@lem2265800)). Qed.
Lemma lem2265803 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2265804 : term420 = term421.
Proof. exact (@lem2265803 term32 term32). Qed.
Lemma lem2265805 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265806 : term44 = term32.
Proof. exact (EQ_MP (@lem2265805) (@lem940073)). Qed.
Lemma lem2265807 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265808 : term42 = term38.
Proof. exact (MK_COMB (@lem2265807) (@lem2265806)). Qed.
Lemma lem2265809 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2265810 : term421 = term26.
Proof. exact (MK_COMB (@lem2265809) (@lem2265808)). Qed.
Lemma lem2265811 : term420 = term26.
Proof. exact (TRANS (@lem2265804) (@lem2265810)). Qed.
Lemma lem2265812 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2265813 : term422 = term410.
Proof. exact (MK_COMB (@lem2265812) (@lem2265811)). Qed.
Lemma lem2265814 : term423 = term412.
Proof. exact (MK_COMB (@lem2265813) (@lem2265801)). Qed.
Lemma lem2265816 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2265817 : term412 = term14.
Proof. exact (@lem2265816 term32). Qed.
Lemma lem2265818 : term423 = term14.
Proof. exact (TRANS (@lem2265814) (@lem2265817)). Qed.
Lemma lem2265819 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265820 : term425 = term426.
Proof. exact (MK_COMB (@lem2265819) (@lem2265818)). Qed.
Lemma lem2265821 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2265822 : term427 = term388.
Proof. exact (MK_COMB (@lem2265820) (@lem2265821)). Qed.
Lemma lem2265824 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265825 : term388 = term14.
Proof. exact (@lem2265824 term32). Qed.
Lemma lem2265826 : term427 = term14.
Proof. exact (TRANS (@lem2265822) (@lem2265825)). Qed.
Lemma lem2265828 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265829 : term41 = term42.
Proof. exact (@lem2265828 term32 term32). Qed.
Lemma lem2265830 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265831 : term44 = term32.
Proof. exact (EQ_MP (@lem2265830) (@lem940073)). Qed.
Lemma lem2265832 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265833 : term42 = term38.
Proof. exact (MK_COMB (@lem2265832) (@lem2265831)). Qed.
Lemma lem2265834 : term41 = term38.
Proof. exact (TRANS (@lem2265829) (@lem2265833)). Qed.
Lemma lem2265835 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2265836 : term428 = term388.
Proof. exact (MK_COMB (@lem2265835) (@lem2265834)). Qed.
Lemma lem2265838 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265839 : term388 = term14.
Proof. exact (@lem2265838 term32). Qed.
Lemma lem2265840 : term428 = term14.
Proof. exact (TRANS (@lem2265836) (@lem2265839)). Qed.
Lemma lem2265841 : term14 = term428.
Proof. exact (SYM (@lem2265840)). Qed.
Lemma lem2265842 : term427 = term428.
Proof. exact (TRANS (@lem2265826) (@lem2265841)). Qed.
Lemma lem2265843 : term413 = term180.
Proof. exact (@lem2265793 (@lem2265842)). Qed.
Lemma lem2265844 : term412 = term180.
Proof. exact (TRANS (@lem2265759) (@lem2265843)). Qed.
Lemma lem2265846 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2265847 : term180 = term14.
Proof. exact (@lem2265846 term14). Qed.
Lemma lem2265848 : term412 = term14.
Proof. exact (TRANS (@lem2265844) (@lem2265847)). Qed.
Lemma lem2265849 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2265850 : term429 = term426.
Proof. exact (MK_COMB (@lem2265849) (@lem2265848)). Qed.
Lemma lem2265851 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2265852 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2265850) (@lem2265851 n)). Qed.
Lemma lem2265853 (n : nat) : (term460 n) = (term387 n).
Proof. exact (TRANS (@lem2265750 n) (@lem2265852 n)). Qed.
Lemma lem2265854 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2265855 (n : nat) : (term460 n) = term14.
Proof. exact (TRANS (@lem2265853 n) (@lem2265854 n)). Qed.
Lemma lem2265856 (x : real) (n : nat) : (term473 x n) = term435.
Proof. exact (MK_COMB (@lem2265749 x) (@lem2265855 n)). Qed.
Lemma lem2265857 (x : real) (n : nat) : (term472 x n) = term435.
Proof. exact (TRANS (@lem2265641 x n) (@lem2265856 x n)). Qed.
Lemma lem2265858 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2265859 (x : real) (n : nat) : (term472 x n) = term14.
Proof. exact (TRANS (@lem2265857 x n) (@lem2265858)). Qed.
Lemma lem2265860 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2265861 (x : real) (n : nat) : (term476 x n) = term437.
Proof. exact (MK_COMB (@lem2265860) (@lem2265859 x n)). Qed.
Lemma lem2265862 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2265863 (x : real) (n : nat) : (term471 x n) = term438.
Proof. exact (MK_COMB (@lem2265861 x n) (@lem2265862)). Qed.
Lemma lem2265864 (x : real) (n : nat) (h1 : term343 x n) : term438.
Proof. exact (EQ_MP (@lem2265863 x n) (@lem2265640 x n h1)). Qed.
Lemma lem2265866 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2265867 : term438 = term439.
Proof. exact (@lem2265866 term14 term14). Qed.
Lemma lem2265869 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265870 : term14 = term180.
Proof. exact (@lem2265869 (NUMERAL 0)). Qed.
Lemma lem2265872 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265873 : term14 = term180.
Proof. exact (@lem2265872 (NUMERAL 0)). Qed.
Lemma lem2265874 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265875 : term378 = term379.
Proof. exact (MK_COMB (@lem2265874) (@lem2265873)). Qed.
Lemma lem2265876 : term439 = term440.
Proof. exact (MK_COMB (@lem2265875) (@lem2265870)). Qed.
Lemma lem2265877 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2265879 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265880 : term377 = term383.
Proof. exact (@lem2265879 (NUMERAL 0) term32). Qed.
Lemma lem2265881 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265882 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265883 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265882 h1) (fun h1 : term383 = True => @lem2265881)). Qed.
Lemma lem2265884 : term383 = True.
Proof. exact (EQ_MP (@lem2265883) (@lem2265881)). Qed.
Lemma lem2265885 : term377 = True.
Proof. exact (TRANS (@lem2265880) (@lem2265884)). Qed.
Lemma lem2265886 : True = term377.
Proof. exact (SYM (@lem2265885)). Qed.
Lemma lem2265887 : term377.
Proof. exact (EQ_MP (@lem2265886) (@lem0)). Qed.
Lemma lem2265888 : term442.
Proof. exact (@lem2265877 (@lem2265887)). Qed.
Lemma lem2265890 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265891 : term377 = term383.
Proof. exact (@lem2265890 (NUMERAL 0) term32). Qed.
Lemma lem2265892 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265893 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265894 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265893 h1) (fun h1 : term383 = True => @lem2265892)). Qed.
Lemma lem2265895 : term383 = True.
Proof. exact (EQ_MP (@lem2265894) (@lem2265892)). Qed.
Lemma lem2265896 : term377 = True.
Proof. exact (TRANS (@lem2265891) (@lem2265895)). Qed.
Lemma lem2265897 : True = term377.
Proof. exact (SYM (@lem2265896)). Qed.
Lemma lem2265898 : term377.
Proof. exact (EQ_MP (@lem2265897) (@lem0)). Qed.
Lemma lem2265899 : term440 = term443.
Proof. exact (@lem2265888 (@lem2265898)). Qed.
Lemma lem2265901 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265902 : term388 = term14.
Proof. exact (@lem2265901 term32). Qed.
Lemma lem2265904 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265905 : term388 = term14.
Proof. exact (@lem2265904 term32). Qed.
Lemma lem2265906 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265907 : term389 = term378.
Proof. exact (MK_COMB (@lem2265906) (@lem2265905)). Qed.
Lemma lem2265908 : term443 = term439.
Proof. exact (MK_COMB (@lem2265907) (@lem2265902)). Qed.
Lemma lem2265910 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265911 : term439 = term444.
Proof. exact (@lem2265910 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2265912 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2265913 : term439 = False.
Proof. exact (TRANS (@lem2265911) (@lem2265912)). Qed.
Lemma lem2265914 : term443 = False.
Proof. exact (TRANS (@lem2265908) (@lem2265913)). Qed.
Lemma lem2265915 : term440 = False.
Proof. exact (TRANS (@lem2265899) (@lem2265914)). Qed.
Lemma lem2265916 : term439 = False.
Proof. exact (TRANS (@lem2265876) (@lem2265915)). Qed.
Lemma lem2265917 : term438 = False.
Proof. exact (TRANS (@lem2265867) (@lem2265916)). Qed.
Lemma lem2265918 (x : real) (n : nat) (h1 : term343 x n) : False.
Proof. exact (EQ_MP (@lem2265917) (@lem2265864 x n h1)). Qed.
Lemma lem2265919 (x : real) (n : nat) (h1 : term346 x n) : False.
Proof. exact (or_elim (@lem2264194 x n h1) (fun h0 : term326 x n => @lem2265542 x n h0) (fun h0 : term343 x n => @lem2265918 x n h0)). Qed.
Lemma lem2265920 (x : real) (n : nat) (h1 : term371 x n) : term371 x n.
Proof. exact (h1). Qed.
Lemma lem2265921 (x : real) (n : nat) (h1 : term366 x n) : term366 x n.
Proof. exact (h1). Qed.
Lemma lem2265922 (x : real) (n : nat) (h1 : term358 x n) : term358 x n.
Proof. exact (h1). Qed.
Lemma lem2265923 (x : real) (n : nat) (h1 : term358 x n) : term356 x n.
Proof. exact (proj2 (@lem2265922 x n h1)). Qed.
Lemma lem2265925 (x : real) (n : nat) (h1 : term358 x n) : (term72 x n) = term14.
Proof. exact (proj2 (@lem2265923 x n h1)). Qed.
Lemma lem2265926 (x : real) (n : nat) (h1 : term358 x n) : term63 x n.
Proof. exact (proj1 (@lem2265923 x n h1)). Qed.
Lemma lem2265927 (n : nat) : term494 n.
Proof. exact (@lem1396812 n). Qed.
Lemma lem2265929 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2265930 : term376 = term377.
Proof. exact (@lem2265929 term14 term38). Qed.
Lemma lem2265932 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265933 : term38 = term48.
Proof. exact (@lem2265932 term32). Qed.
Lemma lem2265935 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2265936 : term14 = term180.
Proof. exact (@lem2265935 (NUMERAL 0)). Qed.
Lemma lem2265937 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265938 : term378 = term379.
Proof. exact (MK_COMB (@lem2265937) (@lem2265936)). Qed.
Lemma lem2265939 : term377 = term380.
Proof. exact (MK_COMB (@lem2265938) (@lem2265933)). Qed.
Lemma lem2265940 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2265942 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265943 : term377 = term383.
Proof. exact (@lem2265942 (NUMERAL 0) term32). Qed.
Lemma lem2265944 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265945 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265946 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265945 h1) (fun h1 : term383 = True => @lem2265944)). Qed.
Lemma lem2265947 : term383 = True.
Proof. exact (EQ_MP (@lem2265946) (@lem2265944)). Qed.
Lemma lem2265948 : term377 = True.
Proof. exact (TRANS (@lem2265943) (@lem2265947)). Qed.
Lemma lem2265949 : True = term377.
Proof. exact (SYM (@lem2265948)). Qed.
Lemma lem2265950 : term377.
Proof. exact (EQ_MP (@lem2265949) (@lem0)). Qed.
Lemma lem2265951 : term385.
Proof. exact (@lem2265940 (@lem2265950)). Qed.
Lemma lem2265953 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265954 : term377 = term383.
Proof. exact (@lem2265953 (NUMERAL 0) term32). Qed.
Lemma lem2265955 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265956 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265957 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265956 h1) (fun h1 : term383 = True => @lem2265955)). Qed.
Lemma lem2265958 : term383 = True.
Proof. exact (EQ_MP (@lem2265957) (@lem2265955)). Qed.
Lemma lem2265959 : term377 = True.
Proof. exact (TRANS (@lem2265954) (@lem2265958)). Qed.
Lemma lem2265960 : True = term377.
Proof. exact (SYM (@lem2265959)). Qed.
Lemma lem2265961 : term377.
Proof. exact (EQ_MP (@lem2265960) (@lem0)). Qed.
Lemma lem2265962 : term380 = term386.
Proof. exact (@lem2265951 (@lem2265961)). Qed.
Lemma lem2265964 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2265965 : term41 = term42.
Proof. exact (@lem2265964 term32 term32). Qed.
Lemma lem2265966 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2265967 : term44 = term32.
Proof. exact (EQ_MP (@lem2265966) (@lem940073)). Qed.
Lemma lem2265968 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2265969 : term42 = term38.
Proof. exact (MK_COMB (@lem2265968) (@lem2265967)). Qed.
Lemma lem2265970 : term41 = term38.
Proof. exact (TRANS (@lem2265965) (@lem2265969)). Qed.
Lemma lem2265972 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2265973 : term388 = term14.
Proof. exact (@lem2265972 term32). Qed.
Lemma lem2265974 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2265975 : term389 = term378.
Proof. exact (MK_COMB (@lem2265974) (@lem2265973)). Qed.
Lemma lem2265976 : term386 = term377.
Proof. exact (MK_COMB (@lem2265975) (@lem2265970)). Qed.
Lemma lem2265978 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2265979 : term377 = term383.
Proof. exact (@lem2265978 (NUMERAL 0) term32). Qed.
Lemma lem2265980 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2265981 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2265982 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2265981 h1) (fun h1 : term383 = True => @lem2265980)). Qed.
Lemma lem2265983 : term383 = True.
Proof. exact (EQ_MP (@lem2265982) (@lem2265980)). Qed.
Lemma lem2265984 : term377 = True.
Proof. exact (TRANS (@lem2265979) (@lem2265983)). Qed.
Lemma lem2265985 : term386 = True.
Proof. exact (TRANS (@lem2265976) (@lem2265984)). Qed.
Lemma lem2265986 : term380 = True.
Proof. exact (TRANS (@lem2265962) (@lem2265985)). Qed.
Lemma lem2265987 : term377 = True.
Proof. exact (TRANS (@lem2265939) (@lem2265986)). Qed.
Lemma lem2265988 : term376 = True.
Proof. exact (TRANS (@lem2265930) (@lem2265987)). Qed.
Lemma lem2265989 : True = term376.
Proof. exact (SYM (@lem2265988)). Qed.
Lemma lem2265990 : term376.
Proof. exact (EQ_MP (@lem2265989) (@lem0)). Qed.
Lemma lem2265991 (n : nat) : term495 n.
Proof. exact (conj (@lem2265990) (@lem2265927 n)). Qed.
Lemma lem2265993 (x : real) (y : real) : term496 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2265994 (n : nat) : term497 n.
Proof. exact (@lem2265993 term38 (real_of_num n)). Qed.
Lemma lem2265995 (n : nat) : term498 n.
Proof. exact (@lem2265994 n (@lem2265991 n)). Qed.
Lemma lem2265996 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (@lem1982733 (real_of_num n)). Qed.
Lemma lem2265997 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2265998 (n : nat) : (term499 n) = (term500 n).
Proof. exact (MK_COMB (@lem2265997) (@lem2265996 n)). Qed.
Lemma lem2265999 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266000 (n : nat) : (term498 n) = (term494 n).
Proof. exact (MK_COMB (@lem2265998 n) (@lem2265999)). Qed.
Lemma lem2266001 (n : nat) : term494 n.
Proof. exact (EQ_MP (@lem2266000 n) (@lem2265995 n)). Qed.
Lemma lem2266003 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2266004 (x : real) (n : nat) : term587 x n.
Proof. exact (@lem2266003 (term72 x n)). Qed.
Lemma lem2266005 (x : real) (n : nat) (h1 : term358 x n) : term588 x n.
Proof. exact (@lem2266004 x n (@lem2265925 x n h1)). Qed.
Lemma lem2266006 (x : real) (n : nat) (h1 : term358 x n) : term589 x n.
Proof. exact (@lem2266005 x n h1 term26). Qed.
Lemma lem2266007 (x : real) (n : nat) : (term589 x n) = ((term75 x n) = term14).
Proof. exact (eq_refl (term589 x n)). Qed.
Lemma lem2266008 (x : real) (n : nat) (h1 : term358 x n) : (term75 x n) = term14.
Proof. exact (EQ_MP (@lem2266007 x n) (@lem2266006 x n h1)). Qed.
Lemma lem2266015 (x : real) (n : nat) : (term75 x n) = (term76 x n).
Proof. exact (@lem1982781 x term26 (real_of_num n)). Qed.
Lemma lem2266016 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2266017 (x : real) (n : nat) : (term590 x n) = (term222 x n).
Proof. exact (MK_COMB (@lem2266016) (@lem2266015 x n)). Qed.
Lemma lem2266018 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266019 (x : real) (n : nat) : ((term75 x n) = term14) = ((term76 x n) = term14).
Proof. exact (MK_COMB (@lem2266017 x n) (@lem2266018)). Qed.
Lemma lem2266020 (x : real) (n : nat) (h1 : term358 x n) : (term76 x n) = term14.
Proof. exact (EQ_MP (@lem2266019 x n) (@lem2266008 x n h1)). Qed.
Lemma lem2266021 (x : real) (n : nat) (h1 : term358 x n) : term591 x n.
Proof. exact (conj (@lem2266020 x n h1) (@lem2266001 n)). Qed.
Lemma lem2266023 (x : real) (y : real) : term502 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2266024 (x : real) (n : nat) : term592 x n.
Proof. exact (@lem2266023 (term76 x n) (real_of_num n)). Qed.
Lemma lem2266025 (x : real) (n : nat) (h1 : term358 x n) : term593 x n.
Proof. exact (@lem2266024 x n (@lem2266021 x n h1)). Qed.
Lemma lem2266026 (x : real) (n : nat) : (term594 x n) = (term595 x n).
Proof. exact (@lem1982755 (term208 x) (term27 n) (real_of_num n)). Qed.
Lemma lem2266027 (n : nat) : (term460 n) = (term434 n).
Proof. exact (@lem1982713 term26 (real_of_num n)). Qed.
Lemma lem2266029 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266030 : term38 = term48.
Proof. exact (@lem2266029 term32). Qed.
Lemma lem2266032 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2266033 : term26 = term31.
Proof. exact (@lem2266032 term32). Qed.
Lemma lem2266034 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266035 : term410 = term411.
Proof. exact (MK_COMB (@lem2266034) (@lem2266033)). Qed.
Lemma lem2266036 : term412 = term413.
Proof. exact (MK_COMB (@lem2266035) (@lem2266030)). Qed.
Lemma lem2266037 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2266039 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266040 : term377 = term383.
Proof. exact (@lem2266039 (NUMERAL 0) term32). Qed.
Lemma lem2266041 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266042 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266043 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266042 h1) (fun h1 : term383 = True => @lem2266041)). Qed.
Lemma lem2266044 : term383 = True.
Proof. exact (EQ_MP (@lem2266043) (@lem2266041)). Qed.
Lemma lem2266045 : term377 = True.
Proof. exact (TRANS (@lem2266040) (@lem2266044)). Qed.
Lemma lem2266046 : True = term377.
Proof. exact (SYM (@lem2266045)). Qed.
Lemma lem2266047 : term377.
Proof. exact (EQ_MP (@lem2266046) (@lem0)). Qed.
Lemma lem2266048 : term415.
Proof. exact (@lem2266037 (@lem2266047)). Qed.
Lemma lem2266050 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266051 : term377 = term383.
Proof. exact (@lem2266050 (NUMERAL 0) term32). Qed.
Lemma lem2266052 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266053 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266054 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266053 h1) (fun h1 : term383 = True => @lem2266052)). Qed.
Lemma lem2266055 : term383 = True.
Proof. exact (EQ_MP (@lem2266054) (@lem2266052)). Qed.
Lemma lem2266056 : term377 = True.
Proof. exact (TRANS (@lem2266051) (@lem2266055)). Qed.
Lemma lem2266057 : True = term377.
Proof. exact (SYM (@lem2266056)). Qed.
Lemma lem2266058 : term377.
Proof. exact (EQ_MP (@lem2266057) (@lem0)). Qed.
Lemma lem2266059 : term416.
Proof. exact (@lem2266048 (@lem2266058)). Qed.
Lemma lem2266061 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266062 : term377 = term383.
Proof. exact (@lem2266061 (NUMERAL 0) term32). Qed.
Lemma lem2266063 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266064 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266065 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266064 h1) (fun h1 : term383 = True => @lem2266063)). Qed.
Lemma lem2266066 : term383 = True.
Proof. exact (EQ_MP (@lem2266065) (@lem2266063)). Qed.
Lemma lem2266067 : term377 = True.
Proof. exact (TRANS (@lem2266062) (@lem2266066)). Qed.
Lemma lem2266068 : True = term377.
Proof. exact (SYM (@lem2266067)). Qed.
Lemma lem2266069 : term377.
Proof. exact (EQ_MP (@lem2266068) (@lem0)). Qed.
Lemma lem2266070 : term417.
Proof. exact (@lem2266059 (@lem2266069)). Qed.
Lemma lem2266072 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266073 : term41 = term42.
Proof. exact (@lem2266072 term32 term32). Qed.
Lemma lem2266074 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266075 : term44 = term32.
Proof. exact (EQ_MP (@lem2266074) (@lem940073)). Qed.
Lemma lem2266076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266077 : term42 = term38.
Proof. exact (MK_COMB (@lem2266076) (@lem2266075)). Qed.
Lemma lem2266078 : term41 = term38.
Proof. exact (TRANS (@lem2266073) (@lem2266077)). Qed.
Lemma lem2266080 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2266081 : term420 = term421.
Proof. exact (@lem2266080 term32 term32). Qed.
Lemma lem2266082 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266083 : term44 = term32.
Proof. exact (EQ_MP (@lem2266082) (@lem940073)). Qed.
Lemma lem2266084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266085 : term42 = term38.
Proof. exact (MK_COMB (@lem2266084) (@lem2266083)). Qed.
Lemma lem2266086 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2266087 : term421 = term26.
Proof. exact (MK_COMB (@lem2266086) (@lem2266085)). Qed.
Lemma lem2266088 : term420 = term26.
Proof. exact (TRANS (@lem2266081) (@lem2266087)). Qed.
Lemma lem2266089 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266090 : term422 = term410.
Proof. exact (MK_COMB (@lem2266089) (@lem2266088)). Qed.
Lemma lem2266091 : term423 = term412.
Proof. exact (MK_COMB (@lem2266090) (@lem2266078)). Qed.
Lemma lem2266093 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2266094 : term412 = term14.
Proof. exact (@lem2266093 term32). Qed.
Lemma lem2266095 : term423 = term14.
Proof. exact (TRANS (@lem2266091) (@lem2266094)). Qed.
Lemma lem2266096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266097 : term425 = term426.
Proof. exact (MK_COMB (@lem2266096) (@lem2266095)). Qed.
Lemma lem2266098 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2266099 : term427 = term388.
Proof. exact (MK_COMB (@lem2266097) (@lem2266098)). Qed.
Lemma lem2266101 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266102 : term388 = term14.
Proof. exact (@lem2266101 term32). Qed.
Lemma lem2266103 : term427 = term14.
Proof. exact (TRANS (@lem2266099) (@lem2266102)). Qed.
Lemma lem2266105 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266106 : term41 = term42.
Proof. exact (@lem2266105 term32 term32). Qed.
Lemma lem2266107 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266108 : term44 = term32.
Proof. exact (EQ_MP (@lem2266107) (@lem940073)). Qed.
Lemma lem2266109 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266110 : term42 = term38.
Proof. exact (MK_COMB (@lem2266109) (@lem2266108)). Qed.
Lemma lem2266111 : term41 = term38.
Proof. exact (TRANS (@lem2266106) (@lem2266110)). Qed.
Lemma lem2266112 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2266113 : term428 = term388.
Proof. exact (MK_COMB (@lem2266112) (@lem2266111)). Qed.
Lemma lem2266115 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266116 : term388 = term14.
Proof. exact (@lem2266115 term32). Qed.
Lemma lem2266117 : term428 = term14.
Proof. exact (TRANS (@lem2266113) (@lem2266116)). Qed.
Lemma lem2266118 : term14 = term428.
Proof. exact (SYM (@lem2266117)). Qed.
Lemma lem2266119 : term427 = term428.
Proof. exact (TRANS (@lem2266103) (@lem2266118)). Qed.
Lemma lem2266120 : term413 = term180.
Proof. exact (@lem2266070 (@lem2266119)). Qed.
Lemma lem2266121 : term412 = term180.
Proof. exact (TRANS (@lem2266036) (@lem2266120)). Qed.
Lemma lem2266123 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2266124 : term180 = term14.
Proof. exact (@lem2266123 term14). Qed.
Lemma lem2266125 : term412 = term14.
Proof. exact (TRANS (@lem2266121) (@lem2266124)). Qed.
Lemma lem2266126 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266127 : term429 = term426.
Proof. exact (MK_COMB (@lem2266126) (@lem2266125)). Qed.
Lemma lem2266128 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2266129 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2266127) (@lem2266128 n)). Qed.
Lemma lem2266130 (n : nat) : (term460 n) = (term387 n).
Proof. exact (TRANS (@lem2266027 n) (@lem2266129 n)). Qed.
Lemma lem2266131 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2266132 (n : nat) : (term460 n) = term14.
Proof. exact (TRANS (@lem2266130 n) (@lem2266131 n)). Qed.
Lemma lem2266133 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2266134 (n : nat) (x : real) : (term595 x n) = (term596 x).
Proof. exact (MK_COMB (@lem2266133 x) (@lem2266132 n)). Qed.
Lemma lem2266135 (n : nat) (x : real) : (term594 x n) = (term596 x).
Proof. exact (TRANS (@lem2266026 x n) (@lem2266134 n x)). Qed.
Lemma lem2266136 (x : real) : (term596 x) = (term208 x).
Proof. exact (@lem1982723 (term208 x)). Qed.
Lemma lem2266137 (n : nat) (x : real) : (term594 x n) = (term208 x).
Proof. exact (TRANS (@lem2266135 n x) (@lem2266136 x)). Qed.
Lemma lem2266138 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2266139 (n : nat) (x : real) : (term597 x n) = (term598 x).
Proof. exact (MK_COMB (@lem2266138) (@lem2266137 n x)). Qed.
Lemma lem2266140 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266141 (n : nat) (x : real) : (term593 x n) = (term599 x).
Proof. exact (MK_COMB (@lem2266139 n x) (@lem2266140)). Qed.
Lemma lem2266142 (x : real) (n : nat) (h1 : term358 x n) : term599 x.
Proof. exact (EQ_MP (@lem2266141 n x) (@lem2266025 x n h1)). Qed.
Lemma lem2266144 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2266145 : term508 = term509.
Proof. exact (@lem2266144 term14 term510). Qed.
Lemma lem2266147 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266148 : term510 = term511.
Proof. exact (@lem2266147 term512). Qed.
Lemma lem2266150 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266151 : term14 = term180.
Proof. exact (@lem2266150 (NUMERAL 0)). Qed.
Lemma lem2266152 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266153 : term378 = term379.
Proof. exact (MK_COMB (@lem2266152) (@lem2266151)). Qed.
Lemma lem2266154 : term509 = term513.
Proof. exact (MK_COMB (@lem2266153) (@lem2266148)). Qed.
Lemma lem2266155 : term514.
Proof. exact (@lem1980255 term14 term38 term510 term38). Qed.
Lemma lem2266157 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266158 : term377 = term383.
Proof. exact (@lem2266157 (NUMERAL 0) term32). Qed.
Lemma lem2266159 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266160 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266161 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266160 h1) (fun h1 : term383 = True => @lem2266159)). Qed.
Lemma lem2266162 : term383 = True.
Proof. exact (EQ_MP (@lem2266161) (@lem2266159)). Qed.
Lemma lem2266163 : term377 = True.
Proof. exact (TRANS (@lem2266158) (@lem2266162)). Qed.
Lemma lem2266164 : True = term377.
Proof. exact (SYM (@lem2266163)). Qed.
Lemma lem2266165 : term377.
Proof. exact (EQ_MP (@lem2266164) (@lem0)). Qed.
Lemma lem2266166 : term515.
Proof. exact (@lem2266155 (@lem2266165)). Qed.
Lemma lem2266168 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266169 : term377 = term383.
Proof. exact (@lem2266168 (NUMERAL 0) term32). Qed.
Lemma lem2266170 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266171 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266172 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266171 h1) (fun h1 : term383 = True => @lem2266170)). Qed.
Lemma lem2266173 : term383 = True.
Proof. exact (EQ_MP (@lem2266172) (@lem2266170)). Qed.
Lemma lem2266174 : term377 = True.
Proof. exact (TRANS (@lem2266169) (@lem2266173)). Qed.
Lemma lem2266175 : True = term377.
Proof. exact (SYM (@lem2266174)). Qed.
Lemma lem2266176 : term377.
Proof. exact (EQ_MP (@lem2266175) (@lem0)). Qed.
Lemma lem2266177 : term513 = term516.
Proof. exact (@lem2266166 (@lem2266176)). Qed.
Lemma lem2266179 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266180 : term517 = term518.
Proof. exact (@lem2266179 term512 term32). Qed.
Lemma lem2266181 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2266182 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2266183 : term521 = term512.
Proof. exact (EQ_MP (@lem2266182) (@lem2266181)). Qed.
Lemma lem2266184 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266185 : term518 = term510.
Proof. exact (MK_COMB (@lem2266184) (@lem2266183)). Qed.
Lemma lem2266186 : term517 = term510.
Proof. exact (TRANS (@lem2266180) (@lem2266185)). Qed.
Lemma lem2266188 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266189 : term388 = term14.
Proof. exact (@lem2266188 term32). Qed.
Lemma lem2266190 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266191 : term389 = term378.
Proof. exact (MK_COMB (@lem2266190) (@lem2266189)). Qed.
Lemma lem2266192 : term516 = term509.
Proof. exact (MK_COMB (@lem2266191) (@lem2266186)). Qed.
Lemma lem2266194 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266195 : term509 = term522.
Proof. exact (@lem2266194 (NUMERAL 0) term512). Qed.
Lemma lem2266196 : term523 = term520.
Proof. exact (@lem912803). Qed.
Lemma lem2266197 (h1 : term523 = term520) : term522 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term520 h1). Qed.
Lemma lem2266198 : (term523 = term520) = (term522 = True).
Proof. exact (prop_ext (fun h1 : term523 = term520 => @lem2266197 h1) (fun h1 : term522 = True => @lem2266196)). Qed.
Lemma lem2266199 : term522 = True.
Proof. exact (EQ_MP (@lem2266198) (@lem2266196)). Qed.
Lemma lem2266200 : term509 = True.
Proof. exact (TRANS (@lem2266195) (@lem2266199)). Qed.
Lemma lem2266201 : term516 = True.
Proof. exact (TRANS (@lem2266192) (@lem2266200)). Qed.
Lemma lem2266202 : term513 = True.
Proof. exact (TRANS (@lem2266177) (@lem2266201)). Qed.
Lemma lem2266203 : term509 = True.
Proof. exact (TRANS (@lem2266154) (@lem2266202)). Qed.
Lemma lem2266204 : term508 = True.
Proof. exact (TRANS (@lem2266145) (@lem2266203)). Qed.
Lemma lem2266205 : True = term508.
Proof. exact (SYM (@lem2266204)). Qed.
Lemma lem2266206 : term508.
Proof. exact (EQ_MP (@lem2266205) (@lem0)). Qed.
Lemma lem2266207 (x : real) (n : nat) (h1 : term358 x n) : term600 x.
Proof. exact (conj (@lem2266206) (@lem2266142 x n h1)). Qed.
Lemma lem2266209 (x : real) (y : real) : term496 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2266210 (x : real) : term601 x.
Proof. exact (@lem2266209 term510 (term208 x)). Qed.
Lemma lem2266211 (x : real) (n : nat) (h1 : term358 x n) : term602 x.
Proof. exact (@lem2266210 x (@lem2266207 x n h1)). Qed.
Lemma lem2266212 (x : real) : (term603 x) = (term604 x).
Proof. exact (@lem1982749 term510 term26 x). Qed.
Lemma lem2266214 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2266215 : term26 = term31.
Proof. exact (@lem2266214 term32). Qed.
Lemma lem2266217 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266218 : term510 = term511.
Proof. exact (@lem2266217 term512). Qed.
Lemma lem2266219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266220 : term605 = term606.
Proof. exact (MK_COMB (@lem2266219) (@lem2266218)). Qed.
Lemma lem2266221 : term607 = term608.
Proof. exact (MK_COMB (@lem2266220) (@lem2266215)). Qed.
Lemma lem2266222 : term608 = term609.
Proof. exact (@lem1981613 term510 term26 term38 term38). Qed.
Lemma lem2266224 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266225 : term41 = term42.
Proof. exact (@lem2266224 term32 term32). Qed.
Lemma lem2266226 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266227 : term44 = term32.
Proof. exact (EQ_MP (@lem2266226) (@lem940073)). Qed.
Lemma lem2266228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266229 : term42 = term38.
Proof. exact (MK_COMB (@lem2266228) (@lem2266227)). Qed.
Lemma lem2266230 : term41 = term38.
Proof. exact (TRANS (@lem2266225) (@lem2266229)). Qed.
Lemma lem2266232 (m : nat) (n : nat) : (term610 m n) = (term419 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2266233 : term607 = term550.
Proof. exact (@lem2266232 term512 term32). Qed.
Lemma lem2266234 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2266235 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2266236 : term521 = term512.
Proof. exact (EQ_MP (@lem2266235) (@lem2266234)). Qed.
Lemma lem2266237 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266238 : term518 = term510.
Proof. exact (MK_COMB (@lem2266237) (@lem2266236)). Qed.
Lemma lem2266239 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2266240 : term550 = term537.
Proof. exact (MK_COMB (@lem2266239) (@lem2266238)). Qed.
Lemma lem2266241 : term607 = term537.
Proof. exact (TRANS (@lem2266233) (@lem2266240)). Qed.
Lemma lem2266242 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2266243 : term611 = term612.
Proof. exact (MK_COMB (@lem2266242) (@lem2266241)). Qed.
Lemma lem2266244 : term609 = term552.
Proof. exact (MK_COMB (@lem2266243) (@lem2266230)). Qed.
Lemma lem2266245 : term608 = term552.
Proof. exact (TRANS (@lem2266222) (@lem2266244)). Qed.
Lemma lem2266246 : term607 = term552.
Proof. exact (TRANS (@lem2266221) (@lem2266245)). Qed.
Lemma lem2266248 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2266249 : term552 = term537.
Proof. exact (@lem2266248 term537). Qed.
Lemma lem2266250 : term607 = term537.
Proof. exact (TRANS (@lem2266246) (@lem2266249)). Qed.
Lemma lem2266251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266252 : term613 = term547.
Proof. exact (MK_COMB (@lem2266251) (@lem2266250)). Qed.
Lemma lem2266253 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2266254 (x : real) : (term604 x) = (term554 x).
Proof. exact (MK_COMB (@lem2266252) (@lem2266253 x)). Qed.
Lemma lem2266255 (x : real) : (term603 x) = (term554 x).
Proof. exact (TRANS (@lem2266212 x) (@lem2266254 x)). Qed.
Lemma lem2266256 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2266257 (x : real) : (term614 x) = (term615 x).
Proof. exact (MK_COMB (@lem2266256) (@lem2266255 x)). Qed.
Lemma lem2266258 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266259 (x : real) : (term602 x) = (term616 x).
Proof. exact (MK_COMB (@lem2266257 x) (@lem2266258)). Qed.
Lemma lem2266260 (x : real) (n : nat) (h1 : term358 x n) : term616 x.
Proof. exact (EQ_MP (@lem2266259 x) (@lem2266211 x n h1)). Qed.
Lemma lem2266262 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2266263 : term376 = term377.
Proof. exact (@lem2266262 term14 term38). Qed.
Lemma lem2266265 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266266 : term38 = term48.
Proof. exact (@lem2266265 term32). Qed.
Lemma lem2266268 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266269 : term14 = term180.
Proof. exact (@lem2266268 (NUMERAL 0)). Qed.
Lemma lem2266270 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266271 : term378 = term379.
Proof. exact (MK_COMB (@lem2266270) (@lem2266269)). Qed.
Lemma lem2266272 : term377 = term380.
Proof. exact (MK_COMB (@lem2266271) (@lem2266266)). Qed.
Lemma lem2266273 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2266275 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266276 : term377 = term383.
Proof. exact (@lem2266275 (NUMERAL 0) term32). Qed.
Lemma lem2266277 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266278 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266279 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266278 h1) (fun h1 : term383 = True => @lem2266277)). Qed.
Lemma lem2266280 : term383 = True.
Proof. exact (EQ_MP (@lem2266279) (@lem2266277)). Qed.
Lemma lem2266281 : term377 = True.
Proof. exact (TRANS (@lem2266276) (@lem2266280)). Qed.
Lemma lem2266282 : True = term377.
Proof. exact (SYM (@lem2266281)). Qed.
Lemma lem2266283 : term377.
Proof. exact (EQ_MP (@lem2266282) (@lem0)). Qed.
Lemma lem2266284 : term385.
Proof. exact (@lem2266273 (@lem2266283)). Qed.
Lemma lem2266286 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266287 : term377 = term383.
Proof. exact (@lem2266286 (NUMERAL 0) term32). Qed.
Lemma lem2266288 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266289 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266290 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266289 h1) (fun h1 : term383 = True => @lem2266288)). Qed.
Lemma lem2266291 : term383 = True.
Proof. exact (EQ_MP (@lem2266290) (@lem2266288)). Qed.
Lemma lem2266292 : term377 = True.
Proof. exact (TRANS (@lem2266287) (@lem2266291)). Qed.
Lemma lem2266293 : True = term377.
Proof. exact (SYM (@lem2266292)). Qed.
Lemma lem2266294 : term377.
Proof. exact (EQ_MP (@lem2266293) (@lem0)). Qed.
Lemma lem2266295 : term380 = term386.
Proof. exact (@lem2266284 (@lem2266294)). Qed.
Lemma lem2266297 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266298 : term41 = term42.
Proof. exact (@lem2266297 term32 term32). Qed.
Lemma lem2266299 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266300 : term44 = term32.
Proof. exact (EQ_MP (@lem2266299) (@lem940073)). Qed.
Lemma lem2266301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266302 : term42 = term38.
Proof. exact (MK_COMB (@lem2266301) (@lem2266300)). Qed.
Lemma lem2266303 : term41 = term38.
Proof. exact (TRANS (@lem2266298) (@lem2266302)). Qed.
Lemma lem2266305 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266306 : term388 = term14.
Proof. exact (@lem2266305 term32). Qed.
Lemma lem2266307 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266308 : term389 = term378.
Proof. exact (MK_COMB (@lem2266307) (@lem2266306)). Qed.
Lemma lem2266309 : term386 = term377.
Proof. exact (MK_COMB (@lem2266308) (@lem2266303)). Qed.
Lemma lem2266311 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266312 : term377 = term383.
Proof. exact (@lem2266311 (NUMERAL 0) term32). Qed.
Lemma lem2266313 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266314 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266315 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266314 h1) (fun h1 : term383 = True => @lem2266313)). Qed.
Lemma lem2266316 : term383 = True.
Proof. exact (EQ_MP (@lem2266315) (@lem2266313)). Qed.
Lemma lem2266317 : term377 = True.
Proof. exact (TRANS (@lem2266312) (@lem2266316)). Qed.
Lemma lem2266318 : term386 = True.
Proof. exact (TRANS (@lem2266309) (@lem2266317)). Qed.
Lemma lem2266319 : term380 = True.
Proof. exact (TRANS (@lem2266295) (@lem2266318)). Qed.
Lemma lem2266320 : term377 = True.
Proof. exact (TRANS (@lem2266272) (@lem2266319)). Qed.
Lemma lem2266321 : term376 = True.
Proof. exact (TRANS (@lem2266263) (@lem2266320)). Qed.
Lemma lem2266322 : True = term376.
Proof. exact (SYM (@lem2266321)). Qed.
Lemma lem2266323 : term376.
Proof. exact (EQ_MP (@lem2266322) (@lem0)). Qed.
Lemma lem2266324 (x : real) (n : nat) (h1 : term358 x n) : term390 x n.
Proof. exact (conj (@lem2266323) (@lem2265926 x n h1)). Qed.
Lemma lem2266326 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2266327 (x : real) (n : nat) : term392 x n.
Proof. exact (@lem2266326 term38 (term21 x n)). Qed.
Lemma lem2266328 (x : real) (n : nat) (h1 : term358 x n) : term393 x n.
Proof. exact (@lem2266327 x n (@lem2266324 x n h1)). Qed.
Lemma lem2266329 (x : real) (n : nat) : (term394 x n) = (term21 x n).
Proof. exact (@lem1982733 (term21 x n)). Qed.
Lemma lem2266330 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2266331 (x : real) (n : nat) : (term395 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem2266330) (@lem2266329 x n)). Qed.
Lemma lem2266332 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266333 (x : real) (n : nat) : (term393 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem2266331 x n) (@lem2266332)). Qed.
Lemma lem2266334 (x : real) (n : nat) (h1 : term358 x n) : term63 x n.
Proof. exact (EQ_MP (@lem2266333 x n) (@lem2266328 x n h1)). Qed.
Lemma lem2266336 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2266337 (x : real) (n : nat) : term587 x n.
Proof. exact (@lem2266336 (term72 x n)). Qed.
Lemma lem2266338 (x : real) (n : nat) (h1 : term358 x n) : term588 x n.
Proof. exact (@lem2266337 x n (@lem2265925 x n h1)). Qed.
Lemma lem2266339 (x : real) (n : nat) (h1 : term358 x n) : term617 x n.
Proof. exact (@lem2266338 x n h1 term38). Qed.
Lemma lem2266340 (x : real) (n : nat) : (term617 x n) = ((term448 x n) = term14).
Proof. exact (eq_refl (term617 x n)). Qed.
Lemma lem2266341 (x : real) (n : nat) (h1 : term358 x n) : (term448 x n) = term14.
Proof. exact (EQ_MP (@lem2266340 x n) (@lem2266339 x n h1)). Qed.
Lemma lem2266342 (x : real) (n : nat) : (term448 x n) = (term72 x n).
Proof. exact (@lem1982733 (term72 x n)). Qed.
Lemma lem2266343 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2266344 (x : real) (n : nat) : (term618 x n) = (term117 x n).
Proof. exact (MK_COMB (@lem2266343) (@lem2266342 x n)). Qed.
Lemma lem2266345 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266346 (x : real) (n : nat) : ((term448 x n) = term14) = ((term72 x n) = term14).
Proof. exact (MK_COMB (@lem2266344 x n) (@lem2266345)). Qed.
Lemma lem2266347 (x : real) (n : nat) (h1 : term358 x n) : (term72 x n) = term14.
Proof. exact (EQ_MP (@lem2266346 x n) (@lem2266341 x n h1)). Qed.
Lemma lem2266348 (x : real) (n : nat) (h1 : term358 x n) : term619 x n.
Proof. exact (conj (@lem2266347 x n h1) (@lem2266334 x n h1)). Qed.
Lemma lem2266350 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2266351 (x : real) (n : nat) : term620 x n.
Proof. exact (@lem2266350 (term72 x n) (term21 x n)). Qed.
Lemma lem2266352 (x : real) (n : nat) (h1 : term358 x n) : term621 x n.
Proof. exact (@lem2266351 x n (@lem2266348 x n h1)). Qed.
Lemma lem2266353 (x : real) (n : nat) : (term622 x n) = (term623 x n).
Proof. exact (@lem1982753 x x (real_of_num n) (term27 n)). Qed.
Lemma lem2266354 (x : real) : (real_add x x) = (term624 x).
Proof. exact (@lem1982717 x). Qed.
Lemma lem2266356 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266357 : term38 = term48.
Proof. exact (@lem2266356 term32). Qed.
Lemma lem2266359 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266360 : term38 = term48.
Proof. exact (@lem2266359 term32). Qed.
Lemma lem2266361 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266362 : term625 = term626.
Proof. exact (MK_COMB (@lem2266361) (@lem2266360)). Qed.
Lemma lem2266363 : term627 = term628.
Proof. exact (MK_COMB (@lem2266362) (@lem2266357)). Qed.
Lemma lem2266364 : term629.
Proof. exact (@lem1981473 term38 term38 term38 term38 term510 term38). Qed.
Lemma lem2266366 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266367 : term377 = term383.
Proof. exact (@lem2266366 (NUMERAL 0) term32). Qed.
Lemma lem2266368 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266369 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266370 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266369 h1) (fun h1 : term383 = True => @lem2266368)). Qed.
Lemma lem2266371 : term383 = True.
Proof. exact (EQ_MP (@lem2266370) (@lem2266368)). Qed.
Lemma lem2266372 : term377 = True.
Proof. exact (TRANS (@lem2266367) (@lem2266371)). Qed.
Lemma lem2266373 : True = term377.
Proof. exact (SYM (@lem2266372)). Qed.
Lemma lem2266374 : term377.
Proof. exact (EQ_MP (@lem2266373) (@lem0)). Qed.
Lemma lem2266375 : term630.
Proof. exact (@lem2266364 (@lem2266374)). Qed.
Lemma lem2266377 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266378 : term377 = term383.
Proof. exact (@lem2266377 (NUMERAL 0) term32). Qed.
Lemma lem2266379 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266380 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266381 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266380 h1) (fun h1 : term383 = True => @lem2266379)). Qed.
Lemma lem2266382 : term383 = True.
Proof. exact (EQ_MP (@lem2266381) (@lem2266379)). Qed.
Lemma lem2266383 : term377 = True.
Proof. exact (TRANS (@lem2266378) (@lem2266382)). Qed.
Lemma lem2266384 : True = term377.
Proof. exact (SYM (@lem2266383)). Qed.
Lemma lem2266385 : term377.
Proof. exact (EQ_MP (@lem2266384) (@lem0)). Qed.
Lemma lem2266386 : term631.
Proof. exact (@lem2266375 (@lem2266385)). Qed.
Lemma lem2266388 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266389 : term377 = term383.
Proof. exact (@lem2266388 (NUMERAL 0) term32). Qed.
Lemma lem2266390 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266391 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266392 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266391 h1) (fun h1 : term383 = True => @lem2266390)). Qed.
Lemma lem2266393 : term383 = True.
Proof. exact (EQ_MP (@lem2266392) (@lem2266390)). Qed.
Lemma lem2266394 : term377 = True.
Proof. exact (TRANS (@lem2266389) (@lem2266393)). Qed.
Lemma lem2266395 : True = term377.
Proof. exact (SYM (@lem2266394)). Qed.
Lemma lem2266396 : term377.
Proof. exact (EQ_MP (@lem2266395) (@lem0)). Qed.
Lemma lem2266397 : term632.
Proof. exact (@lem2266386 (@lem2266396)). Qed.
Lemma lem2266399 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266400 : term41 = term42.
Proof. exact (@lem2266399 term32 term32). Qed.
Lemma lem2266401 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266402 : term44 = term32.
Proof. exact (EQ_MP (@lem2266401) (@lem940073)). Qed.
Lemma lem2266403 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266404 : term42 = term38.
Proof. exact (MK_COMB (@lem2266403) (@lem2266402)). Qed.
Lemma lem2266405 : term41 = term38.
Proof. exact (TRANS (@lem2266400) (@lem2266404)). Qed.
Lemma lem2266407 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266408 : term41 = term42.
Proof. exact (@lem2266407 term32 term32). Qed.
Lemma lem2266409 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266410 : term44 = term32.
Proof. exact (EQ_MP (@lem2266409) (@lem940073)). Qed.
Lemma lem2266411 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266412 : term42 = term38.
Proof. exact (MK_COMB (@lem2266411) (@lem2266410)). Qed.
Lemma lem2266413 : term41 = term38.
Proof. exact (TRANS (@lem2266408) (@lem2266412)). Qed.
Lemma lem2266414 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266415 : term633 = term625.
Proof. exact (MK_COMB (@lem2266414) (@lem2266413)). Qed.
Lemma lem2266416 : term634 = term627.
Proof. exact (MK_COMB (@lem2266415) (@lem2266405)). Qed.
Lemma lem2266417 : term627 = term545.
Proof. exact (@lem1367770 term32 term32). Qed.
Lemma lem2266418 : term543 = term520.
Proof. exact (@lem706885). Qed.
Lemma lem2266419 : (term543 = term520) = (term544 = term512).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term520). Qed.
Lemma lem2266420 : term544 = term512.
Proof. exact (EQ_MP (@lem2266419) (@lem2266418)). Qed.
Lemma lem2266421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266422 : term545 = term510.
Proof. exact (MK_COMB (@lem2266421) (@lem2266420)). Qed.
Lemma lem2266423 : term627 = term510.
Proof. exact (TRANS (@lem2266417) (@lem2266422)). Qed.
Lemma lem2266424 : term634 = term510.
Proof. exact (TRANS (@lem2266416) (@lem2266423)). Qed.
Lemma lem2266425 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266426 : term635 = term605.
Proof. exact (MK_COMB (@lem2266425) (@lem2266424)). Qed.
Lemma lem2266427 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2266428 : term636 = term517.
Proof. exact (MK_COMB (@lem2266426) (@lem2266427)). Qed.
Lemma lem2266430 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266431 : term517 = term518.
Proof. exact (@lem2266430 term512 term32). Qed.
Lemma lem2266432 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2266433 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2266434 : term521 = term512.
Proof. exact (EQ_MP (@lem2266433) (@lem2266432)). Qed.
Lemma lem2266435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266436 : term518 = term510.
Proof. exact (MK_COMB (@lem2266435) (@lem2266434)). Qed.
Lemma lem2266437 : term517 = term510.
Proof. exact (TRANS (@lem2266431) (@lem2266436)). Qed.
Lemma lem2266438 : term636 = term510.
Proof. exact (TRANS (@lem2266428) (@lem2266437)). Qed.
Lemma lem2266440 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266441 : term41 = term42.
Proof. exact (@lem2266440 term32 term32). Qed.
Lemma lem2266442 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266443 : term44 = term32.
Proof. exact (EQ_MP (@lem2266442) (@lem940073)). Qed.
Lemma lem2266444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266445 : term42 = term38.
Proof. exact (MK_COMB (@lem2266444) (@lem2266443)). Qed.
Lemma lem2266446 : term41 = term38.
Proof. exact (TRANS (@lem2266441) (@lem2266445)). Qed.
Lemma lem2266447 : term605 = term605.
Proof. exact (eq_refl term605). Qed.
Lemma lem2266448 : term637 = term517.
Proof. exact (MK_COMB (@lem2266447) (@lem2266446)). Qed.
Lemma lem2266450 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266451 : term517 = term518.
Proof. exact (@lem2266450 term512 term32). Qed.
Lemma lem2266452 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2266453 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2266454 : term521 = term512.
Proof. exact (EQ_MP (@lem2266453) (@lem2266452)). Qed.
Lemma lem2266455 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266456 : term518 = term510.
Proof. exact (MK_COMB (@lem2266455) (@lem2266454)). Qed.
Lemma lem2266457 : term517 = term510.
Proof. exact (TRANS (@lem2266451) (@lem2266456)). Qed.
Lemma lem2266458 : term637 = term510.
Proof. exact (TRANS (@lem2266448) (@lem2266457)). Qed.
Lemma lem2266459 : term510 = term637.
Proof. exact (SYM (@lem2266458)). Qed.
Lemma lem2266460 : term636 = term637.
Proof. exact (TRANS (@lem2266438) (@lem2266459)). Qed.
Lemma lem2266461 : term628 = term511.
Proof. exact (@lem2266397 (@lem2266460)). Qed.
Lemma lem2266462 : term627 = term511.
Proof. exact (TRANS (@lem2266363) (@lem2266461)). Qed.
Lemma lem2266464 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2266465 : term511 = term510.
Proof. exact (@lem2266464 term510). Qed.
Lemma lem2266466 : term627 = term510.
Proof. exact (TRANS (@lem2266462) (@lem2266465)). Qed.
Lemma lem2266467 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266468 : term638 = term605.
Proof. exact (MK_COMB (@lem2266467) (@lem2266466)). Qed.
Lemma lem2266469 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2266470 (x : real) : (term624 x) = (term569 x).
Proof. exact (MK_COMB (@lem2266468) (@lem2266469 x)). Qed.
Lemma lem2266471 (x : real) : (real_add x x) = (term569 x).
Proof. exact (TRANS (@lem2266354 x) (@lem2266470 x)). Qed.
Lemma lem2266472 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266473 (x : real) : (term639 x) = (term640 x).
Proof. exact (MK_COMB (@lem2266472) (@lem2266471 x)). Qed.
Lemma lem2266474 (n : nat) : (term433 n) = (term434 n).
Proof. exact (@lem1982715 term26 (real_of_num n)). Qed.
Lemma lem2266476 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266477 : term38 = term48.
Proof. exact (@lem2266476 term32). Qed.
Lemma lem2266479 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2266480 : term26 = term31.
Proof. exact (@lem2266479 term32). Qed.
Lemma lem2266481 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266482 : term410 = term411.
Proof. exact (MK_COMB (@lem2266481) (@lem2266480)). Qed.
Lemma lem2266483 : term412 = term413.
Proof. exact (MK_COMB (@lem2266482) (@lem2266477)). Qed.
Lemma lem2266484 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2266486 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266487 : term377 = term383.
Proof. exact (@lem2266486 (NUMERAL 0) term32). Qed.
Lemma lem2266488 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266489 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266490 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266489 h1) (fun h1 : term383 = True => @lem2266488)). Qed.
Lemma lem2266491 : term383 = True.
Proof. exact (EQ_MP (@lem2266490) (@lem2266488)). Qed.
Lemma lem2266492 : term377 = True.
Proof. exact (TRANS (@lem2266487) (@lem2266491)). Qed.
Lemma lem2266493 : True = term377.
Proof. exact (SYM (@lem2266492)). Qed.
Lemma lem2266494 : term377.
Proof. exact (EQ_MP (@lem2266493) (@lem0)). Qed.
Lemma lem2266495 : term415.
Proof. exact (@lem2266484 (@lem2266494)). Qed.
Lemma lem2266497 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266498 : term377 = term383.
Proof. exact (@lem2266497 (NUMERAL 0) term32). Qed.
Lemma lem2266499 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266500 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266501 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266500 h1) (fun h1 : term383 = True => @lem2266499)). Qed.
Lemma lem2266502 : term383 = True.
Proof. exact (EQ_MP (@lem2266501) (@lem2266499)). Qed.
Lemma lem2266503 : term377 = True.
Proof. exact (TRANS (@lem2266498) (@lem2266502)). Qed.
Lemma lem2266504 : True = term377.
Proof. exact (SYM (@lem2266503)). Qed.
Lemma lem2266505 : term377.
Proof. exact (EQ_MP (@lem2266504) (@lem0)). Qed.
Lemma lem2266506 : term416.
Proof. exact (@lem2266495 (@lem2266505)). Qed.
Lemma lem2266508 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266509 : term377 = term383.
Proof. exact (@lem2266508 (NUMERAL 0) term32). Qed.
Lemma lem2266510 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266511 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266512 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266511 h1) (fun h1 : term383 = True => @lem2266510)). Qed.
Lemma lem2266513 : term383 = True.
Proof. exact (EQ_MP (@lem2266512) (@lem2266510)). Qed.
Lemma lem2266514 : term377 = True.
Proof. exact (TRANS (@lem2266509) (@lem2266513)). Qed.
Lemma lem2266515 : True = term377.
Proof. exact (SYM (@lem2266514)). Qed.
Lemma lem2266516 : term377.
Proof. exact (EQ_MP (@lem2266515) (@lem0)). Qed.
Lemma lem2266517 : term417.
Proof. exact (@lem2266506 (@lem2266516)). Qed.
Lemma lem2266519 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266520 : term41 = term42.
Proof. exact (@lem2266519 term32 term32). Qed.
Lemma lem2266521 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266522 : term44 = term32.
Proof. exact (EQ_MP (@lem2266521) (@lem940073)). Qed.
Lemma lem2266523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266524 : term42 = term38.
Proof. exact (MK_COMB (@lem2266523) (@lem2266522)). Qed.
Lemma lem2266525 : term41 = term38.
Proof. exact (TRANS (@lem2266520) (@lem2266524)). Qed.
Lemma lem2266527 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2266528 : term420 = term421.
Proof. exact (@lem2266527 term32 term32). Qed.
Lemma lem2266529 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266530 : term44 = term32.
Proof. exact (EQ_MP (@lem2266529) (@lem940073)). Qed.
Lemma lem2266531 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266532 : term42 = term38.
Proof. exact (MK_COMB (@lem2266531) (@lem2266530)). Qed.
Lemma lem2266533 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2266534 : term421 = term26.
Proof. exact (MK_COMB (@lem2266533) (@lem2266532)). Qed.
Lemma lem2266535 : term420 = term26.
Proof. exact (TRANS (@lem2266528) (@lem2266534)). Qed.
Lemma lem2266536 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266537 : term422 = term410.
Proof. exact (MK_COMB (@lem2266536) (@lem2266535)). Qed.
Lemma lem2266538 : term423 = term412.
Proof. exact (MK_COMB (@lem2266537) (@lem2266525)). Qed.
Lemma lem2266540 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2266541 : term412 = term14.
Proof. exact (@lem2266540 term32). Qed.
Lemma lem2266542 : term423 = term14.
Proof. exact (TRANS (@lem2266538) (@lem2266541)). Qed.
Lemma lem2266543 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266544 : term425 = term426.
Proof. exact (MK_COMB (@lem2266543) (@lem2266542)). Qed.
Lemma lem2266545 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2266546 : term427 = term388.
Proof. exact (MK_COMB (@lem2266544) (@lem2266545)). Qed.
Lemma lem2266548 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266549 : term388 = term14.
Proof. exact (@lem2266548 term32). Qed.
Lemma lem2266550 : term427 = term14.
Proof. exact (TRANS (@lem2266546) (@lem2266549)). Qed.
Lemma lem2266552 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266553 : term41 = term42.
Proof. exact (@lem2266552 term32 term32). Qed.
Lemma lem2266554 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266555 : term44 = term32.
Proof. exact (EQ_MP (@lem2266554) (@lem940073)). Qed.
Lemma lem2266556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266557 : term42 = term38.
Proof. exact (MK_COMB (@lem2266556) (@lem2266555)). Qed.
Lemma lem2266558 : term41 = term38.
Proof. exact (TRANS (@lem2266553) (@lem2266557)). Qed.
Lemma lem2266559 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2266560 : term428 = term388.
Proof. exact (MK_COMB (@lem2266559) (@lem2266558)). Qed.
Lemma lem2266562 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266563 : term388 = term14.
Proof. exact (@lem2266562 term32). Qed.
Lemma lem2266564 : term428 = term14.
Proof. exact (TRANS (@lem2266560) (@lem2266563)). Qed.
Lemma lem2266565 : term14 = term428.
Proof. exact (SYM (@lem2266564)). Qed.
Lemma lem2266566 : term427 = term428.
Proof. exact (TRANS (@lem2266550) (@lem2266565)). Qed.
Lemma lem2266567 : term413 = term180.
Proof. exact (@lem2266517 (@lem2266566)). Qed.
Lemma lem2266568 : term412 = term180.
Proof. exact (TRANS (@lem2266483) (@lem2266567)). Qed.
Lemma lem2266570 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2266571 : term180 = term14.
Proof. exact (@lem2266570 term14). Qed.
Lemma lem2266572 : term412 = term14.
Proof. exact (TRANS (@lem2266568) (@lem2266571)). Qed.
Lemma lem2266573 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266574 : term429 = term426.
Proof. exact (MK_COMB (@lem2266573) (@lem2266572)). Qed.
Lemma lem2266575 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2266576 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2266574) (@lem2266575 n)). Qed.
Lemma lem2266577 (n : nat) : (term433 n) = (term387 n).
Proof. exact (TRANS (@lem2266474 n) (@lem2266576 n)). Qed.
Lemma lem2266578 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2266579 (n : nat) : (term433 n) = term14.
Proof. exact (TRANS (@lem2266577 n) (@lem2266578 n)). Qed.
Lemma lem2266580 (n : nat) (x : real) : (term623 x n) = (term641 x).
Proof. exact (MK_COMB (@lem2266473 x) (@lem2266579 n)). Qed.
Lemma lem2266581 (n : nat) (x : real) : (term622 x n) = (term641 x).
Proof. exact (TRANS (@lem2266353 x n) (@lem2266580 n x)). Qed.
Lemma lem2266582 (x : real) : (term641 x) = (term569 x).
Proof. exact (@lem1982723 (term569 x)). Qed.
Lemma lem2266583 (n : nat) (x : real) : (term622 x n) = (term569 x).
Proof. exact (TRANS (@lem2266581 n x) (@lem2266582 x)). Qed.
Lemma lem2266584 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2266585 (n : nat) (x : real) : (term642 x n) = (term643 x).
Proof. exact (MK_COMB (@lem2266584) (@lem2266583 n x)). Qed.
Lemma lem2266586 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266587 (n : nat) (x : real) : (term621 x n) = (term644 x).
Proof. exact (MK_COMB (@lem2266585 n x) (@lem2266586)). Qed.
Lemma lem2266588 (x : real) (n : nat) (h1 : term358 x n) : term644 x.
Proof. exact (EQ_MP (@lem2266587 n x) (@lem2266352 x n h1)). Qed.
Lemma lem2266590 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2266591 : term376 = term377.
Proof. exact (@lem2266590 term14 term38). Qed.
Lemma lem2266593 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266594 : term38 = term48.
Proof. exact (@lem2266593 term32). Qed.
Lemma lem2266596 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266597 : term14 = term180.
Proof. exact (@lem2266596 (NUMERAL 0)). Qed.
Lemma lem2266598 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266599 : term378 = term379.
Proof. exact (MK_COMB (@lem2266598) (@lem2266597)). Qed.
Lemma lem2266600 : term377 = term380.
Proof. exact (MK_COMB (@lem2266599) (@lem2266594)). Qed.
Lemma lem2266601 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2266603 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266604 : term377 = term383.
Proof. exact (@lem2266603 (NUMERAL 0) term32). Qed.
Lemma lem2266605 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266606 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266607 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266606 h1) (fun h1 : term383 = True => @lem2266605)). Qed.
Lemma lem2266608 : term383 = True.
Proof. exact (EQ_MP (@lem2266607) (@lem2266605)). Qed.
Lemma lem2266609 : term377 = True.
Proof. exact (TRANS (@lem2266604) (@lem2266608)). Qed.
Lemma lem2266610 : True = term377.
Proof. exact (SYM (@lem2266609)). Qed.
Lemma lem2266611 : term377.
Proof. exact (EQ_MP (@lem2266610) (@lem0)). Qed.
Lemma lem2266612 : term385.
Proof. exact (@lem2266601 (@lem2266611)). Qed.
Lemma lem2266614 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266615 : term377 = term383.
Proof. exact (@lem2266614 (NUMERAL 0) term32). Qed.
Lemma lem2266616 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266617 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266618 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266617 h1) (fun h1 : term383 = True => @lem2266616)). Qed.
Lemma lem2266619 : term383 = True.
Proof. exact (EQ_MP (@lem2266618) (@lem2266616)). Qed.
Lemma lem2266620 : term377 = True.
Proof. exact (TRANS (@lem2266615) (@lem2266619)). Qed.
Lemma lem2266621 : True = term377.
Proof. exact (SYM (@lem2266620)). Qed.
Lemma lem2266622 : term377.
Proof. exact (EQ_MP (@lem2266621) (@lem0)). Qed.
Lemma lem2266623 : term380 = term386.
Proof. exact (@lem2266612 (@lem2266622)). Qed.
Lemma lem2266625 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266626 : term41 = term42.
Proof. exact (@lem2266625 term32 term32). Qed.
Lemma lem2266627 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266628 : term44 = term32.
Proof. exact (EQ_MP (@lem2266627) (@lem940073)). Qed.
Lemma lem2266629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266630 : term42 = term38.
Proof. exact (MK_COMB (@lem2266629) (@lem2266628)). Qed.
Lemma lem2266631 : term41 = term38.
Proof. exact (TRANS (@lem2266626) (@lem2266630)). Qed.
Lemma lem2266633 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266634 : term388 = term14.
Proof. exact (@lem2266633 term32). Qed.
Lemma lem2266635 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266636 : term389 = term378.
Proof. exact (MK_COMB (@lem2266635) (@lem2266634)). Qed.
Lemma lem2266637 : term386 = term377.
Proof. exact (MK_COMB (@lem2266636) (@lem2266631)). Qed.
Lemma lem2266639 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266640 : term377 = term383.
Proof. exact (@lem2266639 (NUMERAL 0) term32). Qed.
Lemma lem2266641 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266642 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266643 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266642 h1) (fun h1 : term383 = True => @lem2266641)). Qed.
Lemma lem2266644 : term383 = True.
Proof. exact (EQ_MP (@lem2266643) (@lem2266641)). Qed.
Lemma lem2266645 : term377 = True.
Proof. exact (TRANS (@lem2266640) (@lem2266644)). Qed.
Lemma lem2266646 : term386 = True.
Proof. exact (TRANS (@lem2266637) (@lem2266645)). Qed.
Lemma lem2266647 : term380 = True.
Proof. exact (TRANS (@lem2266623) (@lem2266646)). Qed.
Lemma lem2266648 : term377 = True.
Proof. exact (TRANS (@lem2266600) (@lem2266647)). Qed.
Lemma lem2266649 : term376 = True.
Proof. exact (TRANS (@lem2266591) (@lem2266648)). Qed.
Lemma lem2266650 : True = term376.
Proof. exact (SYM (@lem2266649)). Qed.
Lemma lem2266651 : term376.
Proof. exact (EQ_MP (@lem2266650) (@lem0)). Qed.
Lemma lem2266652 (x : real) (n : nat) (h1 : term358 x n) : term645 x.
Proof. exact (conj (@lem2266651) (@lem2266588 x n h1)). Qed.
Lemma lem2266654 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2266655 (x : real) : term646 x.
Proof. exact (@lem2266654 term38 (term569 x)). Qed.
Lemma lem2266656 (x : real) (n : nat) (h1 : term358 x n) : term647 x.
Proof. exact (@lem2266655 x (@lem2266652 x n h1)). Qed.
Lemma lem2266657 (x : real) : (term648 x) = (term569 x).
Proof. exact (@lem1982733 (term569 x)). Qed.
Lemma lem2266658 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2266659 (x : real) : (term649 x) = (term643 x).
Proof. exact (MK_COMB (@lem2266658) (@lem2266657 x)). Qed.
Lemma lem2266660 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266661 (x : real) : (term647 x) = (term644 x).
Proof. exact (MK_COMB (@lem2266659 x) (@lem2266660)). Qed.
Lemma lem2266662 (x : real) (n : nat) (h1 : term358 x n) : term644 x.
Proof. exact (EQ_MP (@lem2266661 x) (@lem2266656 x n h1)). Qed.
Lemma lem2266663 (x : real) (n : nat) (h1 : term358 x n) : term650 x.
Proof. exact (conj (@lem2266662 x n h1) (@lem2266260 x n h1)). Qed.
Lemma lem2266665 (x : real) (y : real) : term567 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem2266666 (x : real) : term651 x.
Proof. exact (@lem2266665 (term569 x) (term554 x)). Qed.
Lemma lem2266667 (x : real) (n : nat) (h1 : term358 x n) : term652 x.
Proof. exact (@lem2266666 x (@lem2266663 x n h1)). Qed.
Lemma lem2266668 (x : real) : (term653 x) = (term654 x).
Proof. exact (@lem1982711 term510 term537 x). Qed.
Lemma lem2266670 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2266671 : term537 = term552.
Proof. exact (@lem2266670 term512). Qed.
Lemma lem2266673 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266674 : term510 = term511.
Proof. exact (@lem2266673 term512). Qed.
Lemma lem2266675 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266676 : term655 = term656.
Proof. exact (MK_COMB (@lem2266675) (@lem2266674)). Qed.
Lemma lem2266677 : term657 = term658.
Proof. exact (MK_COMB (@lem2266676) (@lem2266671)). Qed.
Lemma lem2266678 : term659.
Proof. exact (@lem1981473 term510 term38 term537 term38 term14 term38). Qed.
Lemma lem2266680 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266681 : term377 = term383.
Proof. exact (@lem2266680 (NUMERAL 0) term32). Qed.
Lemma lem2266682 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266683 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266684 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266683 h1) (fun h1 : term383 = True => @lem2266682)). Qed.
Lemma lem2266685 : term383 = True.
Proof. exact (EQ_MP (@lem2266684) (@lem2266682)). Qed.
Lemma lem2266686 : term377 = True.
Proof. exact (TRANS (@lem2266681) (@lem2266685)). Qed.
Lemma lem2266687 : True = term377.
Proof. exact (SYM (@lem2266686)). Qed.
Lemma lem2266688 : term377.
Proof. exact (EQ_MP (@lem2266687) (@lem0)). Qed.
Lemma lem2266689 : term660.
Proof. exact (@lem2266678 (@lem2266688)). Qed.
Lemma lem2266691 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266692 : term377 = term383.
Proof. exact (@lem2266691 (NUMERAL 0) term32). Qed.
Lemma lem2266693 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266694 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266695 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266694 h1) (fun h1 : term383 = True => @lem2266693)). Qed.
Lemma lem2266696 : term383 = True.
Proof. exact (EQ_MP (@lem2266695) (@lem2266693)). Qed.
Lemma lem2266697 : term377 = True.
Proof. exact (TRANS (@lem2266692) (@lem2266696)). Qed.
Lemma lem2266698 : True = term377.
Proof. exact (SYM (@lem2266697)). Qed.
Lemma lem2266699 : term377.
Proof. exact (EQ_MP (@lem2266698) (@lem0)). Qed.
Lemma lem2266700 : term661.
Proof. exact (@lem2266689 (@lem2266699)). Qed.
Lemma lem2266702 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266703 : term377 = term383.
Proof. exact (@lem2266702 (NUMERAL 0) term32). Qed.
Lemma lem2266704 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266705 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266706 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266705 h1) (fun h1 : term383 = True => @lem2266704)). Qed.
Lemma lem2266707 : term383 = True.
Proof. exact (EQ_MP (@lem2266706) (@lem2266704)). Qed.
Lemma lem2266708 : term377 = True.
Proof. exact (TRANS (@lem2266703) (@lem2266707)). Qed.
Lemma lem2266709 : True = term377.
Proof. exact (SYM (@lem2266708)). Qed.
Lemma lem2266710 : term377.
Proof. exact (EQ_MP (@lem2266709) (@lem0)). Qed.
Lemma lem2266711 : term662.
Proof. exact (@lem2266700 (@lem2266710)). Qed.
Lemma lem2266713 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2266714 : term549 = term550.
Proof. exact (@lem2266713 term512 term32). Qed.
Lemma lem2266715 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2266716 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2266717 : term521 = term512.
Proof. exact (EQ_MP (@lem2266716) (@lem2266715)). Qed.
Lemma lem2266718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266719 : term518 = term510.
Proof. exact (MK_COMB (@lem2266718) (@lem2266717)). Qed.
Lemma lem2266720 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2266721 : term550 = term537.
Proof. exact (MK_COMB (@lem2266720) (@lem2266719)). Qed.
Lemma lem2266722 : term549 = term537.
Proof. exact (TRANS (@lem2266714) (@lem2266721)). Qed.
Lemma lem2266724 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266725 : term517 = term518.
Proof. exact (@lem2266724 term512 term32). Qed.
Lemma lem2266726 : term519 = term520.
Proof. exact (@lem996237 term520). Qed.
Lemma lem2266727 : (term519 = term520) = (term521 = term512).
Proof. exact (@lem1007663 term520 (BIT1 0) term520). Qed.
Lemma lem2266728 : term521 = term512.
Proof. exact (EQ_MP (@lem2266727) (@lem2266726)). Qed.
Lemma lem2266729 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266730 : term518 = term510.
Proof. exact (MK_COMB (@lem2266729) (@lem2266728)). Qed.
Lemma lem2266731 : term517 = term510.
Proof. exact (TRANS (@lem2266725) (@lem2266730)). Qed.
Lemma lem2266732 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266733 : term663 = term655.
Proof. exact (MK_COMB (@lem2266732) (@lem2266731)). Qed.
Lemma lem2266734 : term664 = term657.
Proof. exact (MK_COMB (@lem2266733) (@lem2266722)). Qed.
Lemma lem2266736 (m : nat) : (term665 m) = term14.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2266737 : term657 = term14.
Proof. exact (@lem2266736 term512). Qed.
Lemma lem2266738 : term664 = term14.
Proof. exact (TRANS (@lem2266734) (@lem2266737)). Qed.
Lemma lem2266739 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266740 : term666 = term426.
Proof. exact (MK_COMB (@lem2266739) (@lem2266738)). Qed.
Lemma lem2266741 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2266742 : term667 = term388.
Proof. exact (MK_COMB (@lem2266740) (@lem2266741)). Qed.
Lemma lem2266744 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266745 : term388 = term14.
Proof. exact (@lem2266744 term32). Qed.
Lemma lem2266746 : term667 = term14.
Proof. exact (TRANS (@lem2266742) (@lem2266745)). Qed.
Lemma lem2266748 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266749 : term41 = term42.
Proof. exact (@lem2266748 term32 term32). Qed.
Lemma lem2266750 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266751 : term44 = term32.
Proof. exact (EQ_MP (@lem2266750) (@lem940073)). Qed.
Lemma lem2266752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266753 : term42 = term38.
Proof. exact (MK_COMB (@lem2266752) (@lem2266751)). Qed.
Lemma lem2266754 : term41 = term38.
Proof. exact (TRANS (@lem2266749) (@lem2266753)). Qed.
Lemma lem2266755 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2266756 : term428 = term388.
Proof. exact (MK_COMB (@lem2266755) (@lem2266754)). Qed.
Lemma lem2266758 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266759 : term388 = term14.
Proof. exact (@lem2266758 term32). Qed.
Lemma lem2266760 : term428 = term14.
Proof. exact (TRANS (@lem2266756) (@lem2266759)). Qed.
Lemma lem2266761 : term14 = term428.
Proof. exact (SYM (@lem2266760)). Qed.
Lemma lem2266762 : term667 = term428.
Proof. exact (TRANS (@lem2266746) (@lem2266761)). Qed.
Lemma lem2266763 : term658 = term180.
Proof. exact (@lem2266711 (@lem2266762)). Qed.
Lemma lem2266764 : term657 = term180.
Proof. exact (TRANS (@lem2266677) (@lem2266763)). Qed.
Lemma lem2266766 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2266767 : term180 = term14.
Proof. exact (@lem2266766 term14). Qed.
Lemma lem2266768 : term657 = term14.
Proof. exact (TRANS (@lem2266764) (@lem2266767)). Qed.
Lemma lem2266769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2266770 : term668 = term426.
Proof. exact (MK_COMB (@lem2266769) (@lem2266768)). Qed.
Lemma lem2266771 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2266772 (x : real) : (term654 x) = (term430 x).
Proof. exact (MK_COMB (@lem2266770) (@lem2266771 x)). Qed.
Lemma lem2266773 (x : real) : (term653 x) = (term430 x).
Proof. exact (TRANS (@lem2266668 x) (@lem2266772 x)). Qed.
Lemma lem2266774 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2266775 (x : real) : (term653 x) = term14.
Proof. exact (TRANS (@lem2266773 x) (@lem2266774 x)). Qed.
Lemma lem2266776 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2266777 (x : real) : (term669 x) = term437.
Proof. exact (MK_COMB (@lem2266776) (@lem2266775 x)). Qed.
Lemma lem2266778 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266779 (x : real) : (term652 x) = term438.
Proof. exact (MK_COMB (@lem2266777 x) (@lem2266778)). Qed.
Lemma lem2266780 (x : real) (n : nat) (h1 : term358 x n) : term438.
Proof. exact (EQ_MP (@lem2266779 x) (@lem2266667 x n h1)). Qed.
Lemma lem2266782 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2266783 : term438 = term439.
Proof. exact (@lem2266782 term14 term14). Qed.
Lemma lem2266785 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266786 : term14 = term180.
Proof. exact (@lem2266785 (NUMERAL 0)). Qed.
Lemma lem2266788 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266789 : term14 = term180.
Proof. exact (@lem2266788 (NUMERAL 0)). Qed.
Lemma lem2266790 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266791 : term378 = term379.
Proof. exact (MK_COMB (@lem2266790) (@lem2266789)). Qed.
Lemma lem2266792 : term439 = term440.
Proof. exact (MK_COMB (@lem2266791) (@lem2266786)). Qed.
Lemma lem2266793 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2266795 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266796 : term377 = term383.
Proof. exact (@lem2266795 (NUMERAL 0) term32). Qed.
Lemma lem2266797 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266798 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266799 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266798 h1) (fun h1 : term383 = True => @lem2266797)). Qed.
Lemma lem2266800 : term383 = True.
Proof. exact (EQ_MP (@lem2266799) (@lem2266797)). Qed.
Lemma lem2266801 : term377 = True.
Proof. exact (TRANS (@lem2266796) (@lem2266800)). Qed.
Lemma lem2266802 : True = term377.
Proof. exact (SYM (@lem2266801)). Qed.
Lemma lem2266803 : term377.
Proof. exact (EQ_MP (@lem2266802) (@lem0)). Qed.
Lemma lem2266804 : term442.
Proof. exact (@lem2266793 (@lem2266803)). Qed.
Lemma lem2266806 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266807 : term377 = term383.
Proof. exact (@lem2266806 (NUMERAL 0) term32). Qed.
Lemma lem2266808 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266809 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266810 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266809 h1) (fun h1 : term383 = True => @lem2266808)). Qed.
Lemma lem2266811 : term383 = True.
Proof. exact (EQ_MP (@lem2266810) (@lem2266808)). Qed.
Lemma lem2266812 : term377 = True.
Proof. exact (TRANS (@lem2266807) (@lem2266811)). Qed.
Lemma lem2266813 : True = term377.
Proof. exact (SYM (@lem2266812)). Qed.
Lemma lem2266814 : term377.
Proof. exact (EQ_MP (@lem2266813) (@lem0)). Qed.
Lemma lem2266815 : term440 = term443.
Proof. exact (@lem2266804 (@lem2266814)). Qed.
Lemma lem2266817 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266818 : term388 = term14.
Proof. exact (@lem2266817 term32). Qed.
Lemma lem2266820 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266821 : term388 = term14.
Proof. exact (@lem2266820 term32). Qed.
Lemma lem2266822 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266823 : term389 = term378.
Proof. exact (MK_COMB (@lem2266822) (@lem2266821)). Qed.
Lemma lem2266824 : term443 = term439.
Proof. exact (MK_COMB (@lem2266823) (@lem2266818)). Qed.
Lemma lem2266826 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266827 : term439 = term444.
Proof. exact (@lem2266826 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2266828 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2266829 : term439 = False.
Proof. exact (TRANS (@lem2266827) (@lem2266828)). Qed.
Lemma lem2266830 : term443 = False.
Proof. exact (TRANS (@lem2266824) (@lem2266829)). Qed.
Lemma lem2266831 : term440 = False.
Proof. exact (TRANS (@lem2266815) (@lem2266830)). Qed.
Lemma lem2266832 : term439 = False.
Proof. exact (TRANS (@lem2266792) (@lem2266831)). Qed.
Lemma lem2266833 : term438 = False.
Proof. exact (TRANS (@lem2266783) (@lem2266832)). Qed.
Lemma lem2266834 (x : real) (n : nat) (h1 : term358 x n) : False.
Proof. exact (EQ_MP (@lem2266833) (@lem2266780 x n h1)). Qed.
Lemma lem2266835 (x : real) (n : nat) (h1 : term365 x n) : term365 x n.
Proof. exact (h1). Qed.
Lemma lem2266836 (x : real) (n : nat) (h1 : term365 x n) : term364 x n.
Proof. exact (proj2 (@lem2266835 x n h1)). Qed.
Lemma lem2266838 (x : real) (n : nat) (h1 : term365 x n) : (term72 x n) = term14.
Proof. exact (proj2 (@lem2266836 x n h1)). Qed.
Lemma lem2266839 (x : real) (n : nat) (h1 : term365 x n) : term81 x n.
Proof. exact (proj1 (@lem2266836 x n h1)). Qed.
Lemma lem2266842 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2266843 : term376 = term377.
Proof. exact (@lem2266842 term14 term38). Qed.
Lemma lem2266845 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266846 : term38 = term48.
Proof. exact (@lem2266845 term32). Qed.
Lemma lem2266848 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266849 : term14 = term180.
Proof. exact (@lem2266848 (NUMERAL 0)). Qed.
Lemma lem2266850 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266851 : term378 = term379.
Proof. exact (MK_COMB (@lem2266850) (@lem2266849)). Qed.
Lemma lem2266852 : term377 = term380.
Proof. exact (MK_COMB (@lem2266851) (@lem2266846)). Qed.
Lemma lem2266853 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2266855 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266856 : term377 = term383.
Proof. exact (@lem2266855 (NUMERAL 0) term32). Qed.
Lemma lem2266857 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266858 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266859 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266858 h1) (fun h1 : term383 = True => @lem2266857)). Qed.
Lemma lem2266860 : term383 = True.
Proof. exact (EQ_MP (@lem2266859) (@lem2266857)). Qed.
Lemma lem2266861 : term377 = True.
Proof. exact (TRANS (@lem2266856) (@lem2266860)). Qed.
Lemma lem2266862 : True = term377.
Proof. exact (SYM (@lem2266861)). Qed.
Lemma lem2266863 : term377.
Proof. exact (EQ_MP (@lem2266862) (@lem0)). Qed.
Lemma lem2266864 : term385.
Proof. exact (@lem2266853 (@lem2266863)). Qed.
Lemma lem2266866 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266867 : term377 = term383.
Proof. exact (@lem2266866 (NUMERAL 0) term32). Qed.
Lemma lem2266868 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266869 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266870 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266869 h1) (fun h1 : term383 = True => @lem2266868)). Qed.
Lemma lem2266871 : term383 = True.
Proof. exact (EQ_MP (@lem2266870) (@lem2266868)). Qed.
Lemma lem2266872 : term377 = True.
Proof. exact (TRANS (@lem2266867) (@lem2266871)). Qed.
Lemma lem2266873 : True = term377.
Proof. exact (SYM (@lem2266872)). Qed.
Lemma lem2266874 : term377.
Proof. exact (EQ_MP (@lem2266873) (@lem0)). Qed.
Lemma lem2266875 : term380 = term386.
Proof. exact (@lem2266864 (@lem2266874)). Qed.
Lemma lem2266877 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266878 : term41 = term42.
Proof. exact (@lem2266877 term32 term32). Qed.
Lemma lem2266879 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266880 : term44 = term32.
Proof. exact (EQ_MP (@lem2266879) (@lem940073)). Qed.
Lemma lem2266881 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266882 : term42 = term38.
Proof. exact (MK_COMB (@lem2266881) (@lem2266880)). Qed.
Lemma lem2266883 : term41 = term38.
Proof. exact (TRANS (@lem2266878) (@lem2266882)). Qed.
Lemma lem2266885 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2266886 : term388 = term14.
Proof. exact (@lem2266885 term32). Qed.
Lemma lem2266887 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2266888 : term389 = term378.
Proof. exact (MK_COMB (@lem2266887) (@lem2266886)). Qed.
Lemma lem2266889 : term386 = term377.
Proof. exact (MK_COMB (@lem2266888) (@lem2266883)). Qed.
Lemma lem2266891 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266892 : term377 = term383.
Proof. exact (@lem2266891 (NUMERAL 0) term32). Qed.
Lemma lem2266893 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266894 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266895 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266894 h1) (fun h1 : term383 = True => @lem2266893)). Qed.
Lemma lem2266896 : term383 = True.
Proof. exact (EQ_MP (@lem2266895) (@lem2266893)). Qed.
Lemma lem2266897 : term377 = True.
Proof. exact (TRANS (@lem2266892) (@lem2266896)). Qed.
Lemma lem2266898 : term386 = True.
Proof. exact (TRANS (@lem2266889) (@lem2266897)). Qed.
Lemma lem2266899 : term380 = True.
Proof. exact (TRANS (@lem2266875) (@lem2266898)). Qed.
Lemma lem2266900 : term377 = True.
Proof. exact (TRANS (@lem2266852) (@lem2266899)). Qed.
Lemma lem2266901 : term376 = True.
Proof. exact (TRANS (@lem2266843) (@lem2266900)). Qed.
Lemma lem2266902 : True = term376.
Proof. exact (SYM (@lem2266901)). Qed.
Lemma lem2266903 : term376.
Proof. exact (EQ_MP (@lem2266902) (@lem0)). Qed.
Lemma lem2266904 (x : real) (n : nat) (h1 : term365 x n) : term477 x n.
Proof. exact (conj (@lem2266903) (@lem2266839 x n h1)). Qed.
Lemma lem2266906 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2266907 (x : real) (n : nat) : term478 x n.
Proof. exact (@lem2266906 term38 (term76 x n)). Qed.
Lemma lem2266908 (x : real) (n : nat) (h1 : term365 x n) : term479 x n.
Proof. exact (@lem2266907 x n (@lem2266904 x n h1)). Qed.
Lemma lem2266909 (x : real) (n : nat) : (term453 x n) = (term76 x n).
Proof. exact (@lem1982733 (term76 x n)). Qed.
Lemma lem2266910 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2266911 (x : real) (n : nat) : (term480 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem2266910) (@lem2266909 x n)). Qed.
Lemma lem2266912 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266913 (x : real) (n : nat) : (term479 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2266911 x n) (@lem2266912)). Qed.
Lemma lem2266914 (x : real) (n : nat) (h1 : term365 x n) : term81 x n.
Proof. exact (EQ_MP (@lem2266913 x n) (@lem2266908 x n h1)). Qed.
Lemma lem2266916 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2266917 (x : real) (n : nat) : term587 x n.
Proof. exact (@lem2266916 (term72 x n)). Qed.
Lemma lem2266918 (x : real) (n : nat) (h1 : term365 x n) : term588 x n.
Proof. exact (@lem2266917 x n (@lem2266838 x n h1)). Qed.
Lemma lem2266919 (x : real) (n : nat) (h1 : term365 x n) : term617 x n.
Proof. exact (@lem2266918 x n h1 term38). Qed.
Lemma lem2266920 (x : real) (n : nat) : (term617 x n) = ((term448 x n) = term14).
Proof. exact (eq_refl (term617 x n)). Qed.
Lemma lem2266921 (x : real) (n : nat) (h1 : term365 x n) : (term448 x n) = term14.
Proof. exact (EQ_MP (@lem2266920 x n) (@lem2266919 x n h1)). Qed.
Lemma lem2266922 (x : real) (n : nat) : (term448 x n) = (term72 x n).
Proof. exact (@lem1982733 (term72 x n)). Qed.
Lemma lem2266923 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2266924 (x : real) (n : nat) : (term618 x n) = (term117 x n).
Proof. exact (MK_COMB (@lem2266923) (@lem2266922 x n)). Qed.
Lemma lem2266925 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2266926 (x : real) (n : nat) : ((term448 x n) = term14) = ((term72 x n) = term14).
Proof. exact (MK_COMB (@lem2266924 x n) (@lem2266925)). Qed.
Lemma lem2266927 (x : real) (n : nat) (h1 : term365 x n) : (term72 x n) = term14.
Proof. exact (EQ_MP (@lem2266926 x n) (@lem2266921 x n h1)). Qed.
Lemma lem2266928 (x : real) (n : nat) (h1 : term365 x n) : term488 x n.
Proof. exact (conj (@lem2266927 x n h1) (@lem2266914 x n h1)). Qed.
Lemma lem2266930 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2266931 (x : real) (n : nat) : term489 x n.
Proof. exact (@lem2266930 (term72 x n) (term76 x n)). Qed.
Lemma lem2266932 (x : real) (n : nat) (h1 : term365 x n) : term490 x n.
Proof. exact (@lem2266931 x n (@lem2266928 x n h1)). Qed.
Lemma lem2266933 (x : real) (n : nat) : (term491 x n) = (term492 x n).
Proof. exact (@lem1982753 x (term208 x) (real_of_num n) (term27 n)). Qed.
Lemma lem2266934 (x : real) : (term474 x) = (term409 x).
Proof. exact (@lem1982715 term26 x). Qed.
Lemma lem2266936 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2266937 : term38 = term48.
Proof. exact (@lem2266936 term32). Qed.
Lemma lem2266939 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2266940 : term26 = term31.
Proof. exact (@lem2266939 term32). Qed.
Lemma lem2266941 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266942 : term410 = term411.
Proof. exact (MK_COMB (@lem2266941) (@lem2266940)). Qed.
Lemma lem2266943 : term412 = term413.
Proof. exact (MK_COMB (@lem2266942) (@lem2266937)). Qed.
Lemma lem2266944 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2266946 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266947 : term377 = term383.
Proof. exact (@lem2266946 (NUMERAL 0) term32). Qed.
Lemma lem2266948 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266949 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266950 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266949 h1) (fun h1 : term383 = True => @lem2266948)). Qed.
Lemma lem2266951 : term383 = True.
Proof. exact (EQ_MP (@lem2266950) (@lem2266948)). Qed.
Lemma lem2266952 : term377 = True.
Proof. exact (TRANS (@lem2266947) (@lem2266951)). Qed.
Lemma lem2266953 : True = term377.
Proof. exact (SYM (@lem2266952)). Qed.
Lemma lem2266954 : term377.
Proof. exact (EQ_MP (@lem2266953) (@lem0)). Qed.
Lemma lem2266955 : term415.
Proof. exact (@lem2266944 (@lem2266954)). Qed.
Lemma lem2266957 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266958 : term377 = term383.
Proof. exact (@lem2266957 (NUMERAL 0) term32). Qed.
Lemma lem2266959 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266960 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266961 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266960 h1) (fun h1 : term383 = True => @lem2266959)). Qed.
Lemma lem2266962 : term383 = True.
Proof. exact (EQ_MP (@lem2266961) (@lem2266959)). Qed.
Lemma lem2266963 : term377 = True.
Proof. exact (TRANS (@lem2266958) (@lem2266962)). Qed.
Lemma lem2266964 : True = term377.
Proof. exact (SYM (@lem2266963)). Qed.
Lemma lem2266965 : term377.
Proof. exact (EQ_MP (@lem2266964) (@lem0)). Qed.
Lemma lem2266966 : term416.
Proof. exact (@lem2266955 (@lem2266965)). Qed.
Lemma lem2266968 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2266969 : term377 = term383.
Proof. exact (@lem2266968 (NUMERAL 0) term32). Qed.
Lemma lem2266970 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2266971 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2266972 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2266971 h1) (fun h1 : term383 = True => @lem2266970)). Qed.
Lemma lem2266973 : term383 = True.
Proof. exact (EQ_MP (@lem2266972) (@lem2266970)). Qed.
Lemma lem2266974 : term377 = True.
Proof. exact (TRANS (@lem2266969) (@lem2266973)). Qed.
Lemma lem2266975 : True = term377.
Proof. exact (SYM (@lem2266974)). Qed.
Lemma lem2266976 : term377.
Proof. exact (EQ_MP (@lem2266975) (@lem0)). Qed.
Lemma lem2266977 : term417.
Proof. exact (@lem2266966 (@lem2266976)). Qed.
Lemma lem2266979 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2266980 : term41 = term42.
Proof. exact (@lem2266979 term32 term32). Qed.
Lemma lem2266981 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266982 : term44 = term32.
Proof. exact (EQ_MP (@lem2266981) (@lem940073)). Qed.
Lemma lem2266983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266984 : term42 = term38.
Proof. exact (MK_COMB (@lem2266983) (@lem2266982)). Qed.
Lemma lem2266985 : term41 = term38.
Proof. exact (TRANS (@lem2266980) (@lem2266984)). Qed.
Lemma lem2266987 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2266988 : term420 = term421.
Proof. exact (@lem2266987 term32 term32). Qed.
Lemma lem2266989 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2266990 : term44 = term32.
Proof. exact (EQ_MP (@lem2266989) (@lem940073)). Qed.
Lemma lem2266991 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2266992 : term42 = term38.
Proof. exact (MK_COMB (@lem2266991) (@lem2266990)). Qed.
Lemma lem2266993 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2266994 : term421 = term26.
Proof. exact (MK_COMB (@lem2266993) (@lem2266992)). Qed.
Lemma lem2266995 : term420 = term26.
Proof. exact (TRANS (@lem2266988) (@lem2266994)). Qed.
Lemma lem2266996 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2266997 : term422 = term410.
Proof. exact (MK_COMB (@lem2266996) (@lem2266995)). Qed.
Lemma lem2266998 : term423 = term412.
Proof. exact (MK_COMB (@lem2266997) (@lem2266985)). Qed.
Lemma lem2267000 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2267001 : term412 = term14.
Proof. exact (@lem2267000 term32). Qed.
Lemma lem2267002 : term423 = term14.
Proof. exact (TRANS (@lem2266998) (@lem2267001)). Qed.
Lemma lem2267003 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2267004 : term425 = term426.
Proof. exact (MK_COMB (@lem2267003) (@lem2267002)). Qed.
Lemma lem2267005 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2267006 : term427 = term388.
Proof. exact (MK_COMB (@lem2267004) (@lem2267005)). Qed.
Lemma lem2267008 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267009 : term388 = term14.
Proof. exact (@lem2267008 term32). Qed.
Lemma lem2267010 : term427 = term14.
Proof. exact (TRANS (@lem2267006) (@lem2267009)). Qed.
Lemma lem2267012 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2267013 : term41 = term42.
Proof. exact (@lem2267012 term32 term32). Qed.
Lemma lem2267014 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267015 : term44 = term32.
Proof. exact (EQ_MP (@lem2267014) (@lem940073)). Qed.
Lemma lem2267016 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267017 : term42 = term38.
Proof. exact (MK_COMB (@lem2267016) (@lem2267015)). Qed.
Lemma lem2267018 : term41 = term38.
Proof. exact (TRANS (@lem2267013) (@lem2267017)). Qed.
Lemma lem2267019 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2267020 : term428 = term388.
Proof. exact (MK_COMB (@lem2267019) (@lem2267018)). Qed.
Lemma lem2267022 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267023 : term388 = term14.
Proof. exact (@lem2267022 term32). Qed.
Lemma lem2267024 : term428 = term14.
Proof. exact (TRANS (@lem2267020) (@lem2267023)). Qed.
Lemma lem2267025 : term14 = term428.
Proof. exact (SYM (@lem2267024)). Qed.
Lemma lem2267026 : term427 = term428.
Proof. exact (TRANS (@lem2267010) (@lem2267025)). Qed.
Lemma lem2267027 : term413 = term180.
Proof. exact (@lem2266977 (@lem2267026)). Qed.
Lemma lem2267028 : term412 = term180.
Proof. exact (TRANS (@lem2266943) (@lem2267027)). Qed.
Lemma lem2267030 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2267031 : term180 = term14.
Proof. exact (@lem2267030 term14). Qed.
Lemma lem2267032 : term412 = term14.
Proof. exact (TRANS (@lem2267028) (@lem2267031)). Qed.
Lemma lem2267033 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2267034 : term429 = term426.
Proof. exact (MK_COMB (@lem2267033) (@lem2267032)). Qed.
Lemma lem2267035 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2267036 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2267034) (@lem2267035 x)). Qed.
Lemma lem2267037 (x : real) : (term474 x) = (term430 x).
Proof. exact (TRANS (@lem2266934 x) (@lem2267036 x)). Qed.
Lemma lem2267038 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2267039 (x : real) : (term474 x) = term14.
Proof. exact (TRANS (@lem2267037 x) (@lem2267038 x)). Qed.
Lemma lem2267040 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2267041 (x : real) : (term475 x) = term432.
Proof. exact (MK_COMB (@lem2267040) (@lem2267039 x)). Qed.
Lemma lem2267042 (n : nat) : (term433 n) = (term434 n).
Proof. exact (@lem1982715 term26 (real_of_num n)). Qed.
Lemma lem2267044 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267045 : term38 = term48.
Proof. exact (@lem2267044 term32). Qed.
Lemma lem2267047 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2267048 : term26 = term31.
Proof. exact (@lem2267047 term32). Qed.
Lemma lem2267049 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2267050 : term410 = term411.
Proof. exact (MK_COMB (@lem2267049) (@lem2267048)). Qed.
Lemma lem2267051 : term412 = term413.
Proof. exact (MK_COMB (@lem2267050) (@lem2267045)). Qed.
Lemma lem2267052 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2267054 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267055 : term377 = term383.
Proof. exact (@lem2267054 (NUMERAL 0) term32). Qed.
Lemma lem2267056 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267057 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267058 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267057 h1) (fun h1 : term383 = True => @lem2267056)). Qed.
Lemma lem2267059 : term383 = True.
Proof. exact (EQ_MP (@lem2267058) (@lem2267056)). Qed.
Lemma lem2267060 : term377 = True.
Proof. exact (TRANS (@lem2267055) (@lem2267059)). Qed.
Lemma lem2267061 : True = term377.
Proof. exact (SYM (@lem2267060)). Qed.
Lemma lem2267062 : term377.
Proof. exact (EQ_MP (@lem2267061) (@lem0)). Qed.
Lemma lem2267063 : term415.
Proof. exact (@lem2267052 (@lem2267062)). Qed.
Lemma lem2267065 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267066 : term377 = term383.
Proof. exact (@lem2267065 (NUMERAL 0) term32). Qed.
Lemma lem2267067 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267068 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267069 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267068 h1) (fun h1 : term383 = True => @lem2267067)). Qed.
Lemma lem2267070 : term383 = True.
Proof. exact (EQ_MP (@lem2267069) (@lem2267067)). Qed.
Lemma lem2267071 : term377 = True.
Proof. exact (TRANS (@lem2267066) (@lem2267070)). Qed.
Lemma lem2267072 : True = term377.
Proof. exact (SYM (@lem2267071)). Qed.
Lemma lem2267073 : term377.
Proof. exact (EQ_MP (@lem2267072) (@lem0)). Qed.
Lemma lem2267074 : term416.
Proof. exact (@lem2267063 (@lem2267073)). Qed.
Lemma lem2267076 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267077 : term377 = term383.
Proof. exact (@lem2267076 (NUMERAL 0) term32). Qed.
Lemma lem2267078 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267079 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267080 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267079 h1) (fun h1 : term383 = True => @lem2267078)). Qed.
Lemma lem2267081 : term383 = True.
Proof. exact (EQ_MP (@lem2267080) (@lem2267078)). Qed.
Lemma lem2267082 : term377 = True.
Proof. exact (TRANS (@lem2267077) (@lem2267081)). Qed.
Lemma lem2267083 : True = term377.
Proof. exact (SYM (@lem2267082)). Qed.
Lemma lem2267084 : term377.
Proof. exact (EQ_MP (@lem2267083) (@lem0)). Qed.
Lemma lem2267085 : term417.
Proof. exact (@lem2267074 (@lem2267084)). Qed.
Lemma lem2267087 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2267088 : term41 = term42.
Proof. exact (@lem2267087 term32 term32). Qed.
Lemma lem2267089 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267090 : term44 = term32.
Proof. exact (EQ_MP (@lem2267089) (@lem940073)). Qed.
Lemma lem2267091 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267092 : term42 = term38.
Proof. exact (MK_COMB (@lem2267091) (@lem2267090)). Qed.
Lemma lem2267093 : term41 = term38.
Proof. exact (TRANS (@lem2267088) (@lem2267092)). Qed.
Lemma lem2267095 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2267096 : term420 = term421.
Proof. exact (@lem2267095 term32 term32). Qed.
Lemma lem2267097 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267098 : term44 = term32.
Proof. exact (EQ_MP (@lem2267097) (@lem940073)). Qed.
Lemma lem2267099 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267100 : term42 = term38.
Proof. exact (MK_COMB (@lem2267099) (@lem2267098)). Qed.
Lemma lem2267101 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2267102 : term421 = term26.
Proof. exact (MK_COMB (@lem2267101) (@lem2267100)). Qed.
Lemma lem2267103 : term420 = term26.
Proof. exact (TRANS (@lem2267096) (@lem2267102)). Qed.
Lemma lem2267104 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2267105 : term422 = term410.
Proof. exact (MK_COMB (@lem2267104) (@lem2267103)). Qed.
Lemma lem2267106 : term423 = term412.
Proof. exact (MK_COMB (@lem2267105) (@lem2267093)). Qed.
Lemma lem2267108 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2267109 : term412 = term14.
Proof. exact (@lem2267108 term32). Qed.
Lemma lem2267110 : term423 = term14.
Proof. exact (TRANS (@lem2267106) (@lem2267109)). Qed.
Lemma lem2267111 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2267112 : term425 = term426.
Proof. exact (MK_COMB (@lem2267111) (@lem2267110)). Qed.
Lemma lem2267113 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2267114 : term427 = term388.
Proof. exact (MK_COMB (@lem2267112) (@lem2267113)). Qed.
Lemma lem2267116 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267117 : term388 = term14.
Proof. exact (@lem2267116 term32). Qed.
Lemma lem2267118 : term427 = term14.
Proof. exact (TRANS (@lem2267114) (@lem2267117)). Qed.
Lemma lem2267120 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2267121 : term41 = term42.
Proof. exact (@lem2267120 term32 term32). Qed.
Lemma lem2267122 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267123 : term44 = term32.
Proof. exact (EQ_MP (@lem2267122) (@lem940073)). Qed.
Lemma lem2267124 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267125 : term42 = term38.
Proof. exact (MK_COMB (@lem2267124) (@lem2267123)). Qed.
Lemma lem2267126 : term41 = term38.
Proof. exact (TRANS (@lem2267121) (@lem2267125)). Qed.
Lemma lem2267127 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2267128 : term428 = term388.
Proof. exact (MK_COMB (@lem2267127) (@lem2267126)). Qed.
Lemma lem2267130 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267131 : term388 = term14.
Proof. exact (@lem2267130 term32). Qed.
Lemma lem2267132 : term428 = term14.
Proof. exact (TRANS (@lem2267128) (@lem2267131)). Qed.
Lemma lem2267133 : term14 = term428.
Proof. exact (SYM (@lem2267132)). Qed.
Lemma lem2267134 : term427 = term428.
Proof. exact (TRANS (@lem2267118) (@lem2267133)). Qed.
Lemma lem2267135 : term413 = term180.
Proof. exact (@lem2267085 (@lem2267134)). Qed.
Lemma lem2267136 : term412 = term180.
Proof. exact (TRANS (@lem2267051) (@lem2267135)). Qed.
Lemma lem2267138 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2267139 : term180 = term14.
Proof. exact (@lem2267138 term14). Qed.
Lemma lem2267140 : term412 = term14.
Proof. exact (TRANS (@lem2267136) (@lem2267139)). Qed.
Lemma lem2267141 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2267142 : term429 = term426.
Proof. exact (MK_COMB (@lem2267141) (@lem2267140)). Qed.
Lemma lem2267143 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2267144 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2267142) (@lem2267143 n)). Qed.
Lemma lem2267145 (n : nat) : (term433 n) = (term387 n).
Proof. exact (TRANS (@lem2267042 n) (@lem2267144 n)). Qed.
Lemma lem2267146 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2267147 (n : nat) : (term433 n) = term14.
Proof. exact (TRANS (@lem2267145 n) (@lem2267146 n)). Qed.
Lemma lem2267148 (x : real) (n : nat) : (term492 x n) = term435.
Proof. exact (MK_COMB (@lem2267041 x) (@lem2267147 n)). Qed.
Lemma lem2267149 (x : real) (n : nat) : (term491 x n) = term435.
Proof. exact (TRANS (@lem2266933 x n) (@lem2267148 x n)). Qed.
Lemma lem2267150 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2267151 (x : real) (n : nat) : (term491 x n) = term14.
Proof. exact (TRANS (@lem2267149 x n) (@lem2267150)). Qed.
Lemma lem2267152 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2267153 (x : real) (n : nat) : (term493 x n) = term437.
Proof. exact (MK_COMB (@lem2267152) (@lem2267151 x n)). Qed.
Lemma lem2267154 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2267155 (x : real) (n : nat) : (term490 x n) = term438.
Proof. exact (MK_COMB (@lem2267153 x n) (@lem2267154)). Qed.
Lemma lem2267156 (x : real) (n : nat) (h1 : term365 x n) : term438.
Proof. exact (EQ_MP (@lem2267155 x n) (@lem2266932 x n h1)). Qed.
Lemma lem2267158 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2267159 : term438 = term439.
Proof. exact (@lem2267158 term14 term14). Qed.
Lemma lem2267161 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267162 : term14 = term180.
Proof. exact (@lem2267161 (NUMERAL 0)). Qed.
Lemma lem2267164 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267165 : term14 = term180.
Proof. exact (@lem2267164 (NUMERAL 0)). Qed.
Lemma lem2267166 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2267167 : term378 = term379.
Proof. exact (MK_COMB (@lem2267166) (@lem2267165)). Qed.
Lemma lem2267168 : term439 = term440.
Proof. exact (MK_COMB (@lem2267167) (@lem2267162)). Qed.
Lemma lem2267169 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2267171 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267172 : term377 = term383.
Proof. exact (@lem2267171 (NUMERAL 0) term32). Qed.
Lemma lem2267173 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267174 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267175 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267174 h1) (fun h1 : term383 = True => @lem2267173)). Qed.
Lemma lem2267176 : term383 = True.
Proof. exact (EQ_MP (@lem2267175) (@lem2267173)). Qed.
Lemma lem2267177 : term377 = True.
Proof. exact (TRANS (@lem2267172) (@lem2267176)). Qed.
Lemma lem2267178 : True = term377.
Proof. exact (SYM (@lem2267177)). Qed.
Lemma lem2267179 : term377.
Proof. exact (EQ_MP (@lem2267178) (@lem0)). Qed.
Lemma lem2267180 : term442.
Proof. exact (@lem2267169 (@lem2267179)). Qed.
Lemma lem2267182 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267183 : term377 = term383.
Proof. exact (@lem2267182 (NUMERAL 0) term32). Qed.
Lemma lem2267184 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267185 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267186 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267185 h1) (fun h1 : term383 = True => @lem2267184)). Qed.
Lemma lem2267187 : term383 = True.
Proof. exact (EQ_MP (@lem2267186) (@lem2267184)). Qed.
Lemma lem2267188 : term377 = True.
Proof. exact (TRANS (@lem2267183) (@lem2267187)). Qed.
Lemma lem2267189 : True = term377.
Proof. exact (SYM (@lem2267188)). Qed.
Lemma lem2267190 : term377.
Proof. exact (EQ_MP (@lem2267189) (@lem0)). Qed.
Lemma lem2267191 : term440 = term443.
Proof. exact (@lem2267180 (@lem2267190)). Qed.
Lemma lem2267193 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267194 : term388 = term14.
Proof. exact (@lem2267193 term32). Qed.
Lemma lem2267196 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267197 : term388 = term14.
Proof. exact (@lem2267196 term32). Qed.
Lemma lem2267198 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2267199 : term389 = term378.
Proof. exact (MK_COMB (@lem2267198) (@lem2267197)). Qed.
Lemma lem2267200 : term443 = term439.
Proof. exact (MK_COMB (@lem2267199) (@lem2267194)). Qed.
Lemma lem2267202 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267203 : term439 = term444.
Proof. exact (@lem2267202 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2267204 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2267205 : term439 = False.
Proof. exact (TRANS (@lem2267203) (@lem2267204)). Qed.
Lemma lem2267206 : term443 = False.
Proof. exact (TRANS (@lem2267200) (@lem2267205)). Qed.
Lemma lem2267207 : term440 = False.
Proof. exact (TRANS (@lem2267191) (@lem2267206)). Qed.
Lemma lem2267208 : term439 = False.
Proof. exact (TRANS (@lem2267168) (@lem2267207)). Qed.
Lemma lem2267209 : term438 = False.
Proof. exact (TRANS (@lem2267159) (@lem2267208)). Qed.
Lemma lem2267210 (x : real) (n : nat) (h1 : term365 x n) : False.
Proof. exact (EQ_MP (@lem2267209) (@lem2267156 x n h1)). Qed.
Lemma lem2267211 (x : real) (n : nat) (h1 : term366 x n) : False.
Proof. exact (or_elim (@lem2265921 x n h1) (fun h0 : term358 x n => @lem2266834 x n h0) (fun h0 : term365 x n => @lem2267210 x n h0)). Qed.
Lemma lem2267212 (x : real) (n : nat) (h1 : term368 x n) : term368 x n.
Proof. exact (h1). Qed.
Lemma lem2267213 (x : real) (n : nat) (h1 : term368 x n) : (term72 x n) = term14.
Proof. exact (proj2 (@lem2267212 x n h1)). Qed.
Lemma lem2267214 (x : real) (n : nat) (h1 : term368 x n) : term151 x n.
Proof. exact (proj1 (@lem2267212 x n h1)). Qed.
Lemma lem2267215 (x : real) (n : nat) (h1 : term368 x n) : term85 x n.
Proof. exact (proj2 (@lem2267214 x n h1)). Qed.
Lemma lem2267219 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2267220 : term376 = term377.
Proof. exact (@lem2267219 term14 term38). Qed.
Lemma lem2267222 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267223 : term38 = term48.
Proof. exact (@lem2267222 term32). Qed.
Lemma lem2267225 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267226 : term14 = term180.
Proof. exact (@lem2267225 (NUMERAL 0)). Qed.
Lemma lem2267227 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2267228 : term378 = term379.
Proof. exact (MK_COMB (@lem2267227) (@lem2267226)). Qed.
Lemma lem2267229 : term377 = term380.
Proof. exact (MK_COMB (@lem2267228) (@lem2267223)). Qed.
Lemma lem2267230 : term381.
Proof. exact (@lem1980255 term14 term38 term38 term38). Qed.
Lemma lem2267232 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267233 : term377 = term383.
Proof. exact (@lem2267232 (NUMERAL 0) term32). Qed.
Lemma lem2267234 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267235 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267236 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267235 h1) (fun h1 : term383 = True => @lem2267234)). Qed.
Lemma lem2267237 : term383 = True.
Proof. exact (EQ_MP (@lem2267236) (@lem2267234)). Qed.
Lemma lem2267238 : term377 = True.
Proof. exact (TRANS (@lem2267233) (@lem2267237)). Qed.
Lemma lem2267239 : True = term377.
Proof. exact (SYM (@lem2267238)). Qed.
Lemma lem2267240 : term377.
Proof. exact (EQ_MP (@lem2267239) (@lem0)). Qed.
Lemma lem2267241 : term385.
Proof. exact (@lem2267230 (@lem2267240)). Qed.
Lemma lem2267243 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267244 : term377 = term383.
Proof. exact (@lem2267243 (NUMERAL 0) term32). Qed.
Lemma lem2267245 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267246 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267247 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267246 h1) (fun h1 : term383 = True => @lem2267245)). Qed.
Lemma lem2267248 : term383 = True.
Proof. exact (EQ_MP (@lem2267247) (@lem2267245)). Qed.
Lemma lem2267249 : term377 = True.
Proof. exact (TRANS (@lem2267244) (@lem2267248)). Qed.
Lemma lem2267250 : True = term377.
Proof. exact (SYM (@lem2267249)). Qed.
Lemma lem2267251 : term377.
Proof. exact (EQ_MP (@lem2267250) (@lem0)). Qed.
Lemma lem2267252 : term380 = term386.
Proof. exact (@lem2267241 (@lem2267251)). Qed.
Lemma lem2267254 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2267255 : term41 = term42.
Proof. exact (@lem2267254 term32 term32). Qed.
Lemma lem2267256 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267257 : term44 = term32.
Proof. exact (EQ_MP (@lem2267256) (@lem940073)). Qed.
Lemma lem2267258 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267259 : term42 = term38.
Proof. exact (MK_COMB (@lem2267258) (@lem2267257)). Qed.
Lemma lem2267260 : term41 = term38.
Proof. exact (TRANS (@lem2267255) (@lem2267259)). Qed.
Lemma lem2267262 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267263 : term388 = term14.
Proof. exact (@lem2267262 term32). Qed.
Lemma lem2267264 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2267265 : term389 = term378.
Proof. exact (MK_COMB (@lem2267264) (@lem2267263)). Qed.
Lemma lem2267266 : term386 = term377.
Proof. exact (MK_COMB (@lem2267265) (@lem2267260)). Qed.
Lemma lem2267268 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267269 : term377 = term383.
Proof. exact (@lem2267268 (NUMERAL 0) term32). Qed.
Lemma lem2267270 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267271 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267272 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267271 h1) (fun h1 : term383 = True => @lem2267270)). Qed.
Lemma lem2267273 : term383 = True.
Proof. exact (EQ_MP (@lem2267272) (@lem2267270)). Qed.
Lemma lem2267274 : term377 = True.
Proof. exact (TRANS (@lem2267269) (@lem2267273)). Qed.
Lemma lem2267275 : term386 = True.
Proof. exact (TRANS (@lem2267266) (@lem2267274)). Qed.
Lemma lem2267276 : term380 = True.
Proof. exact (TRANS (@lem2267252) (@lem2267275)). Qed.
Lemma lem2267277 : term377 = True.
Proof. exact (TRANS (@lem2267229) (@lem2267276)). Qed.
Lemma lem2267278 : term376 = True.
Proof. exact (TRANS (@lem2267220) (@lem2267277)). Qed.
Lemma lem2267279 : True = term376.
Proof. exact (SYM (@lem2267278)). Qed.
Lemma lem2267280 : term376.
Proof. exact (EQ_MP (@lem2267279) (@lem0)). Qed.
Lemma lem2267281 (x : real) (n : nat) (h1 : term368 x n) : term445 x n.
Proof. exact (conj (@lem2267280) (@lem2267215 x n h1)). Qed.
Lemma lem2267283 (x : real) (y : real) : term391 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2267284 (x : real) (n : nat) : term446 x n.
Proof. exact (@lem2267283 term38 (term72 x n)). Qed.
Lemma lem2267285 (x : real) (n : nat) (h1 : term368 x n) : term447 x n.
Proof. exact (@lem2267284 x n (@lem2267281 x n h1)). Qed.
Lemma lem2267286 (x : real) (n : nat) : (term448 x n) = (term72 x n).
Proof. exact (@lem1982733 (term72 x n)). Qed.
Lemma lem2267287 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2267288 (x : real) (n : nat) : (term449 x n) = (term83 x n).
Proof. exact (MK_COMB (@lem2267287) (@lem2267286 x n)). Qed.
Lemma lem2267289 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2267290 (x : real) (n : nat) : (term447 x n) = (term85 x n).
Proof. exact (MK_COMB (@lem2267288 x n) (@lem2267289)). Qed.
Lemma lem2267291 (x : real) (n : nat) (h1 : term368 x n) : term85 x n.
Proof. exact (EQ_MP (@lem2267290 x n) (@lem2267285 x n h1)). Qed.
Lemma lem2267293 (y : real) : term396 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2267294 (x : real) (n : nat) : term587 x n.
Proof. exact (@lem2267293 (term72 x n)). Qed.
Lemma lem2267295 (x : real) (n : nat) (h1 : term368 x n) : term588 x n.
Proof. exact (@lem2267294 x n (@lem2267213 x n h1)). Qed.
Lemma lem2267296 (x : real) (n : nat) (h1 : term368 x n) : term589 x n.
Proof. exact (@lem2267295 x n h1 term26). Qed.
Lemma lem2267297 (x : real) (n : nat) : (term589 x n) = ((term75 x n) = term14).
Proof. exact (eq_refl (term589 x n)). Qed.
Lemma lem2267298 (x : real) (n : nat) (h1 : term368 x n) : (term75 x n) = term14.
Proof. exact (EQ_MP (@lem2267297 x n) (@lem2267296 x n h1)). Qed.
Lemma lem2267305 (x : real) (n : nat) : (term75 x n) = (term76 x n).
Proof. exact (@lem1982781 x term26 (real_of_num n)). Qed.
Lemma lem2267306 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2267307 (x : real) (n : nat) : (term590 x n) = (term222 x n).
Proof. exact (MK_COMB (@lem2267306) (@lem2267305 x n)). Qed.
Lemma lem2267308 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2267309 (x : real) (n : nat) : ((term75 x n) = term14) = ((term76 x n) = term14).
Proof. exact (MK_COMB (@lem2267307 x n) (@lem2267308)). Qed.
Lemma lem2267310 (x : real) (n : nat) (h1 : term368 x n) : (term76 x n) = term14.
Proof. exact (EQ_MP (@lem2267309 x n) (@lem2267298 x n h1)). Qed.
Lemma lem2267311 (x : real) (n : nat) (h1 : term368 x n) : term455 x n.
Proof. exact (conj (@lem2267310 x n h1) (@lem2267291 x n h1)). Qed.
Lemma lem2267313 (x : real) (y : real) : term403 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem2267314 (x : real) (n : nat) : term456 x n.
Proof. exact (@lem2267313 (term76 x n) (term72 x n)). Qed.
Lemma lem2267315 (x : real) (n : nat) (h1 : term368 x n) : term457 x n.
Proof. exact (@lem2267314 x n (@lem2267311 x n h1)). Qed.
Lemma lem2267316 (x : real) (n : nat) : (term458 x n) = (term459 x n).
Proof. exact (@lem1982753 (term208 x) x (term27 n) (real_of_num n)). Qed.
Lemma lem2267317 (x : real) : (term408 x) = (term409 x).
Proof. exact (@lem1982713 term26 x). Qed.
Lemma lem2267319 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267320 : term38 = term48.
Proof. exact (@lem2267319 term32). Qed.
Lemma lem2267322 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2267323 : term26 = term31.
Proof. exact (@lem2267322 term32). Qed.
Lemma lem2267324 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2267325 : term410 = term411.
Proof. exact (MK_COMB (@lem2267324) (@lem2267323)). Qed.
Lemma lem2267326 : term412 = term413.
Proof. exact (MK_COMB (@lem2267325) (@lem2267320)). Qed.
Lemma lem2267327 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2267329 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267330 : term377 = term383.
Proof. exact (@lem2267329 (NUMERAL 0) term32). Qed.
Lemma lem2267331 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267332 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267333 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267332 h1) (fun h1 : term383 = True => @lem2267331)). Qed.
Lemma lem2267334 : term383 = True.
Proof. exact (EQ_MP (@lem2267333) (@lem2267331)). Qed.
Lemma lem2267335 : term377 = True.
Proof. exact (TRANS (@lem2267330) (@lem2267334)). Qed.
Lemma lem2267336 : True = term377.
Proof. exact (SYM (@lem2267335)). Qed.
Lemma lem2267337 : term377.
Proof. exact (EQ_MP (@lem2267336) (@lem0)). Qed.
Lemma lem2267338 : term415.
Proof. exact (@lem2267327 (@lem2267337)). Qed.
Lemma lem2267340 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267341 : term377 = term383.
Proof. exact (@lem2267340 (NUMERAL 0) term32). Qed.
Lemma lem2267342 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267343 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267344 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267343 h1) (fun h1 : term383 = True => @lem2267342)). Qed.
Lemma lem2267345 : term383 = True.
Proof. exact (EQ_MP (@lem2267344) (@lem2267342)). Qed.
Lemma lem2267346 : term377 = True.
Proof. exact (TRANS (@lem2267341) (@lem2267345)). Qed.
Lemma lem2267347 : True = term377.
Proof. exact (SYM (@lem2267346)). Qed.
Lemma lem2267348 : term377.
Proof. exact (EQ_MP (@lem2267347) (@lem0)). Qed.
Lemma lem2267349 : term416.
Proof. exact (@lem2267338 (@lem2267348)). Qed.
Lemma lem2267351 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267352 : term377 = term383.
Proof. exact (@lem2267351 (NUMERAL 0) term32). Qed.
Lemma lem2267353 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267354 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267355 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267354 h1) (fun h1 : term383 = True => @lem2267353)). Qed.
Lemma lem2267356 : term383 = True.
Proof. exact (EQ_MP (@lem2267355) (@lem2267353)). Qed.
Lemma lem2267357 : term377 = True.
Proof. exact (TRANS (@lem2267352) (@lem2267356)). Qed.
Lemma lem2267358 : True = term377.
Proof. exact (SYM (@lem2267357)). Qed.
Lemma lem2267359 : term377.
Proof. exact (EQ_MP (@lem2267358) (@lem0)). Qed.
Lemma lem2267360 : term417.
Proof. exact (@lem2267349 (@lem2267359)). Qed.
Lemma lem2267362 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2267363 : term41 = term42.
Proof. exact (@lem2267362 term32 term32). Qed.
Lemma lem2267364 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267365 : term44 = term32.
Proof. exact (EQ_MP (@lem2267364) (@lem940073)). Qed.
Lemma lem2267366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267367 : term42 = term38.
Proof. exact (MK_COMB (@lem2267366) (@lem2267365)). Qed.
Lemma lem2267368 : term41 = term38.
Proof. exact (TRANS (@lem2267363) (@lem2267367)). Qed.
Lemma lem2267370 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2267371 : term420 = term421.
Proof. exact (@lem2267370 term32 term32). Qed.
Lemma lem2267372 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267373 : term44 = term32.
Proof. exact (EQ_MP (@lem2267372) (@lem940073)). Qed.
Lemma lem2267374 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267375 : term42 = term38.
Proof. exact (MK_COMB (@lem2267374) (@lem2267373)). Qed.
Lemma lem2267376 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2267377 : term421 = term26.
Proof. exact (MK_COMB (@lem2267376) (@lem2267375)). Qed.
Lemma lem2267378 : term420 = term26.
Proof. exact (TRANS (@lem2267371) (@lem2267377)). Qed.
Lemma lem2267379 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2267380 : term422 = term410.
Proof. exact (MK_COMB (@lem2267379) (@lem2267378)). Qed.
Lemma lem2267381 : term423 = term412.
Proof. exact (MK_COMB (@lem2267380) (@lem2267368)). Qed.
Lemma lem2267383 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2267384 : term412 = term14.
Proof. exact (@lem2267383 term32). Qed.
Lemma lem2267385 : term423 = term14.
Proof. exact (TRANS (@lem2267381) (@lem2267384)). Qed.
Lemma lem2267386 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2267387 : term425 = term426.
Proof. exact (MK_COMB (@lem2267386) (@lem2267385)). Qed.
Lemma lem2267388 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2267389 : term427 = term388.
Proof. exact (MK_COMB (@lem2267387) (@lem2267388)). Qed.
Lemma lem2267391 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267392 : term388 = term14.
Proof. exact (@lem2267391 term32). Qed.
Lemma lem2267393 : term427 = term14.
Proof. exact (TRANS (@lem2267389) (@lem2267392)). Qed.
Lemma lem2267395 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2267396 : term41 = term42.
Proof. exact (@lem2267395 term32 term32). Qed.
Lemma lem2267397 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267398 : term44 = term32.
Proof. exact (EQ_MP (@lem2267397) (@lem940073)). Qed.
Lemma lem2267399 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267400 : term42 = term38.
Proof. exact (MK_COMB (@lem2267399) (@lem2267398)). Qed.
Lemma lem2267401 : term41 = term38.
Proof. exact (TRANS (@lem2267396) (@lem2267400)). Qed.
Lemma lem2267402 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2267403 : term428 = term388.
Proof. exact (MK_COMB (@lem2267402) (@lem2267401)). Qed.
Lemma lem2267405 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267406 : term388 = term14.
Proof. exact (@lem2267405 term32). Qed.
Lemma lem2267407 : term428 = term14.
Proof. exact (TRANS (@lem2267403) (@lem2267406)). Qed.
Lemma lem2267408 : term14 = term428.
Proof. exact (SYM (@lem2267407)). Qed.
Lemma lem2267409 : term427 = term428.
Proof. exact (TRANS (@lem2267393) (@lem2267408)). Qed.
Lemma lem2267410 : term413 = term180.
Proof. exact (@lem2267360 (@lem2267409)). Qed.
Lemma lem2267411 : term412 = term180.
Proof. exact (TRANS (@lem2267326) (@lem2267410)). Qed.
Lemma lem2267413 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2267414 : term180 = term14.
Proof. exact (@lem2267413 term14). Qed.
Lemma lem2267415 : term412 = term14.
Proof. exact (TRANS (@lem2267411) (@lem2267414)). Qed.
Lemma lem2267416 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2267417 : term429 = term426.
Proof. exact (MK_COMB (@lem2267416) (@lem2267415)). Qed.
Lemma lem2267418 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2267419 (x : real) : (term409 x) = (term430 x).
Proof. exact (MK_COMB (@lem2267417) (@lem2267418 x)). Qed.
Lemma lem2267420 (x : real) : (term408 x) = (term430 x).
Proof. exact (TRANS (@lem2267317 x) (@lem2267419 x)). Qed.
Lemma lem2267421 (x : real) : (term430 x) = term14.
Proof. exact (@lem1982719 x). Qed.
Lemma lem2267422 (x : real) : (term408 x) = term14.
Proof. exact (TRANS (@lem2267420 x) (@lem2267421 x)). Qed.
Lemma lem2267423 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2267424 (x : real) : (term431 x) = term432.
Proof. exact (MK_COMB (@lem2267423) (@lem2267422 x)). Qed.
Lemma lem2267425 (n : nat) : (term460 n) = (term434 n).
Proof. exact (@lem1982713 term26 (real_of_num n)). Qed.
Lemma lem2267427 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267428 : term38 = term48.
Proof. exact (@lem2267427 term32). Qed.
Lemma lem2267430 (x : nat) : (term2 x) = (term30 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2267431 : term26 = term31.
Proof. exact (@lem2267430 term32). Qed.
Lemma lem2267432 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2267433 : term410 = term411.
Proof. exact (MK_COMB (@lem2267432) (@lem2267431)). Qed.
Lemma lem2267434 : term412 = term413.
Proof. exact (MK_COMB (@lem2267433) (@lem2267428)). Qed.
Lemma lem2267435 : term414.
Proof. exact (@lem1981473 term26 term38 term38 term38 term14 term38). Qed.
Lemma lem2267437 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267438 : term377 = term383.
Proof. exact (@lem2267437 (NUMERAL 0) term32). Qed.
Lemma lem2267439 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267440 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267441 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267440 h1) (fun h1 : term383 = True => @lem2267439)). Qed.
Lemma lem2267442 : term383 = True.
Proof. exact (EQ_MP (@lem2267441) (@lem2267439)). Qed.
Lemma lem2267443 : term377 = True.
Proof. exact (TRANS (@lem2267438) (@lem2267442)). Qed.
Lemma lem2267444 : True = term377.
Proof. exact (SYM (@lem2267443)). Qed.
Lemma lem2267445 : term377.
Proof. exact (EQ_MP (@lem2267444) (@lem0)). Qed.
Lemma lem2267446 : term415.
Proof. exact (@lem2267435 (@lem2267445)). Qed.
Lemma lem2267448 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267449 : term377 = term383.
Proof. exact (@lem2267448 (NUMERAL 0) term32). Qed.
Lemma lem2267450 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267451 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267452 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267451 h1) (fun h1 : term383 = True => @lem2267450)). Qed.
Lemma lem2267453 : term383 = True.
Proof. exact (EQ_MP (@lem2267452) (@lem2267450)). Qed.
Lemma lem2267454 : term377 = True.
Proof. exact (TRANS (@lem2267449) (@lem2267453)). Qed.
Lemma lem2267455 : True = term377.
Proof. exact (SYM (@lem2267454)). Qed.
Lemma lem2267456 : term377.
Proof. exact (EQ_MP (@lem2267455) (@lem0)). Qed.
Lemma lem2267457 : term416.
Proof. exact (@lem2267446 (@lem2267456)). Qed.
Lemma lem2267459 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267460 : term377 = term383.
Proof. exact (@lem2267459 (NUMERAL 0) term32). Qed.
Lemma lem2267461 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267462 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267463 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267462 h1) (fun h1 : term383 = True => @lem2267461)). Qed.
Lemma lem2267464 : term383 = True.
Proof. exact (EQ_MP (@lem2267463) (@lem2267461)). Qed.
Lemma lem2267465 : term377 = True.
Proof. exact (TRANS (@lem2267460) (@lem2267464)). Qed.
Lemma lem2267466 : True = term377.
Proof. exact (SYM (@lem2267465)). Qed.
Lemma lem2267467 : term377.
Proof. exact (EQ_MP (@lem2267466) (@lem0)). Qed.
Lemma lem2267468 : term417.
Proof. exact (@lem2267457 (@lem2267467)). Qed.
Lemma lem2267470 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2267471 : term41 = term42.
Proof. exact (@lem2267470 term32 term32). Qed.
Lemma lem2267472 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267473 : term44 = term32.
Proof. exact (EQ_MP (@lem2267472) (@lem940073)). Qed.
Lemma lem2267474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267475 : term42 = term38.
Proof. exact (MK_COMB (@lem2267474) (@lem2267473)). Qed.
Lemma lem2267476 : term41 = term38.
Proof. exact (TRANS (@lem2267471) (@lem2267475)). Qed.
Lemma lem2267478 (m : nat) (n : nat) : (term418 m n) = (term419 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2267479 : term420 = term421.
Proof. exact (@lem2267478 term32 term32). Qed.
Lemma lem2267480 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267481 : term44 = term32.
Proof. exact (EQ_MP (@lem2267480) (@lem940073)). Qed.
Lemma lem2267482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267483 : term42 = term38.
Proof. exact (MK_COMB (@lem2267482) (@lem2267481)). Qed.
Lemma lem2267484 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2267485 : term421 = term26.
Proof. exact (MK_COMB (@lem2267484) (@lem2267483)). Qed.
Lemma lem2267486 : term420 = term26.
Proof. exact (TRANS (@lem2267479) (@lem2267485)). Qed.
Lemma lem2267487 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2267488 : term422 = term410.
Proof. exact (MK_COMB (@lem2267487) (@lem2267486)). Qed.
Lemma lem2267489 : term423 = term412.
Proof. exact (MK_COMB (@lem2267488) (@lem2267476)). Qed.
Lemma lem2267491 (m : nat) : (term424 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2267492 : term412 = term14.
Proof. exact (@lem2267491 term32). Qed.
Lemma lem2267493 : term423 = term14.
Proof. exact (TRANS (@lem2267489) (@lem2267492)). Qed.
Lemma lem2267494 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2267495 : term425 = term426.
Proof. exact (MK_COMB (@lem2267494) (@lem2267493)). Qed.
Lemma lem2267496 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem2267497 : term427 = term388.
Proof. exact (MK_COMB (@lem2267495) (@lem2267496)). Qed.
Lemma lem2267499 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267500 : term388 = term14.
Proof. exact (@lem2267499 term32). Qed.
Lemma lem2267501 : term427 = term14.
Proof. exact (TRANS (@lem2267497) (@lem2267500)). Qed.
Lemma lem2267503 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2267504 : term41 = term42.
Proof. exact (@lem2267503 term32 term32). Qed.
Lemma lem2267505 : (term43 = (BIT1 0)) = (term44 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2267506 : term44 = term32.
Proof. exact (EQ_MP (@lem2267505) (@lem940073)). Qed.
Lemma lem2267507 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2267508 : term42 = term38.
Proof. exact (MK_COMB (@lem2267507) (@lem2267506)). Qed.
Lemma lem2267509 : term41 = term38.
Proof. exact (TRANS (@lem2267504) (@lem2267508)). Qed.
Lemma lem2267510 : term426 = term426.
Proof. exact (eq_refl term426). Qed.
Lemma lem2267511 : term428 = term388.
Proof. exact (MK_COMB (@lem2267510) (@lem2267509)). Qed.
Lemma lem2267513 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267514 : term388 = term14.
Proof. exact (@lem2267513 term32). Qed.
Lemma lem2267515 : term428 = term14.
Proof. exact (TRANS (@lem2267511) (@lem2267514)). Qed.
Lemma lem2267516 : term14 = term428.
Proof. exact (SYM (@lem2267515)). Qed.
Lemma lem2267517 : term427 = term428.
Proof. exact (TRANS (@lem2267501) (@lem2267516)). Qed.
Lemma lem2267518 : term413 = term180.
Proof. exact (@lem2267468 (@lem2267517)). Qed.
Lemma lem2267519 : term412 = term180.
Proof. exact (TRANS (@lem2267434) (@lem2267518)). Qed.
Lemma lem2267521 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2267522 : term180 = term14.
Proof. exact (@lem2267521 term14). Qed.
Lemma lem2267523 : term412 = term14.
Proof. exact (TRANS (@lem2267519) (@lem2267522)). Qed.
Lemma lem2267524 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2267525 : term429 = term426.
Proof. exact (MK_COMB (@lem2267524) (@lem2267523)). Qed.
Lemma lem2267526 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem2267527 (n : nat) : (term434 n) = (term387 n).
Proof. exact (MK_COMB (@lem2267525) (@lem2267526 n)). Qed.
Lemma lem2267528 (n : nat) : (term460 n) = (term387 n).
Proof. exact (TRANS (@lem2267425 n) (@lem2267527 n)). Qed.
Lemma lem2267529 (n : nat) : (term387 n) = term14.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem2267530 (n : nat) : (term460 n) = term14.
Proof. exact (TRANS (@lem2267528 n) (@lem2267529 n)). Qed.
Lemma lem2267531 (x : real) (n : nat) : (term459 x n) = term435.
Proof. exact (MK_COMB (@lem2267424 x) (@lem2267530 n)). Qed.
Lemma lem2267532 (x : real) (n : nat) : (term458 x n) = term435.
Proof. exact (TRANS (@lem2267316 x n) (@lem2267531 x n)). Qed.
Lemma lem2267533 : term435 = term14.
Proof. exact (@lem1982721 term14). Qed.
Lemma lem2267534 (x : real) (n : nat) : (term458 x n) = term14.
Proof. exact (TRANS (@lem2267532 x n) (@lem2267533)). Qed.
Lemma lem2267535 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2267536 (x : real) (n : nat) : (term461 x n) = term437.
Proof. exact (MK_COMB (@lem2267535) (@lem2267534 x n)). Qed.
Lemma lem2267537 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2267538 (x : real) (n : nat) : (term457 x n) = term438.
Proof. exact (MK_COMB (@lem2267536 x n) (@lem2267537)). Qed.
Lemma lem2267539 (x : real) (n : nat) (h1 : term368 x n) : term438.
Proof. exact (EQ_MP (@lem2267538 x n) (@lem2267315 x n h1)). Qed.
Lemma lem2267541 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2267542 : term438 = term439.
Proof. exact (@lem2267541 term14 term14). Qed.
Lemma lem2267544 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267545 : term14 = term180.
Proof. exact (@lem2267544 (NUMERAL 0)). Qed.
Lemma lem2267547 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2267548 : term14 = term180.
Proof. exact (@lem2267547 (NUMERAL 0)). Qed.
Lemma lem2267549 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2267550 : term378 = term379.
Proof. exact (MK_COMB (@lem2267549) (@lem2267548)). Qed.
Lemma lem2267551 : term439 = term440.
Proof. exact (MK_COMB (@lem2267550) (@lem2267545)). Qed.
Lemma lem2267552 : term441.
Proof. exact (@lem1980255 term14 term38 term14 term38). Qed.
Lemma lem2267554 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267555 : term377 = term383.
Proof. exact (@lem2267554 (NUMERAL 0) term32). Qed.
Lemma lem2267556 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267557 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267558 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267557 h1) (fun h1 : term383 = True => @lem2267556)). Qed.
Lemma lem2267559 : term383 = True.
Proof. exact (EQ_MP (@lem2267558) (@lem2267556)). Qed.
Lemma lem2267560 : term377 = True.
Proof. exact (TRANS (@lem2267555) (@lem2267559)). Qed.
Lemma lem2267561 : True = term377.
Proof. exact (SYM (@lem2267560)). Qed.
Lemma lem2267562 : term377.
Proof. exact (EQ_MP (@lem2267561) (@lem0)). Qed.
Lemma lem2267563 : term442.
Proof. exact (@lem2267552 (@lem2267562)). Qed.
Lemma lem2267565 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267566 : term377 = term383.
Proof. exact (@lem2267565 (NUMERAL 0) term32). Qed.
Lemma lem2267567 : term384 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2267568 (h1 : term384 = (BIT1 0)) : term383 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2267569 : (term384 = (BIT1 0)) = (term383 = True).
Proof. exact (prop_ext (fun h1 : term384 = (BIT1 0) => @lem2267568 h1) (fun h1 : term383 = True => @lem2267567)). Qed.
Lemma lem2267570 : term383 = True.
Proof. exact (EQ_MP (@lem2267569) (@lem2267567)). Qed.
Lemma lem2267571 : term377 = True.
Proof. exact (TRANS (@lem2267566) (@lem2267570)). Qed.
Lemma lem2267572 : True = term377.
Proof. exact (SYM (@lem2267571)). Qed.
Lemma lem2267573 : term377.
Proof. exact (EQ_MP (@lem2267572) (@lem0)). Qed.
Lemma lem2267574 : term440 = term443.
Proof. exact (@lem2267563 (@lem2267573)). Qed.
Lemma lem2267576 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267577 : term388 = term14.
Proof. exact (@lem2267576 term32). Qed.
Lemma lem2267579 (x : nat) : (term387 x) = term14.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2267580 : term388 = term14.
Proof. exact (@lem2267579 term32). Qed.
Lemma lem2267581 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2267582 : term389 = term378.
Proof. exact (MK_COMB (@lem2267581) (@lem2267580)). Qed.
Lemma lem2267583 : term443 = term439.
Proof. exact (MK_COMB (@lem2267582) (@lem2267577)). Qed.
Lemma lem2267585 (m : nat) (n : nat) : (term382 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2267586 : term439 = term444.
Proof. exact (@lem2267585 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2267587 : term444 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2267588 : term439 = False.
Proof. exact (TRANS (@lem2267586) (@lem2267587)). Qed.
Lemma lem2267589 : term443 = False.
Proof. exact (TRANS (@lem2267583) (@lem2267588)). Qed.
Lemma lem2267590 : term440 = False.
Proof. exact (TRANS (@lem2267574) (@lem2267589)). Qed.
Lemma lem2267591 : term439 = False.
Proof. exact (TRANS (@lem2267551) (@lem2267590)). Qed.
Lemma lem2267592 : term438 = False.
Proof. exact (TRANS (@lem2267542) (@lem2267591)). Qed.
Lemma lem2267593 (x : real) (n : nat) (h1 : term368 x n) : False.
Proof. exact (EQ_MP (@lem2267592) (@lem2267539 x n h1)). Qed.
Lemma lem2267594 (x : real) (n : nat) (h1 : term371 x n) : False.
Proof. exact (or_elim (@lem2265920 x n h1) (fun h0 : term366 x n => @lem2267211 x n h0) (fun h0 : term368 x n => @lem2267593 x n h0)). Qed.
Lemma lem2267595 (x : real) (n : nat) (h1 : term373 x n) : False.
Proof. exact (or_elim (@lem2264193 x n h1) (fun h0 : term346 x n => @lem2265919 x n h0) (fun h0 : term371 x n => @lem2267594 x n h0)). Qed.
Lemma lem2267596 (x : real) (n : nat) (h1 : term375 x n) : False.
Proof. exact (or_elim (@lem2260878 x n h1) (fun h0 : term302 x n => @lem2264192 x n h0) (fun h0 : term373 x n => @lem2267595 x n h0)). Qed.
Lemma lem2267597 (x : real) (n : nat) (h1 : term156 x n) : term156 x n.
Proof. exact (h1). Qed.
Lemma lem2267598 (x : real) (n : nat) (h1 : term156 x n) : term375 x n.
Proof. exact (EQ_MP (@lem2260877 x n) (@lem2267597 x n h1)). Qed.
Lemma lem2267599 (x : real) (n : nat) (h1 : term156 x n) : (term375 x n) = False.
Proof. exact (prop_ext (fun h2 : term375 x n => @lem2267596 x n h2) (fun h2 : False => @lem2267598 x n h1)). Qed.
Lemma lem2267600 (x : real) (n : nat) (h1 : term156 x n) : False.
Proof. exact (EQ_MP (@lem2267599 x n h1) (@lem2267598 x n h1)). Qed.
Lemma lem2267601 (x : real) (n : nat) (h1 : term11 x n) : term11 x n.
Proof. exact (h1). Qed.
Lemma lem2267602 (x : real) (n : nat) (h1 : term11 x n) : term156 x n.
Proof. exact (EQ_MP (@lem2259921 x n) (@lem2267601 x n h1)). Qed.
Lemma lem2267603 (x : real) (n : nat) (h1 : term11 x n) : (term156 x n) = False.
Proof. exact (prop_ext (fun h2 : term156 x n => @lem2267600 x n h2) (fun h2 : False => @lem2267602 x n h1)). Qed.
Lemma lem2267604 (x : real) (n : nat) (h1 : term11 x n) : False.
Proof. exact (EQ_MP (@lem2267603 x n h1) (@lem2267602 x n h1)). Qed.
Lemma lem2267605 (x : real) (n : nat) : term670 x n.
Proof. exact (fun h0 : term11 x n => @lem2267604 x n h0). Qed.
Lemma lem2267606 (x : real) (n : nat) : term671 x n.
Proof. exact (@lem1386578 (((real_abs x) = (real_of_num n)) = (term12 x n))). Qed.
Lemma lem2267609 (x : real) (n : nat) : ((real_abs x) = (real_of_num n)) = (term12 x n).
Proof. exact (@lem2267606 x n (@lem2267605 x n)). Qed.
Lemma lem2267612 (x : real) : (term672 x) = (term673 x).
Proof. exact (fun_ext (fun n : nat => @lem2267609 x n)). Qed.
Lemma lem2267613 (x : real) : (term674 x) = (term675 x).
Proof. exact (MK_COMB (@lem2259384) (@lem2267612 x)). Qed.
