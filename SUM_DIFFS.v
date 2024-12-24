Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_DIFFS_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import REAL_SUB_REFL_spec.
Require Import SUM_0_spec.
Require Import SUM_PARTIAL_SUC_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm19158_spec.
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
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7233426 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7069399 A s). Qed.
Lemma lem7233427 {A : Type'} (s : A -> Prop) : (term0 A s) = ((term1 A s) = term2).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem7233429 (x : real) : term3 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem7233430 (x : real) : (term3 x) = ((term4 x) = term2).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem7233432 (x : real) : term5 x.
Proof. exact (@lem1505261 x). Qed.
Lemma lem7233433 (x : real) : (term5 x) = ((real_sub x x) = term2).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem7233435 (f : nat -> real) : term6 f.
Proof. exact (@lem7233249 f). Qed.
Lemma lem7233436 (f : nat -> real) : (term6 f) = (term7 f).
Proof. exact (eq_refl (term6 f)). Qed.
Lemma lem7233437 (f : nat -> real) : term7 f.
Proof. exact (EQ_MP (@lem7233436 f) (@lem7233435 f)). Qed.
Lemma lem7233438 (f : nat -> real) (g : nat -> real) : term8 f g.
Proof. exact (@lem7233437 f g). Qed.
Lemma lem7233439 (g : nat -> real) (f : nat -> real) : (term8 f g) = (term9 g f).
Proof. exact (eq_refl (term8 f g)). Qed.
Lemma lem7233440 (g : nat -> real) (f : nat -> real) : term9 g f.
Proof. exact (EQ_MP (@lem7233439 g f) (@lem7233438 f g)). Qed.
Lemma lem7233441 (g : nat -> real) (f : nat -> real) (m : nat) : term10 g f m.
Proof. exact (@lem7233440 g f m). Qed.
Lemma lem7233442 (m : nat) (g : nat -> real) (f : nat -> real) : (term10 g f m) = (term11 m g f).
Proof. exact (eq_refl (term10 g f m)). Qed.
Lemma lem7233443 (m : nat) (g : nat -> real) (f : nat -> real) : term11 m g f.
Proof. exact (EQ_MP (@lem7233442 m g f) (@lem7233441 g f m)). Qed.
Lemma lem7233444 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : term12 m g f n.
Proof. exact (@lem7233443 m g f n). Qed.
Lemma lem7233445 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term12 m g f n) = ((term13 m n f g) = (term14 m n g f)).
Proof. exact (eq_refl (term12 m g f n)). Qed.
Lemma lem7233457 (b : real) (a : real) : (term15 b a) = (term16 b a).
Proof. exact (@lem1988318 (real_sub a b) (term17 b a)). Qed.
Lemma lem7233463 (b : real) (a : real) : (real_sub b a) = (term18 b a).
Proof. exact (@lem1982792 b a). Qed.
Lemma lem7233468 (a : real) (b : real) : (term18 b a) = (term19 a b).
Proof. exact (@lem1982761 (term20 a) b). Qed.
Lemma lem7233470 (a : real) (b : real) : (real_sub b a) = (term19 a b).
Proof. exact (TRANS (@lem7233463 b a) (@lem7233468 a b)). Qed.
Lemma lem7233473 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7233474 (a : real) (b : real) : (term17 b a) = (term22 a b).
Proof. exact (MK_COMB (@lem7233473) (@lem7233470 a b)). Qed.
Lemma lem7233475 (a : real) (b : real) : (term22 a b) = (term23 a b).
Proof. exact (@lem1982781 (term20 a) term24 b). Qed.
Lemma lem7233476 (b : real) : (term20 b) = (term20 b).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem7233477 (a : real) : (term25 a) = (term26 a).
Proof. exact (@lem1982749 term24 term24 a). Qed.
Lemma lem7233479 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7233480 : term24 = term29.
Proof. exact (@lem7233479 term30). Qed.
Lemma lem7233482 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7233483 : term24 = term29.
Proof. exact (@lem7233482 term30). Qed.
Lemma lem7233484 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233485 : term21 = term31.
Proof. exact (MK_COMB (@lem7233484) (@lem7233483)). Qed.
Lemma lem7233486 : term32 = term33.
Proof. exact (MK_COMB (@lem7233485) (@lem7233480)). Qed.
Lemma lem7233487 : term33 = term34.
Proof. exact (@lem1981613 term24 term24 term35 term35). Qed.
Lemma lem7233489 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7233490 : term38 = term39.
Proof. exact (@lem7233489 term30 term30). Qed.
Lemma lem7233491 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233492 : term41 = term30.
Proof. exact (EQ_MP (@lem7233491) (@lem940073)). Qed.
Lemma lem7233493 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233494 : term39 = term35.
Proof. exact (MK_COMB (@lem7233493) (@lem7233492)). Qed.
Lemma lem7233495 : term38 = term35.
Proof. exact (TRANS (@lem7233490) (@lem7233494)). Qed.
Lemma lem7233497 (m : nat) (n : nat) : (term42 m n) = (term37 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7233498 : term32 = term39.
Proof. exact (@lem7233497 term30 term30). Qed.
Lemma lem7233499 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233500 : term41 = term30.
Proof. exact (EQ_MP (@lem7233499) (@lem940073)). Qed.
Lemma lem7233501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233502 : term39 = term35.
Proof. exact (MK_COMB (@lem7233501) (@lem7233500)). Qed.
Lemma lem7233503 : term32 = term35.
Proof. exact (TRANS (@lem7233498) (@lem7233502)). Qed.
Lemma lem7233504 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7233505 : term43 = term44.
Proof. exact (MK_COMB (@lem7233504) (@lem7233503)). Qed.
Lemma lem7233506 : term34 = term45.
Proof. exact (MK_COMB (@lem7233505) (@lem7233495)). Qed.
Lemma lem7233507 : term33 = term45.
Proof. exact (TRANS (@lem7233487) (@lem7233506)). Qed.
Lemma lem7233508 : term32 = term45.
Proof. exact (TRANS (@lem7233486) (@lem7233507)). Qed.
Lemma lem7233510 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7233511 : term45 = term35.
Proof. exact (@lem7233510 term35). Qed.
Lemma lem7233512 : term32 = term35.
Proof. exact (TRANS (@lem7233508) (@lem7233511)). Qed.
Lemma lem7233513 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233514 : term47 = term48.
Proof. exact (MK_COMB (@lem7233513) (@lem7233512)). Qed.
Lemma lem7233515 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7233516 (a : real) : (term26 a) = (term49 a).
Proof. exact (MK_COMB (@lem7233514) (@lem7233515 a)). Qed.
Lemma lem7233517 (a : real) : (term25 a) = (term49 a).
Proof. exact (TRANS (@lem7233477 a) (@lem7233516 a)). Qed.
Lemma lem7233518 (a : real) : (term49 a) = a.
Proof. exact (@lem1982709 a). Qed.
Lemma lem7233519 (a : real) : (term25 a) = a.
Proof. exact (TRANS (@lem7233517 a) (@lem7233518 a)). Qed.
Lemma lem7233520 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7233521 (a : real) : (term50 a) = (real_add a).
Proof. exact (MK_COMB (@lem7233520) (@lem7233519 a)). Qed.
Lemma lem7233522 (a : real) (b : real) : (term23 a b) = (term18 a b).
Proof. exact (MK_COMB (@lem7233521 a) (@lem7233476 b)). Qed.
Lemma lem7233523 (a : real) (b : real) : (term22 a b) = (term18 a b).
Proof. exact (TRANS (@lem7233475 a b) (@lem7233522 a b)). Qed.
Lemma lem7233524 (a : real) (b : real) : (term17 b a) = (term18 a b).
Proof. exact (TRANS (@lem7233474 a b) (@lem7233523 a b)). Qed.
Lemma lem7233537 (a : real) (b : real) : (real_sub a b) = (term18 a b).
Proof. exact (@lem1982792 a b). Qed.
Lemma lem7233538 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7233539 (a : real) (b : real) : (term51 a b) = (term52 a b).
Proof. exact (MK_COMB (@lem7233538) (@lem7233537 a b)). Qed.
Lemma lem7233540 (a : real) (b : real) : (term53 b a) = (term54 a b).
Proof. exact (MK_COMB (@lem7233539 a b) (@lem7233524 a b)). Qed.
Lemma lem7233541 (a : real) (b : real) : (term54 a b) = (term55 a b).
Proof. exact (@lem1982792 (term18 a b) (term18 a b)). Qed.
Lemma lem7233542 (a : real) (b : real) : (term56 a b) = (term57 a b).
Proof. exact (@lem1982781 a term24 (term20 b)). Qed.
Lemma lem7233543 (b : real) : (term25 b) = (term26 b).
Proof. exact (@lem1982749 term24 term24 b). Qed.
Lemma lem7233545 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7233546 : term24 = term29.
Proof. exact (@lem7233545 term30). Qed.
Lemma lem7233548 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7233549 : term24 = term29.
Proof. exact (@lem7233548 term30). Qed.
Lemma lem7233550 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233551 : term21 = term31.
Proof. exact (MK_COMB (@lem7233550) (@lem7233549)). Qed.
Lemma lem7233552 : term32 = term33.
Proof. exact (MK_COMB (@lem7233551) (@lem7233546)). Qed.
Lemma lem7233553 : term33 = term34.
Proof. exact (@lem1981613 term24 term24 term35 term35). Qed.
Lemma lem7233555 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7233556 : term38 = term39.
Proof. exact (@lem7233555 term30 term30). Qed.
Lemma lem7233557 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233558 : term41 = term30.
Proof. exact (EQ_MP (@lem7233557) (@lem940073)). Qed.
Lemma lem7233559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233560 : term39 = term35.
Proof. exact (MK_COMB (@lem7233559) (@lem7233558)). Qed.
Lemma lem7233561 : term38 = term35.
Proof. exact (TRANS (@lem7233556) (@lem7233560)). Qed.
Lemma lem7233563 (m : nat) (n : nat) : (term42 m n) = (term37 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7233564 : term32 = term39.
Proof. exact (@lem7233563 term30 term30). Qed.
Lemma lem7233565 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233566 : term41 = term30.
Proof. exact (EQ_MP (@lem7233565) (@lem940073)). Qed.
Lemma lem7233567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233568 : term39 = term35.
Proof. exact (MK_COMB (@lem7233567) (@lem7233566)). Qed.
Lemma lem7233569 : term32 = term35.
Proof. exact (TRANS (@lem7233564) (@lem7233568)). Qed.
Lemma lem7233570 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7233571 : term43 = term44.
Proof. exact (MK_COMB (@lem7233570) (@lem7233569)). Qed.
Lemma lem7233572 : term34 = term45.
Proof. exact (MK_COMB (@lem7233571) (@lem7233561)). Qed.
Lemma lem7233573 : term33 = term45.
Proof. exact (TRANS (@lem7233553) (@lem7233572)). Qed.
Lemma lem7233574 : term32 = term45.
Proof. exact (TRANS (@lem7233552) (@lem7233573)). Qed.
Lemma lem7233576 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7233577 : term45 = term35.
Proof. exact (@lem7233576 term35). Qed.
Lemma lem7233578 : term32 = term35.
Proof. exact (TRANS (@lem7233574) (@lem7233577)). Qed.
Lemma lem7233579 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233580 : term47 = term48.
Proof. exact (MK_COMB (@lem7233579) (@lem7233578)). Qed.
Lemma lem7233581 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7233582 (b : real) : (term26 b) = (term49 b).
Proof. exact (MK_COMB (@lem7233580) (@lem7233581 b)). Qed.
Lemma lem7233583 (b : real) : (term25 b) = (term49 b).
Proof. exact (TRANS (@lem7233543 b) (@lem7233582 b)). Qed.
Lemma lem7233584 (b : real) : (term49 b) = b.
Proof. exact (@lem1982709 b). Qed.
Lemma lem7233585 (b : real) : (term25 b) = b.
Proof. exact (TRANS (@lem7233583 b) (@lem7233584 b)). Qed.
Lemma lem7233588 (a : real) : (term58 a) = (term58 a).
Proof. exact (eq_refl (term58 a)). Qed.
Lemma lem7233589 (a : real) (b : real) : (term57 a b) = (term19 a b).
Proof. exact (MK_COMB (@lem7233588 a) (@lem7233585 b)). Qed.
Lemma lem7233590 (a : real) (b : real) : (term56 a b) = (term19 a b).
Proof. exact (TRANS (@lem7233542 a b) (@lem7233589 a b)). Qed.
Lemma lem7233591 (a : real) (b : real) : (term59 a b) = (term59 a b).
Proof. exact (eq_refl (term59 a b)). Qed.
Lemma lem7233592 (a : real) (b : real) : (term55 a b) = (term60 a b).
Proof. exact (MK_COMB (@lem7233591 a b) (@lem7233590 a b)). Qed.
Lemma lem7233593 (a : real) (b : real) : (term60 a b) = (term61 a b).
Proof. exact (@lem1982753 a (term20 a) (term20 b) b). Qed.
Lemma lem7233594 (a : real) : (term62 a) = (term63 a).
Proof. exact (@lem1982715 term24 a). Qed.
Lemma lem7233596 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233597 : term35 = term45.
Proof. exact (@lem7233596 term30). Qed.
Lemma lem7233599 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7233600 : term24 = term29.
Proof. exact (@lem7233599 term30). Qed.
Lemma lem7233601 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7233602 : term65 = term66.
Proof. exact (MK_COMB (@lem7233601) (@lem7233600)). Qed.
Lemma lem7233603 : term67 = term68.
Proof. exact (MK_COMB (@lem7233602) (@lem7233597)). Qed.
Lemma lem7233604 : term69.
Proof. exact (@lem1981473 term24 term35 term35 term35 term2 term35). Qed.
Lemma lem7233606 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233607 : term71 = term72.
Proof. exact (@lem7233606 (NUMERAL 0) term30). Qed.
Lemma lem7233608 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233609 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233610 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233609 h1) (fun h1 : term72 = True => @lem7233608)). Qed.
Lemma lem7233611 : term72 = True.
Proof. exact (EQ_MP (@lem7233610) (@lem7233608)). Qed.
Lemma lem7233612 : term71 = True.
Proof. exact (TRANS (@lem7233607) (@lem7233611)). Qed.
Lemma lem7233613 : True = term71.
Proof. exact (SYM (@lem7233612)). Qed.
Lemma lem7233614 : term71.
Proof. exact (EQ_MP (@lem7233613) (@lem0)). Qed.
Lemma lem7233615 : term74.
Proof. exact (@lem7233604 (@lem7233614)). Qed.
Lemma lem7233617 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233618 : term71 = term72.
Proof. exact (@lem7233617 (NUMERAL 0) term30). Qed.
Lemma lem7233619 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233620 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233621 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233620 h1) (fun h1 : term72 = True => @lem7233619)). Qed.
Lemma lem7233622 : term72 = True.
Proof. exact (EQ_MP (@lem7233621) (@lem7233619)). Qed.
Lemma lem7233623 : term71 = True.
Proof. exact (TRANS (@lem7233618) (@lem7233622)). Qed.
Lemma lem7233624 : True = term71.
Proof. exact (SYM (@lem7233623)). Qed.
Lemma lem7233625 : term71.
Proof. exact (EQ_MP (@lem7233624) (@lem0)). Qed.
Lemma lem7233626 : term75.
Proof. exact (@lem7233615 (@lem7233625)). Qed.
Lemma lem7233628 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233629 : term71 = term72.
Proof. exact (@lem7233628 (NUMERAL 0) term30). Qed.
Lemma lem7233630 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233631 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233632 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233631 h1) (fun h1 : term72 = True => @lem7233630)). Qed.
Lemma lem7233633 : term72 = True.
Proof. exact (EQ_MP (@lem7233632) (@lem7233630)). Qed.
Lemma lem7233634 : term71 = True.
Proof. exact (TRANS (@lem7233629) (@lem7233633)). Qed.
Lemma lem7233635 : True = term71.
Proof. exact (SYM (@lem7233634)). Qed.
Lemma lem7233636 : term71.
Proof. exact (EQ_MP (@lem7233635) (@lem0)). Qed.
Lemma lem7233637 : term76.
Proof. exact (@lem7233626 (@lem7233636)). Qed.
Lemma lem7233639 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7233640 : term38 = term39.
Proof. exact (@lem7233639 term30 term30). Qed.
Lemma lem7233641 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233642 : term41 = term30.
Proof. exact (EQ_MP (@lem7233641) (@lem940073)). Qed.
Lemma lem7233643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233644 : term39 = term35.
Proof. exact (MK_COMB (@lem7233643) (@lem7233642)). Qed.
Lemma lem7233645 : term38 = term35.
Proof. exact (TRANS (@lem7233640) (@lem7233644)). Qed.
Lemma lem7233647 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7233648 : term79 = term80.
Proof. exact (@lem7233647 term30 term30). Qed.
Lemma lem7233649 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233650 : term41 = term30.
Proof. exact (EQ_MP (@lem7233649) (@lem940073)). Qed.
Lemma lem7233651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233652 : term39 = term35.
Proof. exact (MK_COMB (@lem7233651) (@lem7233650)). Qed.
Lemma lem7233653 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7233654 : term80 = term24.
Proof. exact (MK_COMB (@lem7233653) (@lem7233652)). Qed.
Lemma lem7233655 : term79 = term24.
Proof. exact (TRANS (@lem7233648) (@lem7233654)). Qed.
Lemma lem7233656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7233657 : term81 = term65.
Proof. exact (MK_COMB (@lem7233656) (@lem7233655)). Qed.
Lemma lem7233658 : term82 = term67.
Proof. exact (MK_COMB (@lem7233657) (@lem7233645)). Qed.
Lemma lem7233660 (m : nat) : (term83 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7233661 : term67 = term2.
Proof. exact (@lem7233660 term30). Qed.
Lemma lem7233662 : term82 = term2.
Proof. exact (TRANS (@lem7233658) (@lem7233661)). Qed.
Lemma lem7233663 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233664 : term84 = term85.
Proof. exact (MK_COMB (@lem7233663) (@lem7233662)). Qed.
Lemma lem7233665 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7233666 : term86 = term87.
Proof. exact (MK_COMB (@lem7233664) (@lem7233665)). Qed.
Lemma lem7233668 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233669 : term87 = term2.
Proof. exact (@lem7233668 term30). Qed.
Lemma lem7233670 : term86 = term2.
Proof. exact (TRANS (@lem7233666) (@lem7233669)). Qed.
Lemma lem7233672 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7233673 : term38 = term39.
Proof. exact (@lem7233672 term30 term30). Qed.
Lemma lem7233674 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233675 : term41 = term30.
Proof. exact (EQ_MP (@lem7233674) (@lem940073)). Qed.
Lemma lem7233676 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233677 : term39 = term35.
Proof. exact (MK_COMB (@lem7233676) (@lem7233675)). Qed.
Lemma lem7233678 : term38 = term35.
Proof. exact (TRANS (@lem7233673) (@lem7233677)). Qed.
Lemma lem7233679 : term85 = term85.
Proof. exact (eq_refl term85). Qed.
Lemma lem7233680 : term89 = term87.
Proof. exact (MK_COMB (@lem7233679) (@lem7233678)). Qed.
Lemma lem7233682 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233683 : term87 = term2.
Proof. exact (@lem7233682 term30). Qed.
Lemma lem7233684 : term89 = term2.
Proof. exact (TRANS (@lem7233680) (@lem7233683)). Qed.
Lemma lem7233685 : term2 = term89.
Proof. exact (SYM (@lem7233684)). Qed.
Lemma lem7233686 : term86 = term89.
Proof. exact (TRANS (@lem7233670) (@lem7233685)). Qed.
Lemma lem7233687 : term68 = term90.
Proof. exact (@lem7233637 (@lem7233686)). Qed.
Lemma lem7233688 : term67 = term90.
Proof. exact (TRANS (@lem7233603) (@lem7233687)). Qed.
Lemma lem7233690 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7233691 : term90 = term2.
Proof. exact (@lem7233690 term2). Qed.
Lemma lem7233692 : term67 = term2.
Proof. exact (TRANS (@lem7233688) (@lem7233691)). Qed.
Lemma lem7233693 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233694 : term91 = term85.
Proof. exact (MK_COMB (@lem7233693) (@lem7233692)). Qed.
Lemma lem7233695 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7233696 (a : real) : (term63 a) = (term92 a).
Proof. exact (MK_COMB (@lem7233694) (@lem7233695 a)). Qed.
Lemma lem7233697 (a : real) : (term62 a) = (term92 a).
Proof. exact (TRANS (@lem7233594 a) (@lem7233696 a)). Qed.
Lemma lem7233698 (a : real) : (term92 a) = term2.
Proof. exact (@lem1982719 a). Qed.
Lemma lem7233699 (a : real) : (term62 a) = term2.
Proof. exact (TRANS (@lem7233697 a) (@lem7233698 a)). Qed.
Lemma lem7233700 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7233701 (a : real) : (term93 a) = term94.
Proof. exact (MK_COMB (@lem7233700) (@lem7233699 a)). Qed.
Lemma lem7233702 (b : real) : (term95 b) = (term63 b).
Proof. exact (@lem1982713 term24 b). Qed.
Lemma lem7233704 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233705 : term35 = term45.
Proof. exact (@lem7233704 term30). Qed.
Lemma lem7233707 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7233708 : term24 = term29.
Proof. exact (@lem7233707 term30). Qed.
Lemma lem7233709 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7233710 : term65 = term66.
Proof. exact (MK_COMB (@lem7233709) (@lem7233708)). Qed.
Lemma lem7233711 : term67 = term68.
Proof. exact (MK_COMB (@lem7233710) (@lem7233705)). Qed.
Lemma lem7233712 : term69.
Proof. exact (@lem1981473 term24 term35 term35 term35 term2 term35). Qed.
Lemma lem7233714 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233715 : term71 = term72.
Proof. exact (@lem7233714 (NUMERAL 0) term30). Qed.
Lemma lem7233716 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233717 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233718 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233717 h1) (fun h1 : term72 = True => @lem7233716)). Qed.
Lemma lem7233719 : term72 = True.
Proof. exact (EQ_MP (@lem7233718) (@lem7233716)). Qed.
Lemma lem7233720 : term71 = True.
Proof. exact (TRANS (@lem7233715) (@lem7233719)). Qed.
Lemma lem7233721 : True = term71.
Proof. exact (SYM (@lem7233720)). Qed.
Lemma lem7233722 : term71.
Proof. exact (EQ_MP (@lem7233721) (@lem0)). Qed.
Lemma lem7233723 : term74.
Proof. exact (@lem7233712 (@lem7233722)). Qed.
Lemma lem7233725 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233726 : term71 = term72.
Proof. exact (@lem7233725 (NUMERAL 0) term30). Qed.
Lemma lem7233727 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233728 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233729 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233728 h1) (fun h1 : term72 = True => @lem7233727)). Qed.
Lemma lem7233730 : term72 = True.
Proof. exact (EQ_MP (@lem7233729) (@lem7233727)). Qed.
Lemma lem7233731 : term71 = True.
Proof. exact (TRANS (@lem7233726) (@lem7233730)). Qed.
Lemma lem7233732 : True = term71.
Proof. exact (SYM (@lem7233731)). Qed.
Lemma lem7233733 : term71.
Proof. exact (EQ_MP (@lem7233732) (@lem0)). Qed.
Lemma lem7233734 : term75.
Proof. exact (@lem7233723 (@lem7233733)). Qed.
Lemma lem7233736 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233737 : term71 = term72.
Proof. exact (@lem7233736 (NUMERAL 0) term30). Qed.
Lemma lem7233738 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233739 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233740 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233739 h1) (fun h1 : term72 = True => @lem7233738)). Qed.
Lemma lem7233741 : term72 = True.
Proof. exact (EQ_MP (@lem7233740) (@lem7233738)). Qed.
Lemma lem7233742 : term71 = True.
Proof. exact (TRANS (@lem7233737) (@lem7233741)). Qed.
Lemma lem7233743 : True = term71.
Proof. exact (SYM (@lem7233742)). Qed.
Lemma lem7233744 : term71.
Proof. exact (EQ_MP (@lem7233743) (@lem0)). Qed.
Lemma lem7233745 : term76.
Proof. exact (@lem7233734 (@lem7233744)). Qed.
Lemma lem7233747 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7233748 : term38 = term39.
Proof. exact (@lem7233747 term30 term30). Qed.
Lemma lem7233749 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233750 : term41 = term30.
Proof. exact (EQ_MP (@lem7233749) (@lem940073)). Qed.
Lemma lem7233751 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233752 : term39 = term35.
Proof. exact (MK_COMB (@lem7233751) (@lem7233750)). Qed.
Lemma lem7233753 : term38 = term35.
Proof. exact (TRANS (@lem7233748) (@lem7233752)). Qed.
Lemma lem7233755 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7233756 : term79 = term80.
Proof. exact (@lem7233755 term30 term30). Qed.
Lemma lem7233757 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233758 : term41 = term30.
Proof. exact (EQ_MP (@lem7233757) (@lem940073)). Qed.
Lemma lem7233759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233760 : term39 = term35.
Proof. exact (MK_COMB (@lem7233759) (@lem7233758)). Qed.
Lemma lem7233761 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7233762 : term80 = term24.
Proof. exact (MK_COMB (@lem7233761) (@lem7233760)). Qed.
Lemma lem7233763 : term79 = term24.
Proof. exact (TRANS (@lem7233756) (@lem7233762)). Qed.
Lemma lem7233764 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7233765 : term81 = term65.
Proof. exact (MK_COMB (@lem7233764) (@lem7233763)). Qed.
Lemma lem7233766 : term82 = term67.
Proof. exact (MK_COMB (@lem7233765) (@lem7233753)). Qed.
Lemma lem7233768 (m : nat) : (term83 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7233769 : term67 = term2.
Proof. exact (@lem7233768 term30). Qed.
Lemma lem7233770 : term82 = term2.
Proof. exact (TRANS (@lem7233766) (@lem7233769)). Qed.
Lemma lem7233771 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233772 : term84 = term85.
Proof. exact (MK_COMB (@lem7233771) (@lem7233770)). Qed.
Lemma lem7233773 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7233774 : term86 = term87.
Proof. exact (MK_COMB (@lem7233772) (@lem7233773)). Qed.
Lemma lem7233776 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233777 : term87 = term2.
Proof. exact (@lem7233776 term30). Qed.
Lemma lem7233778 : term86 = term2.
Proof. exact (TRANS (@lem7233774) (@lem7233777)). Qed.
Lemma lem7233780 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7233781 : term38 = term39.
Proof. exact (@lem7233780 term30 term30). Qed.
Lemma lem7233782 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233783 : term41 = term30.
Proof. exact (EQ_MP (@lem7233782) (@lem940073)). Qed.
Lemma lem7233784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233785 : term39 = term35.
Proof. exact (MK_COMB (@lem7233784) (@lem7233783)). Qed.
Lemma lem7233786 : term38 = term35.
Proof. exact (TRANS (@lem7233781) (@lem7233785)). Qed.
Lemma lem7233787 : term85 = term85.
Proof. exact (eq_refl term85). Qed.
Lemma lem7233788 : term89 = term87.
Proof. exact (MK_COMB (@lem7233787) (@lem7233786)). Qed.
Lemma lem7233790 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233791 : term87 = term2.
Proof. exact (@lem7233790 term30). Qed.
Lemma lem7233792 : term89 = term2.
Proof. exact (TRANS (@lem7233788) (@lem7233791)). Qed.
Lemma lem7233793 : term2 = term89.
Proof. exact (SYM (@lem7233792)). Qed.
Lemma lem7233794 : term86 = term89.
Proof. exact (TRANS (@lem7233778) (@lem7233793)). Qed.
Lemma lem7233795 : term68 = term90.
Proof. exact (@lem7233745 (@lem7233794)). Qed.
Lemma lem7233796 : term67 = term90.
Proof. exact (TRANS (@lem7233711) (@lem7233795)). Qed.
Lemma lem7233798 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7233799 : term90 = term2.
Proof. exact (@lem7233798 term2). Qed.
Lemma lem7233800 : term67 = term2.
Proof. exact (TRANS (@lem7233796) (@lem7233799)). Qed.
Lemma lem7233801 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233802 : term91 = term85.
Proof. exact (MK_COMB (@lem7233801) (@lem7233800)). Qed.
Lemma lem7233803 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7233804 (b : real) : (term63 b) = (term92 b).
Proof. exact (MK_COMB (@lem7233802) (@lem7233803 b)). Qed.
Lemma lem7233805 (b : real) : (term95 b) = (term92 b).
Proof. exact (TRANS (@lem7233702 b) (@lem7233804 b)). Qed.
Lemma lem7233806 (b : real) : (term92 b) = term2.
Proof. exact (@lem1982719 b). Qed.
Lemma lem7233807 (b : real) : (term95 b) = term2.
Proof. exact (TRANS (@lem7233805 b) (@lem7233806 b)). Qed.
Lemma lem7233808 (a : real) (b : real) : (term61 a b) = term96.
Proof. exact (MK_COMB (@lem7233701 a) (@lem7233807 b)). Qed.
Lemma lem7233809 (a : real) (b : real) : (term60 a b) = term96.
Proof. exact (TRANS (@lem7233593 a b) (@lem7233808 a b)). Qed.
Lemma lem7233810 : term96 = term2.
Proof. exact (@lem1982721 term2). Qed.
Lemma lem7233811 (a : real) (b : real) : (term60 a b) = term2.
Proof. exact (TRANS (@lem7233809 a b) (@lem7233810)). Qed.
Lemma lem7233812 (a : real) (b : real) : (term55 a b) = term2.
Proof. exact (TRANS (@lem7233592 a b) (@lem7233811 a b)). Qed.
Lemma lem7233813 (a : real) (b : real) : (term54 a b) = term2.
Proof. exact (TRANS (@lem7233541 a b) (@lem7233812 a b)). Qed.
Lemma lem7233814 (b : real) (a : real) : (term53 b a) = term2.
Proof. exact (TRANS (@lem7233540 a b) (@lem7233813 a b)). Qed.
Lemma lem7233815 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7233816 (b : real) (a : real) : (term97 b a) = term98.
Proof. exact (MK_COMB (@lem7233815) (@lem7233814 b a)). Qed.
Lemma lem7233817 : term98 = term99.
Proof. exact (@lem1982785 term2). Qed.
Lemma lem7233819 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233820 : term2 = term90.
Proof. exact (@lem7233819 (NUMERAL 0)). Qed.
Lemma lem7233822 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7233823 : term24 = term29.
Proof. exact (@lem7233822 term30). Qed.
Lemma lem7233824 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233825 : term21 = term31.
Proof. exact (MK_COMB (@lem7233824) (@lem7233823)). Qed.
Lemma lem7233826 : term99 = term100.
Proof. exact (MK_COMB (@lem7233825) (@lem7233820)). Qed.
Lemma lem7233827 : term100 = term101.
Proof. exact (@lem1981613 term24 term2 term35 term35). Qed.
Lemma lem7233829 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7233830 : term38 = term39.
Proof. exact (@lem7233829 term30 term30). Qed.
Lemma lem7233831 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233832 : term41 = term30.
Proof. exact (EQ_MP (@lem7233831) (@lem940073)). Qed.
Lemma lem7233833 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233834 : term39 = term35.
Proof. exact (MK_COMB (@lem7233833) (@lem7233832)). Qed.
Lemma lem7233835 : term38 = term35.
Proof. exact (TRANS (@lem7233830) (@lem7233834)). Qed.
Lemma lem7233837 (x : nat) : (term102 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7233838 : term99 = term2.
Proof. exact (@lem7233837 term30). Qed.
Lemma lem7233839 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7233840 : term103 = term104.
Proof. exact (MK_COMB (@lem7233839) (@lem7233838)). Qed.
Lemma lem7233841 : term101 = term90.
Proof. exact (MK_COMB (@lem7233840) (@lem7233835)). Qed.
Lemma lem7233842 : term100 = term90.
Proof. exact (TRANS (@lem7233827) (@lem7233841)). Qed.
Lemma lem7233843 : term99 = term90.
Proof. exact (TRANS (@lem7233826) (@lem7233842)). Qed.
Lemma lem7233845 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7233846 : term90 = term2.
Proof. exact (@lem7233845 term2). Qed.
Lemma lem7233847 : term99 = term2.
Proof. exact (TRANS (@lem7233843) (@lem7233846)). Qed.
Lemma lem7233848 : term98 = term2.
Proof. exact (TRANS (@lem7233817) (@lem7233847)). Qed.
Lemma lem7233849 (b : real) (a : real) : (term105 b a) = (term105 b a).
Proof. exact (eq_refl (term105 b a)). Qed.
Lemma lem7233850 (b : real) (a : real) : ((term97 b a) = term98) = ((term97 b a) = term2).
Proof. exact (MK_COMB (@lem7233849 b a) (@lem7233848)). Qed.
Lemma lem7233851 (b : real) (a : real) : (term97 b a) = term2.
Proof. exact (EQ_MP (@lem7233850 b a) (@lem7233816 b a)). Qed.
Lemma lem7233852 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7233853 (b : real) (a : real) : (term106 b a) = term107.
Proof. exact (MK_COMB (@lem7233852) (@lem7233851 b a)). Qed.
Lemma lem7233854 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7233855 (b : real) (a : real) : (term108 b a) = term109.
Proof. exact (MK_COMB (@lem7233853 b a) (@lem7233854)). Qed.
Lemma lem7233856 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7233857 (b : real) (a : real) : (term110 b a) = term107.
Proof. exact (MK_COMB (@lem7233856) (@lem7233814 b a)). Qed.
Lemma lem7233858 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7233859 (b : real) (a : real) : (term111 b a) = term109.
Proof. exact (MK_COMB (@lem7233857 b a) (@lem7233858)). Qed.
Lemma lem7233860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7233861 (b : real) (a : real) : (term112 b a) = term113.
Proof. exact (MK_COMB (@lem7233860) (@lem7233859 b a)). Qed.
Lemma lem7233862 (b : real) (a : real) : (term16 b a) = term114.
Proof. exact (MK_COMB (@lem7233861 b a) (@lem7233855 b a)). Qed.
Lemma lem7233876 (b : real) (a : real) : (term15 b a) = term114.
Proof. exact (TRANS (@lem7233457 b a) (@lem7233862 b a)). Qed.
Lemma lem7233886 (h1 : term114) : term114.
Proof. exact (h1). Qed.
Lemma lem7233887 (h1 : term109) : term109.
Proof. exact (h1). Qed.
Lemma lem7233889 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7233890 : term109 = term115.
Proof. exact (@lem7233889 term2 term2). Qed.
Lemma lem7233892 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233893 : term2 = term90.
Proof. exact (@lem7233892 (NUMERAL 0)). Qed.
Lemma lem7233895 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233896 : term2 = term90.
Proof. exact (@lem7233895 (NUMERAL 0)). Qed.
Lemma lem7233897 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7233898 : term116 = term117.
Proof. exact (MK_COMB (@lem7233897) (@lem7233896)). Qed.
Lemma lem7233899 : term115 = term118.
Proof. exact (MK_COMB (@lem7233898) (@lem7233893)). Qed.
Lemma lem7233900 : term119.
Proof. exact (@lem1980255 term2 term35 term2 term35). Qed.
Lemma lem7233902 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233903 : term71 = term72.
Proof. exact (@lem7233902 (NUMERAL 0) term30). Qed.
Lemma lem7233904 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233905 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233906 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233905 h1) (fun h1 : term72 = True => @lem7233904)). Qed.
Lemma lem7233907 : term72 = True.
Proof. exact (EQ_MP (@lem7233906) (@lem7233904)). Qed.
Lemma lem7233908 : term71 = True.
Proof. exact (TRANS (@lem7233903) (@lem7233907)). Qed.
Lemma lem7233909 : True = term71.
Proof. exact (SYM (@lem7233908)). Qed.
Lemma lem7233910 : term71.
Proof. exact (EQ_MP (@lem7233909) (@lem0)). Qed.
Lemma lem7233911 : term120.
Proof. exact (@lem7233900 (@lem7233910)). Qed.
Lemma lem7233913 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233914 : term71 = term72.
Proof. exact (@lem7233913 (NUMERAL 0) term30). Qed.
Lemma lem7233915 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233916 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233917 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233916 h1) (fun h1 : term72 = True => @lem7233915)). Qed.
Lemma lem7233918 : term72 = True.
Proof. exact (EQ_MP (@lem7233917) (@lem7233915)). Qed.
Lemma lem7233919 : term71 = True.
Proof. exact (TRANS (@lem7233914) (@lem7233918)). Qed.
Lemma lem7233920 : True = term71.
Proof. exact (SYM (@lem7233919)). Qed.
Lemma lem7233921 : term71.
Proof. exact (EQ_MP (@lem7233920) (@lem0)). Qed.
Lemma lem7233922 : term118 = term121.
Proof. exact (@lem7233911 (@lem7233921)). Qed.
Lemma lem7233924 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233925 : term87 = term2.
Proof. exact (@lem7233924 term30). Qed.
Lemma lem7233927 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233928 : term87 = term2.
Proof. exact (@lem7233927 term30). Qed.
Lemma lem7233929 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7233930 : term122 = term116.
Proof. exact (MK_COMB (@lem7233929) (@lem7233928)). Qed.
Lemma lem7233931 : term121 = term115.
Proof. exact (MK_COMB (@lem7233930) (@lem7233925)). Qed.
Lemma lem7233933 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233934 : term115 = term123.
Proof. exact (@lem7233933 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7233935 : term123 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7233936 : term115 = False.
Proof. exact (TRANS (@lem7233934) (@lem7233935)). Qed.
Lemma lem7233937 : term121 = False.
Proof. exact (TRANS (@lem7233931) (@lem7233936)). Qed.
Lemma lem7233938 : term118 = False.
Proof. exact (TRANS (@lem7233922) (@lem7233937)). Qed.
Lemma lem7233939 : term115 = False.
Proof. exact (TRANS (@lem7233899) (@lem7233938)). Qed.
Lemma lem7233940 : term109 = False.
Proof. exact (TRANS (@lem7233890) (@lem7233939)). Qed.
Lemma lem7233941 (h1 : term109) : False.
Proof. exact (EQ_MP (@lem7233940) (@lem7233887 h1)). Qed.
Lemma lem7233942 (h1 : term109) : term109.
Proof. exact (h1). Qed.
Lemma lem7233944 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7233945 : term109 = term115.
Proof. exact (@lem7233944 term2 term2). Qed.
Lemma lem7233947 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233948 : term2 = term90.
Proof. exact (@lem7233947 (NUMERAL 0)). Qed.
Lemma lem7233950 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233951 : term2 = term90.
Proof. exact (@lem7233950 (NUMERAL 0)). Qed.
Lemma lem7233952 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7233953 : term116 = term117.
Proof. exact (MK_COMB (@lem7233952) (@lem7233951)). Qed.
Lemma lem7233954 : term115 = term118.
Proof. exact (MK_COMB (@lem7233953) (@lem7233948)). Qed.
Lemma lem7233955 : term119.
Proof. exact (@lem1980255 term2 term35 term2 term35). Qed.
Lemma lem7233957 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233958 : term71 = term72.
Proof. exact (@lem7233957 (NUMERAL 0) term30). Qed.
Lemma lem7233959 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233960 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233961 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233960 h1) (fun h1 : term72 = True => @lem7233959)). Qed.
Lemma lem7233962 : term72 = True.
Proof. exact (EQ_MP (@lem7233961) (@lem7233959)). Qed.
Lemma lem7233963 : term71 = True.
Proof. exact (TRANS (@lem7233958) (@lem7233962)). Qed.
Lemma lem7233964 : True = term71.
Proof. exact (SYM (@lem7233963)). Qed.
Lemma lem7233965 : term71.
Proof. exact (EQ_MP (@lem7233964) (@lem0)). Qed.
Lemma lem7233966 : term120.
Proof. exact (@lem7233955 (@lem7233965)). Qed.
Lemma lem7233968 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233969 : term71 = term72.
Proof. exact (@lem7233968 (NUMERAL 0) term30). Qed.
Lemma lem7233970 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233971 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233972 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7233971 h1) (fun h1 : term72 = True => @lem7233970)). Qed.
Lemma lem7233973 : term72 = True.
Proof. exact (EQ_MP (@lem7233972) (@lem7233970)). Qed.
Lemma lem7233974 : term71 = True.
Proof. exact (TRANS (@lem7233969) (@lem7233973)). Qed.
Lemma lem7233975 : True = term71.
Proof. exact (SYM (@lem7233974)). Qed.
Lemma lem7233976 : term71.
Proof. exact (EQ_MP (@lem7233975) (@lem0)). Qed.
Lemma lem7233977 : term118 = term121.
Proof. exact (@lem7233966 (@lem7233976)). Qed.
Lemma lem7233979 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233980 : term87 = term2.
Proof. exact (@lem7233979 term30). Qed.
Lemma lem7233982 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233983 : term87 = term2.
Proof. exact (@lem7233982 term30). Qed.
Lemma lem7233984 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7233985 : term122 = term116.
Proof. exact (MK_COMB (@lem7233984) (@lem7233983)). Qed.
Lemma lem7233986 : term121 = term115.
Proof. exact (MK_COMB (@lem7233985) (@lem7233980)). Qed.
Lemma lem7233988 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233989 : term115 = term123.
Proof. exact (@lem7233988 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7233990 : term123 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7233991 : term115 = False.
Proof. exact (TRANS (@lem7233989) (@lem7233990)). Qed.
Lemma lem7233992 : term121 = False.
Proof. exact (TRANS (@lem7233986) (@lem7233991)). Qed.
Lemma lem7233993 : term118 = False.
Proof. exact (TRANS (@lem7233977) (@lem7233992)). Qed.
Lemma lem7233994 : term115 = False.
Proof. exact (TRANS (@lem7233954) (@lem7233993)). Qed.
Lemma lem7233995 : term109 = False.
Proof. exact (TRANS (@lem7233945) (@lem7233994)). Qed.
Lemma lem7233996 (h1 : term109) : False.
Proof. exact (EQ_MP (@lem7233995) (@lem7233942 h1)). Qed.
Lemma lem7233997 (h1 : term114) : False.
Proof. exact (or_elim (@lem7233886 h1) (fun h0 : term109 => @lem7233941 h0) (fun h0 : term109 => @lem7233996 h0)). Qed.
Lemma lem7233999 (h1 : term114) : term114.
Proof. exact (h1). Qed.
Lemma lem7234000 (h1 : term114) : term114 = False.
Proof. exact (prop_ext (fun h2 : term114 => @lem7233997 h1) (fun h2 : False => @lem7233999 h1)). Qed.
Lemma lem7234001 (h1 : term114) : False.
Proof. exact (EQ_MP (@lem7234000 h1) (@lem7233999 h1)). Qed.
Lemma lem7234002 (b : real) (a : real) (h1 : term15 b a) : term15 b a.
Proof. exact (h1). Qed.
Lemma lem7234003 (b : real) (a : real) (h1 : term15 b a) : term114.
Proof. exact (EQ_MP (@lem7233876 b a) (@lem7234002 b a h1)). Qed.
Lemma lem7234004 (b : real) (a : real) (h1 : term15 b a) : term114 = False.
Proof. exact (prop_ext (fun h2 : term114 => @lem7234001 h2) (fun h2 : False => @lem7234003 b a h1)). Qed.
Lemma lem7234005 (b : real) (a : real) (h1 : term15 b a) : False.
Proof. exact (EQ_MP (@lem7234004 b a h1) (@lem7234003 b a h1)). Qed.
Lemma lem7234006 (b : real) (a : real) : term124 b a.
Proof. exact (fun h0 : term15 b a => @lem7234005 b a h0). Qed.
Lemma lem7234007 (b : real) (a : real) : term125 b a.
Proof. exact (@lem1386578 ((real_sub a b) = (term17 b a))). Qed.
Lemma lem7234022 (b : real) (a : real) : (real_sub a b) = (term17 b a).
Proof. exact (@lem7234007 b a (@lem7234006 b a)). Qed.
Lemma lem7234023 (f : nat -> real) (k : nat) : (term126 f k) = (term127 f k).
Proof. exact (@lem7234022 (term128 f k) (f k)). Qed.
Lemma lem7234024 (f : nat -> real) : (term129 f) = (term130 f).
Proof. exact (fun_ext (fun k : nat => @lem7234023 f k)). Qed.
Lemma lem7234025 (m : nat) (n : nat) : (term131 m n) = (term131 m n).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem7234026 (m : nat) (n : nat) (f : nat -> real) : (term132 m n f) = (term133 m n f).
Proof. exact (MK_COMB (@lem7234025 m n) (@lem7234024 f)). Qed.
Lemma lem7234027 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7234028 (m : nat) (n : nat) (f : nat -> real) : (term134 m n f) = (term135 m n f).
Proof. exact (MK_COMB (@lem7234027) (@lem7234026 m n f)). Qed.
Lemma lem7234030 (b : real) (a : real) : (real_sub a b) = (term17 b a).
Proof. exact (@lem7234007 b a (@lem7234006 b a)). Qed.
Lemma lem7234031 (n : nat) (f : nat -> real) (m : nat) : (term136 m f n) = (term137 n f m).
Proof. exact (@lem7234030 (term128 f n) (f m)). Qed.
Lemma lem7234032 (m : nat) (n : nat) : (term138 m n) = (term138 m n).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem7234033 (n : nat) (f : nat -> real) (m : nat) : (term139 m f n) = (term140 n f m).
Proof. exact (MK_COMB (@lem7234032 m n) (@lem7234031 n f m)). Qed.
Lemma lem7234034 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234035 (n : nat) (f : nat -> real) (m : nat) : (term141 m f n) = (term142 n f m).
Proof. exact (MK_COMB (@lem7234033 n f m) (@lem7234034)). Qed.
Lemma lem7234036 (n : nat) (f : nat -> real) (m : nat) : ((term132 m n f) = (term141 m f n)) = ((term133 m n f) = (term142 n f m)).
Proof. exact (MK_COMB (@lem7234028 m n f) (@lem7234035 n f m)). Qed.
Lemma lem7234037 (f : nat -> real) (m : nat) : (term143 m f) = (term144 f m).
Proof. exact (fun_ext (fun n : nat => @lem7234036 n f m)). Qed.
Lemma lem7234038 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7234039 (f : nat -> real) (m : nat) : (term145 m f) = (term146 f m).
Proof. exact (MK_COMB (@lem7234038) (@lem7234037 f m)). Qed.
Lemma lem7234040 (f : nat -> real) : (term147 f) = (term148 f).
Proof. exact (fun_ext (fun m : nat => @lem7234039 f m)). Qed.
Lemma lem7234041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7234042 (f : nat -> real) : (term149 f) = (term150 f).
Proof. exact (MK_COMB (@lem7234041) (@lem7234040 f)). Qed.
Lemma lem7234043 (f : nat -> real) : (term150 f) = (term149 f).
Proof. exact (SYM (@lem7234042 f)). Qed.
Lemma lem7234055 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term13 m n f g) = (term14 m n g f).
Proof. exact (EQ_MP (@lem7233445 m n g f) (@lem7233444 m g f n)). Qed.
Lemma lem7234056 (m : nat) (n : nat) (f : nat -> real) : (term151 m n f) = (term152 m n f).
Proof. exact (@lem7234055 m n f term153). Qed.
Lemma lem7234057 (k : nat) : (term154 k) = term24.
Proof. exact (eq_refl (term154 k)). Qed.
Lemma lem7234058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234059 (k : nat) : (term155 k) = term21.
Proof. exact (MK_COMB (@lem7234058) (@lem7234057 k)). Qed.
Lemma lem7234060 (f : nat -> real) (k : nat) : (term156 f k) = (term156 f k).
Proof. exact (eq_refl (term156 f k)). Qed.
Lemma lem7234061 (f : nat -> real) (k : nat) : (term157 f k) = (term127 f k).
Proof. exact (MK_COMB (@lem7234059 k) (@lem7234060 f k)). Qed.
Lemma lem7234062 (f : nat -> real) : (term158 f) = (term130 f).
Proof. exact (fun_ext (fun k : nat => @lem7234061 f k)). Qed.
Lemma lem7234063 (m : nat) (n : nat) : (term131 m n) = (term131 m n).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem7234064 (m : nat) (n : nat) (f : nat -> real) : (term151 m n f) = (term133 m n f).
Proof. exact (MK_COMB (@lem7234063 m n) (@lem7234062 f)). Qed.
Lemma lem7234065 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7234066 (m : nat) (n : nat) (f : nat -> real) : (term159 m n f) = (term135 m n f).
Proof. exact (MK_COMB (@lem7234065) (@lem7234064 m n f)). Qed.
Lemma lem7234067 (n : nat) : (term160 n) = term24.
Proof. exact (eq_refl (term160 n)). Qed.
Lemma lem7234068 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234069 (n : nat) : (term161 n) = term21.
Proof. exact (MK_COMB (@lem7234068) (@lem7234067 n)). Qed.
Lemma lem7234070 (f : nat -> real) (n : nat) : (term128 f n) = (term128 f n).
Proof. exact (eq_refl (term128 f n)). Qed.
Lemma lem7234071 (f : nat -> real) (n : nat) : (term162 f n) = (term163 f n).
Proof. exact (MK_COMB (@lem7234069 n) (@lem7234070 f n)). Qed.
Lemma lem7234072 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7234073 (f : nat -> real) (n : nat) : (term164 f n) = (term165 f n).
Proof. exact (MK_COMB (@lem7234072) (@lem7234071 f n)). Qed.
Lemma lem7234074 (m : nat) : (term154 m) = term24.
Proof. exact (eq_refl (term154 m)). Qed.
Lemma lem7234075 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234076 (m : nat) : (term155 m) = term21.
Proof. exact (MK_COMB (@lem7234075) (@lem7234074 m)). Qed.
Lemma lem7234077 (f : nat -> real) (m : nat) : (f m) = (f m).
Proof. exact (eq_refl (f m)). Qed.
Lemma lem7234078 (f : nat -> real) (m : nat) : (term166 f m) = (term167 f m).
Proof. exact (MK_COMB (@lem7234076 m) (@lem7234077 f m)). Qed.
Lemma lem7234079 (n : nat) (f : nat -> real) (m : nat) : (term168 n f m) = (term169 n f m).
Proof. exact (MK_COMB (@lem7234073 f n) (@lem7234078 f m)). Qed.
Lemma lem7234080 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7234081 (n : nat) (f : nat -> real) (m : nat) : (term170 n f m) = (term171 n f m).
Proof. exact (MK_COMB (@lem7234080) (@lem7234079 n f m)). Qed.
Lemma lem7234082 (k : nat) : (term160 k) = term24.
Proof. exact (eq_refl (term160 k)). Qed.
Lemma lem7234083 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7234084 (k : nat) : (term172 k) = term173.
Proof. exact (MK_COMB (@lem7234083) (@lem7234082 k)). Qed.
Lemma lem7234085 (k : nat) : (term154 k) = term24.
Proof. exact (eq_refl (term154 k)). Qed.
Lemma lem7234086 (k : nat) : (term174 k) = term175.
Proof. exact (MK_COMB (@lem7234084 k) (@lem7234085 k)). Qed.
Lemma lem7234087 (f : nat -> real) (k : nat) : (term176 f k) = (term176 f k).
Proof. exact (eq_refl (term176 f k)). Qed.
Lemma lem7234088 (f : nat -> real) (k : nat) : (term177 f k) = (term178 f k).
Proof. exact (MK_COMB (@lem7234087 f k) (@lem7234086 k)). Qed.
Lemma lem7234089 (f : nat -> real) : (term179 f) = (term180 f).
Proof. exact (fun_ext (fun k : nat => @lem7234088 f k)). Qed.
Lemma lem7234090 (m : nat) (n : nat) : (term131 m n) = (term131 m n).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem7234091 (m : nat) (n : nat) (f : nat -> real) : (term181 m n f) = (term182 m n f).
Proof. exact (MK_COMB (@lem7234090 m n) (@lem7234089 f)). Qed.
Lemma lem7234092 (m : nat) (n : nat) (f : nat -> real) : (term183 m n f) = (term184 m n f).
Proof. exact (MK_COMB (@lem7234081 n f m) (@lem7234091 m n f)). Qed.
Lemma lem7234093 (m : nat) (n : nat) : (term138 m n) = (term138 m n).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem7234094 (m : nat) (n : nat) (f : nat -> real) : (term185 m n f) = (term186 m n f).
Proof. exact (MK_COMB (@lem7234093 m n) (@lem7234092 m n f)). Qed.
Lemma lem7234095 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234096 (m : nat) (n : nat) (f : nat -> real) : (term152 m n f) = (term187 m n f).
Proof. exact (MK_COMB (@lem7234094 m n f) (@lem7234095)). Qed.
Lemma lem7234097 (m : nat) (n : nat) (f : nat -> real) : ((term151 m n f) = (term152 m n f)) = ((term133 m n f) = (term187 m n f)).
Proof. exact (MK_COMB (@lem7234066 m n f) (@lem7234096 m n f)). Qed.
Lemma lem7234098 (m : nat) (n : nat) (f : nat -> real) : (term133 m n f) = (term187 m n f).
Proof. exact (EQ_MP (@lem7234097 m n f) (@lem7234056 m n f)). Qed.
Lemma lem7234099 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7234100 (m : nat) (n : nat) (f : nat -> real) : (term135 m n f) = (term188 m n f).
Proof. exact (MK_COMB (@lem7234099) (@lem7234098 m n f)). Qed.
Lemma lem7234101 (n : nat) (f : nat -> real) (m : nat) : (term142 n f m) = (term142 n f m).
Proof. exact (eq_refl (term142 n f m)). Qed.
Lemma lem7234102 (n : nat) (f : nat -> real) (m : nat) : ((term133 m n f) = (term142 n f m)) = ((term187 m n f) = (term142 n f m)).
Proof. exact (MK_COMB (@lem7234100 m n f) (@lem7234101 n f m)). Qed.
Lemma lem7234103 (f : nat -> real) (m : nat) : (term144 f m) = (term189 f m).
Proof. exact (fun_ext (fun n : nat => @lem7234102 n f m)). Qed.
Lemma lem7234104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7234105 (f : nat -> real) (m : nat) : (term146 f m) = (term190 f m).
Proof. exact (MK_COMB (@lem7234104) (@lem7234103 f m)). Qed.
Lemma lem7234106 (f : nat -> real) : (term148 f) = (term191 f).
Proof. exact (fun_ext (fun m : nat => @lem7234105 f m)). Qed.
Lemma lem7234107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7234108 (f : nat -> real) : (term150 f) = (term192 f).
Proof. exact (MK_COMB (@lem7234107) (@lem7234106 f)). Qed.
Lemma lem7234109 (f : nat -> real) : (term192 f) = (term150 f).
Proof. exact (SYM (@lem7234108 f)). Qed.
Lemma lem7234125 (x : real) : (real_sub x x) = term2.
Proof. exact (EQ_MP (@lem7233433 x) (@lem7233432 x)). Qed.
Lemma lem7234126 : term175 = term2.
Proof. exact (@lem7234125 term24). Qed.
Lemma lem7234127 (f : nat -> real) (k : nat) : (term176 f k) = (term176 f k).
Proof. exact (eq_refl (term176 f k)). Qed.
Lemma lem7234128 (f : nat -> real) (k : nat) : (term178 f k) = (term193 f k).
Proof. exact (MK_COMB (@lem7234127 f k) (@lem7234126)). Qed.
Lemma lem7234130 (x : real) : (term4 x) = term2.
Proof. exact (EQ_MP (@lem7233430 x) (@lem7233429 x)). Qed.
Lemma lem7234131 (f : nat -> real) (k : nat) : (term193 f k) = term2.
Proof. exact (@lem7234130 (term128 f k)). Qed.
Lemma lem7234132 (f : nat -> real) (k : nat) : (term178 f k) = term2.
Proof. exact (TRANS (@lem7234128 f k) (@lem7234131 f k)). Qed.
Lemma lem7234133 (f : nat -> real) : (term180 f) = term194.
Proof. exact (fun_ext (fun k : nat => @lem7234132 f k)). Qed.
Lemma lem7234134 (m : nat) (n : nat) : (term131 m n) = (term131 m n).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem7234135 (f : nat -> real) (m : nat) (n : nat) : (term182 m n f) = (term195 m n).
Proof. exact (MK_COMB (@lem7234134 m n) (@lem7234133 f)). Qed.
Lemma lem7234137 {A : Type'} (s : A -> Prop) : (term1 A s) = term2.
Proof. exact (EQ_MP (@lem7233427 A s) (@lem7233426 A s)). Qed.
Lemma lem7234138 (s : nat -> Prop) : (term196 s) = term2.
Proof. exact (@lem7234137 nat s). Qed.
Lemma lem7234139 (m : nat) (n : nat) : (term195 m n) = term2.
Proof. exact (@lem7234138 (dotdot m n)). Qed.
Lemma lem7234140 (m : nat) (n : nat) (f : nat -> real) : (term182 m n f) = term2.
Proof. exact (TRANS (@lem7234135 f m n) (@lem7234139 m n)). Qed.
Lemma lem7234141 (n : nat) (f : nat -> real) (m : nat) : (term171 n f m) = (term171 n f m).
Proof. exact (eq_refl (term171 n f m)). Qed.
Lemma lem7234142 (n : nat) (f : nat -> real) (m : nat) : (term184 m n f) = (term197 n f m).
Proof. exact (MK_COMB (@lem7234141 n f m) (@lem7234140 m n f)). Qed.
Lemma lem7234145 (m : nat) (n : nat) : (term138 m n) = (term138 m n).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem7234146 (n : nat) (f : nat -> real) (m : nat) : (term186 m n f) = (term198 n f m).
Proof. exact (MK_COMB (@lem7234145 m n) (@lem7234142 n f m)). Qed.
Lemma lem7234147 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234148 (n : nat) (f : nat -> real) (m : nat) : (term187 m n f) = (term199 n f m).
Proof. exact (MK_COMB (@lem7234146 n f m) (@lem7234147)). Qed.
Lemma lem7234149 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7234150 (n : nat) (f : nat -> real) (m : nat) : (term188 m n f) = (term200 n f m).
Proof. exact (MK_COMB (@lem7234149) (@lem7234148 n f m)). Qed.
Lemma lem7234153 (n : nat) (f : nat -> real) (m : nat) : (term142 n f m) = (term142 n f m).
Proof. exact (eq_refl (term142 n f m)). Qed.
Lemma lem7234154 (n : nat) (f : nat -> real) (m : nat) : ((term187 m n f) = (term142 n f m)) = ((term199 n f m) = (term142 n f m)).
Proof. exact (MK_COMB (@lem7234150 n f m) (@lem7234153 n f m)). Qed.
Lemma lem7234157 (f : nat -> real) (m : nat) : (term189 f m) = (term201 f m).
Proof. exact (fun_ext (fun n : nat => @lem7234154 n f m)). Qed.
Lemma lem7234158 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7234159 (f : nat -> real) (m : nat) : (term190 f m) = (term202 f m).
Proof. exact (MK_COMB (@lem7234158) (@lem7234157 f m)). Qed.
Lemma lem7234164 (f : nat -> real) : (term191 f) = (term203 f).
Proof. exact (fun_ext (fun m : nat => @lem7234159 f m)). Qed.
Lemma lem7234165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7234166 (f : nat -> real) : (term192 f) = (term204 f).
Proof. exact (MK_COMB (@lem7234165) (@lem7234164 f)). Qed.
Lemma lem7234171 (f : nat -> real) : (term204 f) = (term192 f).
Proof. exact (SYM (@lem7234166 f)). Qed.
Lemma lem7234185 (P : nat -> Prop) : (term205 P) = (term206 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7234186 (f : nat -> real) (m : nat) : (term207 f m) = (term208 f m).
Proof. exact (@lem7234185 (term201 f m)). Qed.
Lemma lem7234187 (n : nat) (f : nat -> real) (m : nat) : (term209 f m n) = ((term199 n f m) = (term142 n f m)).
Proof. exact (eq_refl (term209 f m n)). Qed.
Lemma lem7234188 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7234190 (n : nat) (f : nat -> real) (m : nat) : (term210 f m n) = (term211 n f m).
Proof. exact (MK_COMB (@lem7234188) (@lem7234187 n f m)). Qed.
Lemma lem7234191 (f : nat -> real) (m : nat) : (term212 f m) = (term213 f m).
Proof. exact (fun_ext (fun n : nat => @lem7234190 n f m)). Qed.
Lemma lem7234192 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234193 (f : nat -> real) (m : nat) : (term208 f m) = (term214 f m).
Proof. exact (MK_COMB (@lem7234192) (@lem7234191 f m)). Qed.
Lemma lem7234194 (f : nat -> real) (m : nat) : (term207 f m) = (term214 f m).
Proof. exact (TRANS (@lem7234186 f m) (@lem7234193 f m)). Qed.
Lemma lem7234195 (P : nat -> Prop) : (term205 P) = (term206 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7234196 (f : nat -> real) : (term215 f) = (term216 f).
Proof. exact (@lem7234195 (term203 f)). Qed.
Lemma lem7234197 (f : nat -> real) (m : nat) : (term217 f m) = (term202 f m).
Proof. exact (eq_refl (term217 f m)). Qed.
Lemma lem7234198 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7234199 (f : nat -> real) (m : nat) : (term218 f m) = (term207 f m).
Proof. exact (MK_COMB (@lem7234198) (@lem7234197 f m)). Qed.
Lemma lem7234200 (f : nat -> real) (m : nat) : (term218 f m) = (term214 f m).
Proof. exact (TRANS (@lem7234199 f m) (@lem7234194 f m)). Qed.
Lemma lem7234201 (f : nat -> real) : (term219 f) = (term220 f).
Proof. exact (fun_ext (fun m : nat => @lem7234200 f m)). Qed.
Lemma lem7234202 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234203 (f : nat -> real) : (term216 f) = (term221 f).
Proof. exact (MK_COMB (@lem7234202) (@lem7234201 f)). Qed.
Lemma lem7234205 (f : nat -> real) : (term215 f) = (term221 f).
Proof. exact (TRANS (@lem7234196 f) (@lem7234203 f)). Qed.
Lemma lem7234209 (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (Peano.le m n) = False.
Proof. exact (h1). Qed.
Lemma lem7234210 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7234211 (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term138 m n) = (@COND real False).
Proof. exact (MK_COMB (@lem7234210) (@lem7234209 m n h1)). Qed.
Lemma lem7234212 (n : nat) (f : nat -> real) (m : nat) : (term197 n f m) = (term197 n f m).
Proof. exact (eq_refl (term197 n f m)). Qed.
Lemma lem7234213 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term198 n f m) = (term222 n f m).
Proof. exact (MK_COMB (@lem7234211 m n h1) (@lem7234212 n f m)). Qed.
Lemma lem7234214 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234215 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term199 n f m) = (term223 n f m).
Proof. exact (MK_COMB (@lem7234213 f m n h1) (@lem7234214)). Qed.
Lemma lem7234217 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7234218 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7234217 real t1 t2). Qed.
Lemma lem7234219 (n : nat) (f : nat -> real) (m : nat) : (term223 n f m) = term2.
Proof. exact (@lem7234218 (term197 n f m) term2). Qed.
Lemma lem7234220 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term199 n f m) = term2.
Proof. exact (TRANS (@lem7234215 f m n h1) (@lem7234219 n f m)). Qed.
Lemma lem7234221 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7234222 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term200 n f m) = term224.
Proof. exact (MK_COMB (@lem7234221) (@lem7234220 f m n h1)). Qed.
Lemma lem7234224 (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (Peano.le m n) = False.
Proof. exact (h1). Qed.
Lemma lem7234225 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7234226 (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term138 m n) = (@COND real False).
Proof. exact (MK_COMB (@lem7234225) (@lem7234224 m n h1)). Qed.
Lemma lem7234227 (n : nat) (f : nat -> real) (m : nat) : (term137 n f m) = (term137 n f m).
Proof. exact (eq_refl (term137 n f m)). Qed.
Lemma lem7234228 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term140 n f m) = (term225 n f m).
Proof. exact (MK_COMB (@lem7234226 m n h1) (@lem7234227 n f m)). Qed.
Lemma lem7234229 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234230 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term142 n f m) = (term226 n f m).
Proof. exact (MK_COMB (@lem7234228 f m n h1) (@lem7234229)). Qed.
Lemma lem7234232 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7234233 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7234232 real t1 t2). Qed.
Lemma lem7234234 (n : nat) (f : nat -> real) (m : nat) : (term226 n f m) = term2.
Proof. exact (@lem7234233 (term137 n f m) term2). Qed.
Lemma lem7234235 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term142 n f m) = term2.
Proof. exact (TRANS (@lem7234230 f m n h1) (@lem7234234 n f m)). Qed.
Lemma lem7234236 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : ((term199 n f m) = (term142 n f m)) = (term2 = term2).
Proof. exact (MK_COMB (@lem7234222 f m n h1) (@lem7234235 f m n h1)). Qed.
Lemma lem7234238 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7234239 (x : real) : (x = x) = True.
Proof. exact (@lem7234238 real x). Qed.
Lemma lem7234240 : (term2 = term2) = True.
Proof. exact (@lem7234239 term2). Qed.
Lemma lem7234241 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : ((term199 n f m) = (term142 n f m)) = True.
Proof. exact (TRANS (@lem7234236 f m n h1) (@lem7234240)). Qed.
Lemma lem7234242 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7234243 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term211 n f m) = (~ True).
Proof. exact (MK_COMB (@lem7234242) (@lem7234241 f m n h1)). Qed.
Lemma lem7234245 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem7234246 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = False) : (term211 n f m) = False.
Proof. exact (TRANS (@lem7234243 f m n h1) (@lem7234245)). Qed.
Lemma lem7234247 (n : nat) (f : nat -> real) (m : nat) : term227 n f m.
Proof. exact (fun h0 : (Peano.le m n) = False => @lem7234246 f m n h0). Qed.
Lemma lem7234249 (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (Peano.le m n) = True.
Proof. exact (h1). Qed.
Lemma lem7234250 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7234251 (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term138 m n) = (@COND real True).
Proof. exact (MK_COMB (@lem7234250) (@lem7234249 m n h1)). Qed.
Lemma lem7234252 (n : nat) (f : nat -> real) (m : nat) : (term197 n f m) = (term197 n f m).
Proof. exact (eq_refl (term197 n f m)). Qed.
Lemma lem7234253 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term198 n f m) = (term228 n f m).
Proof. exact (MK_COMB (@lem7234251 m n h1) (@lem7234252 n f m)). Qed.
Lemma lem7234254 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234255 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term199 n f m) = (term229 n f m).
Proof. exact (MK_COMB (@lem7234253 f m n h1) (@lem7234254)). Qed.
Lemma lem7234257 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7234258 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7234257 real t2 t1). Qed.
Lemma lem7234259 (n : nat) (f : nat -> real) (m : nat) : (term229 n f m) = (term197 n f m).
Proof. exact (@lem7234258 term2 (term197 n f m)). Qed.
Lemma lem7234260 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term199 n f m) = (term197 n f m).
Proof. exact (TRANS (@lem7234255 f m n h1) (@lem7234259 n f m)). Qed.
Lemma lem7234261 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7234262 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term200 n f m) = (term230 n f m).
Proof. exact (MK_COMB (@lem7234261) (@lem7234260 f m n h1)). Qed.
Lemma lem7234264 (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (Peano.le m n) = True.
Proof. exact (h1). Qed.
Lemma lem7234265 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7234266 (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term138 m n) = (@COND real True).
Proof. exact (MK_COMB (@lem7234265) (@lem7234264 m n h1)). Qed.
Lemma lem7234267 (n : nat) (f : nat -> real) (m : nat) : (term137 n f m) = (term137 n f m).
Proof. exact (eq_refl (term137 n f m)). Qed.
Lemma lem7234268 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term140 n f m) = (term231 n f m).
Proof. exact (MK_COMB (@lem7234266 m n h1) (@lem7234267 n f m)). Qed.
Lemma lem7234269 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234270 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term142 n f m) = (term232 n f m).
Proof. exact (MK_COMB (@lem7234268 f m n h1) (@lem7234269)). Qed.
Lemma lem7234272 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7234273 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7234272 real t2 t1). Qed.
Lemma lem7234274 (n : nat) (f : nat -> real) (m : nat) : (term232 n f m) = (term137 n f m).
Proof. exact (@lem7234273 term2 (term137 n f m)). Qed.
Lemma lem7234275 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term142 n f m) = (term137 n f m).
Proof. exact (TRANS (@lem7234270 f m n h1) (@lem7234274 n f m)). Qed.
Lemma lem7234276 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : ((term199 n f m) = (term142 n f m)) = ((term197 n f m) = (term137 n f m)).
Proof. exact (MK_COMB (@lem7234262 f m n h1) (@lem7234275 f m n h1)). Qed.
Lemma lem7234279 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7234280 (f : nat -> real) (m : nat) (n : nat) (h1 : (Peano.le m n) = True) : (term211 n f m) = (term233 n f m).
Proof. exact (MK_COMB (@lem7234279) (@lem7234276 f m n h1)). Qed.
Lemma lem7234281 (n : nat) (f : nat -> real) (m : nat) : term234 n f m.
Proof. exact (fun h0 : (Peano.le m n) = True => @lem7234280 f m n h0). Qed.
Lemma lem7234282 (n : nat) (f : nat -> real) (m : nat) : term235 n f m.
Proof. exact (conj (@lem7234247 n f m) (@lem7234281 n f m)). Qed.
Lemma lem7234284 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term236 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem7234285 (f : nat -> real) (m : nat) (n : nat) : term237 f m n.
Proof. exact (@lem7234284 (term211 n f m) (term233 n f m) (Peano.le m n) False). Qed.
Lemma lem7234286 (f : nat -> real) (m : nat) (n : nat) : (term211 n f m) = (term238 f m n).
Proof. exact (@lem7234285 f m n (@lem7234282 n f m)). Qed.
Lemma lem7234288 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem7234289 (m : nat) (n : nat) : (term239 m n) = False.
Proof. exact (@lem7234288 (term240 m n)). Qed.
Lemma lem7234294 (n : nat) (f : nat -> real) (m : nat) : (term241 n f m) = (term241 n f m).
Proof. exact (eq_refl (term241 n f m)). Qed.
Lemma lem7234295 (n : nat) (f : nat -> real) (m : nat) : (term238 f m n) = (term242 n f m).
Proof. exact (MK_COMB (@lem7234294 n f m) (@lem7234289 m n)). Qed.
Lemma lem7234297 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem7234298 (n : nat) (f : nat -> real) (m : nat) : (term242 n f m) = (term243 n f m).
Proof. exact (@lem7234297 (term243 n f m)). Qed.
Lemma lem7234299 (n : nat) (f : nat -> real) (m : nat) : (term238 f m n) = (term243 n f m).
Proof. exact (TRANS (@lem7234295 n f m) (@lem7234298 n f m)). Qed.
Lemma lem7234310 (n : nat) (f : nat -> real) (m : nat) : (term211 n f m) = (term243 n f m).
Proof. exact (TRANS (@lem7234286 f m n) (@lem7234299 n f m)). Qed.
Lemma lem7234311 (f : nat -> real) (m : nat) : (term213 f m) = (term244 f m).
Proof. exact (fun_ext (fun n : nat => @lem7234310 n f m)). Qed.
Lemma lem7234312 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234313 (f : nat -> real) (m : nat) : (term214 f m) = (term245 f m).
Proof. exact (MK_COMB (@lem7234312) (@lem7234311 f m)). Qed.
Lemma lem7234314 (f : nat -> real) : (term220 f) = (term246 f).
Proof. exact (fun_ext (fun m : nat => @lem7234313 f m)). Qed.
Lemma lem7234315 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234316 (f : nat -> real) : (term221 f) = (term247 f).
Proof. exact (MK_COMB (@lem7234315) (@lem7234314 f)). Qed.
Lemma lem7234317 (f : nat -> real) : (term215 f) = (term247 f).
Proof. exact (TRANS (@lem7234205 f) (@lem7234316 f)). Qed.
Lemma lem7234319 (n : nat) (f : nat -> real) (m : nat) : (term233 n f m) = (term248 n f m).
Proof. exact (@lem1988318 (term197 n f m) (term137 n f m)). Qed.
Lemma lem7234325 (n : nat) (f : nat -> real) (m : nat) : (term249 n f m) = (term250 n f m).
Proof. exact (@lem1982792 (term128 f n) (f m)). Qed.
Lemma lem7234330 (m : nat) (f : nat -> real) (n : nat) : (term250 n f m) = (term251 m f n).
Proof. exact (@lem1982761 (term167 f m) (term128 f n)). Qed.
Lemma lem7234332 (m : nat) (f : nat -> real) (n : nat) : (term249 n f m) = (term251 m f n).
Proof. exact (TRANS (@lem7234325 n f m) (@lem7234330 m f n)). Qed.
Lemma lem7234335 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7234336 (m : nat) (f : nat -> real) (n : nat) : (term137 n f m) = (term252 m f n).
Proof. exact (MK_COMB (@lem7234335) (@lem7234332 m f n)). Qed.
Lemma lem7234337 (m : nat) (f : nat -> real) (n : nat) : (term252 m f n) = (term253 m f n).
Proof. exact (@lem1982781 (term167 f m) term24 (term128 f n)). Qed.
Lemma lem7234338 (f : nat -> real) (n : nat) : (term163 f n) = (term163 f n).
Proof. exact (eq_refl (term163 f n)). Qed.
Lemma lem7234339 (f : nat -> real) (m : nat) : (term254 f m) = (term255 f m).
Proof. exact (@lem1982749 term24 term24 (f m)). Qed.
Lemma lem7234341 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234342 : term24 = term29.
Proof. exact (@lem7234341 term30). Qed.
Lemma lem7234344 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234345 : term24 = term29.
Proof. exact (@lem7234344 term30). Qed.
Lemma lem7234346 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234347 : term21 = term31.
Proof. exact (MK_COMB (@lem7234346) (@lem7234345)). Qed.
Lemma lem7234348 : term32 = term33.
Proof. exact (MK_COMB (@lem7234347) (@lem7234342)). Qed.
Lemma lem7234349 : term33 = term34.
Proof. exact (@lem1981613 term24 term24 term35 term35). Qed.
Lemma lem7234351 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234352 : term38 = term39.
Proof. exact (@lem7234351 term30 term30). Qed.
Lemma lem7234353 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234354 : term41 = term30.
Proof. exact (EQ_MP (@lem7234353) (@lem940073)). Qed.
Lemma lem7234355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234356 : term39 = term35.
Proof. exact (MK_COMB (@lem7234355) (@lem7234354)). Qed.
Lemma lem7234357 : term38 = term35.
Proof. exact (TRANS (@lem7234352) (@lem7234356)). Qed.
Lemma lem7234359 (m : nat) (n : nat) : (term42 m n) = (term37 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7234360 : term32 = term39.
Proof. exact (@lem7234359 term30 term30). Qed.
Lemma lem7234361 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234362 : term41 = term30.
Proof. exact (EQ_MP (@lem7234361) (@lem940073)). Qed.
Lemma lem7234363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234364 : term39 = term35.
Proof. exact (MK_COMB (@lem7234363) (@lem7234362)). Qed.
Lemma lem7234365 : term32 = term35.
Proof. exact (TRANS (@lem7234360) (@lem7234364)). Qed.
Lemma lem7234366 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7234367 : term43 = term44.
Proof. exact (MK_COMB (@lem7234366) (@lem7234365)). Qed.
Lemma lem7234368 : term34 = term45.
Proof. exact (MK_COMB (@lem7234367) (@lem7234357)). Qed.
Lemma lem7234369 : term33 = term45.
Proof. exact (TRANS (@lem7234349) (@lem7234368)). Qed.
Lemma lem7234370 : term32 = term45.
Proof. exact (TRANS (@lem7234348) (@lem7234369)). Qed.
Lemma lem7234372 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7234373 : term45 = term35.
Proof. exact (@lem7234372 term35). Qed.
Lemma lem7234374 : term32 = term35.
Proof. exact (TRANS (@lem7234370) (@lem7234373)). Qed.
Lemma lem7234375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234376 : term47 = term48.
Proof. exact (MK_COMB (@lem7234375) (@lem7234374)). Qed.
Lemma lem7234377 (f : nat -> real) (m : nat) : (f m) = (f m).
Proof. exact (eq_refl (f m)). Qed.
Lemma lem7234378 (f : nat -> real) (m : nat) : (term255 f m) = (term256 f m).
Proof. exact (MK_COMB (@lem7234376) (@lem7234377 f m)). Qed.
Lemma lem7234379 (f : nat -> real) (m : nat) : (term254 f m) = (term256 f m).
Proof. exact (TRANS (@lem7234339 f m) (@lem7234378 f m)). Qed.
Lemma lem7234380 (f : nat -> real) (m : nat) : (term256 f m) = (f m).
Proof. exact (@lem1982709 (f m)). Qed.
Lemma lem7234381 (f : nat -> real) (m : nat) : (term254 f m) = (f m).
Proof. exact (TRANS (@lem7234379 f m) (@lem7234380 f m)). Qed.
Lemma lem7234382 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7234383 (f : nat -> real) (m : nat) : (term257 f m) = (term258 f m).
Proof. exact (MK_COMB (@lem7234382) (@lem7234381 f m)). Qed.
Lemma lem7234384 (m : nat) (f : nat -> real) (n : nat) : (term253 m f n) = (term259 m f n).
Proof. exact (MK_COMB (@lem7234383 f m) (@lem7234338 f n)). Qed.
Lemma lem7234385 (m : nat) (f : nat -> real) (n : nat) : (term252 m f n) = (term259 m f n).
Proof. exact (TRANS (@lem7234337 m f n) (@lem7234384 m f n)). Qed.
Lemma lem7234386 (m : nat) (f : nat -> real) (n : nat) : (term137 n f m) = (term259 m f n).
Proof. exact (TRANS (@lem7234336 m f n) (@lem7234385 m f n)). Qed.
Lemma lem7234387 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234405 (n : nat) (f : nat -> real) (m : nat) : (term169 n f m) = (term260 n f m).
Proof. exact (@lem1982792 (term163 f n) (term167 f m)). Qed.
Lemma lem7234406 (f : nat -> real) (m : nat) : (term254 f m) = (term255 f m).
Proof. exact (@lem1982749 term24 term24 (f m)). Qed.
Lemma lem7234408 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234409 : term24 = term29.
Proof. exact (@lem7234408 term30). Qed.
Lemma lem7234411 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234412 : term24 = term29.
Proof. exact (@lem7234411 term30). Qed.
Lemma lem7234413 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234414 : term21 = term31.
Proof. exact (MK_COMB (@lem7234413) (@lem7234412)). Qed.
Lemma lem7234415 : term32 = term33.
Proof. exact (MK_COMB (@lem7234414) (@lem7234409)). Qed.
Lemma lem7234416 : term33 = term34.
Proof. exact (@lem1981613 term24 term24 term35 term35). Qed.
Lemma lem7234418 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234419 : term38 = term39.
Proof. exact (@lem7234418 term30 term30). Qed.
Lemma lem7234420 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234421 : term41 = term30.
Proof. exact (EQ_MP (@lem7234420) (@lem940073)). Qed.
Lemma lem7234422 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234423 : term39 = term35.
Proof. exact (MK_COMB (@lem7234422) (@lem7234421)). Qed.
Lemma lem7234424 : term38 = term35.
Proof. exact (TRANS (@lem7234419) (@lem7234423)). Qed.
Lemma lem7234426 (m : nat) (n : nat) : (term42 m n) = (term37 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7234427 : term32 = term39.
Proof. exact (@lem7234426 term30 term30). Qed.
Lemma lem7234428 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234429 : term41 = term30.
Proof. exact (EQ_MP (@lem7234428) (@lem940073)). Qed.
Lemma lem7234430 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234431 : term39 = term35.
Proof. exact (MK_COMB (@lem7234430) (@lem7234429)). Qed.
Lemma lem7234432 : term32 = term35.
Proof. exact (TRANS (@lem7234427) (@lem7234431)). Qed.
Lemma lem7234433 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7234434 : term43 = term44.
Proof. exact (MK_COMB (@lem7234433) (@lem7234432)). Qed.
Lemma lem7234435 : term34 = term45.
Proof. exact (MK_COMB (@lem7234434) (@lem7234424)). Qed.
Lemma lem7234436 : term33 = term45.
Proof. exact (TRANS (@lem7234416) (@lem7234435)). Qed.
Lemma lem7234437 : term32 = term45.
Proof. exact (TRANS (@lem7234415) (@lem7234436)). Qed.
Lemma lem7234439 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7234440 : term45 = term35.
Proof. exact (@lem7234439 term35). Qed.
Lemma lem7234441 : term32 = term35.
Proof. exact (TRANS (@lem7234437) (@lem7234440)). Qed.
Lemma lem7234442 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234443 : term47 = term48.
Proof. exact (MK_COMB (@lem7234442) (@lem7234441)). Qed.
Lemma lem7234444 (f : nat -> real) (m : nat) : (f m) = (f m).
Proof. exact (eq_refl (f m)). Qed.
Lemma lem7234445 (f : nat -> real) (m : nat) : (term255 f m) = (term256 f m).
Proof. exact (MK_COMB (@lem7234443) (@lem7234444 f m)). Qed.
Lemma lem7234446 (f : nat -> real) (m : nat) : (term254 f m) = (term256 f m).
Proof. exact (TRANS (@lem7234406 f m) (@lem7234445 f m)). Qed.
Lemma lem7234447 (f : nat -> real) (m : nat) : (term256 f m) = (f m).
Proof. exact (@lem1982709 (f m)). Qed.
Lemma lem7234448 (f : nat -> real) (m : nat) : (term254 f m) = (f m).
Proof. exact (TRANS (@lem7234446 f m) (@lem7234447 f m)). Qed.
Lemma lem7234449 (f : nat -> real) (n : nat) : (term261 f n) = (term261 f n).
Proof. exact (eq_refl (term261 f n)). Qed.
Lemma lem7234450 (n : nat) (f : nat -> real) (m : nat) : (term260 n f m) = (term262 n f m).
Proof. exact (MK_COMB (@lem7234449 f n) (@lem7234448 f m)). Qed.
Lemma lem7234451 (m : nat) (f : nat -> real) (n : nat) : (term262 n f m) = (term259 m f n).
Proof. exact (@lem1982761 (f m) (term163 f n)). Qed.
Lemma lem7234452 (m : nat) (f : nat -> real) (n : nat) : (term260 n f m) = (term259 m f n).
Proof. exact (TRANS (@lem7234450 n f m) (@lem7234451 m f n)). Qed.
Lemma lem7234454 (m : nat) (f : nat -> real) (n : nat) : (term169 n f m) = (term259 m f n).
Proof. exact (TRANS (@lem7234405 n f m) (@lem7234452 m f n)). Qed.
Lemma lem7234455 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7234456 (m : nat) (f : nat -> real) (n : nat) : (term171 n f m) = (term263 m f n).
Proof. exact (MK_COMB (@lem7234455) (@lem7234454 m f n)). Qed.
Lemma lem7234457 (m : nat) (f : nat -> real) (n : nat) : (term197 n f m) = (term264 m f n).
Proof. exact (MK_COMB (@lem7234456 m f n) (@lem7234387)). Qed.
Lemma lem7234458 (m : nat) (f : nat -> real) (n : nat) : (term264 m f n) = (term265 m f n).
Proof. exact (@lem1982792 (term259 m f n) term2). Qed.
Lemma lem7234460 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7234461 : term2 = term90.
Proof. exact (@lem7234460 (NUMERAL 0)). Qed.
Lemma lem7234463 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234464 : term24 = term29.
Proof. exact (@lem7234463 term30). Qed.
Lemma lem7234465 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234466 : term21 = term31.
Proof. exact (MK_COMB (@lem7234465) (@lem7234464)). Qed.
Lemma lem7234467 : term99 = term100.
Proof. exact (MK_COMB (@lem7234466) (@lem7234461)). Qed.
Lemma lem7234468 : term100 = term101.
Proof. exact (@lem1981613 term24 term2 term35 term35). Qed.
Lemma lem7234470 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234471 : term38 = term39.
Proof. exact (@lem7234470 term30 term30). Qed.
Lemma lem7234472 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234473 : term41 = term30.
Proof. exact (EQ_MP (@lem7234472) (@lem940073)). Qed.
Lemma lem7234474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234475 : term39 = term35.
Proof. exact (MK_COMB (@lem7234474) (@lem7234473)). Qed.
Lemma lem7234476 : term38 = term35.
Proof. exact (TRANS (@lem7234471) (@lem7234475)). Qed.
Lemma lem7234478 (x : nat) : (term102 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7234479 : term99 = term2.
Proof. exact (@lem7234478 term30). Qed.
Lemma lem7234480 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7234481 : term103 = term104.
Proof. exact (MK_COMB (@lem7234480) (@lem7234479)). Qed.
Lemma lem7234482 : term101 = term90.
Proof. exact (MK_COMB (@lem7234481) (@lem7234476)). Qed.
Lemma lem7234483 : term100 = term90.
Proof. exact (TRANS (@lem7234468) (@lem7234482)). Qed.
Lemma lem7234484 : term99 = term90.
Proof. exact (TRANS (@lem7234467) (@lem7234483)). Qed.
Lemma lem7234486 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7234487 : term90 = term2.
Proof. exact (@lem7234486 term2). Qed.
Lemma lem7234488 : term99 = term2.
Proof. exact (TRANS (@lem7234484) (@lem7234487)). Qed.
Lemma lem7234489 (m : nat) (f : nat -> real) (n : nat) : (term266 m f n) = (term266 m f n).
Proof. exact (eq_refl (term266 m f n)). Qed.
Lemma lem7234490 (m : nat) (f : nat -> real) (n : nat) : (term265 m f n) = (term267 m f n).
Proof. exact (MK_COMB (@lem7234489 m f n) (@lem7234488)). Qed.
Lemma lem7234491 (m : nat) (f : nat -> real) (n : nat) : (term267 m f n) = (term259 m f n).
Proof. exact (@lem1982723 (term259 m f n)). Qed.
Lemma lem7234492 (m : nat) (f : nat -> real) (n : nat) : (term265 m f n) = (term259 m f n).
Proof. exact (TRANS (@lem7234490 m f n) (@lem7234491 m f n)). Qed.
Lemma lem7234493 (m : nat) (f : nat -> real) (n : nat) : (term264 m f n) = (term259 m f n).
Proof. exact (TRANS (@lem7234458 m f n) (@lem7234492 m f n)). Qed.
Lemma lem7234494 (m : nat) (f : nat -> real) (n : nat) : (term197 n f m) = (term259 m f n).
Proof. exact (TRANS (@lem7234457 m f n) (@lem7234493 m f n)). Qed.
Lemma lem7234495 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7234496 (m : nat) (f : nat -> real) (n : nat) : (term268 n f m) = (term263 m f n).
Proof. exact (MK_COMB (@lem7234495) (@lem7234494 m f n)). Qed.
Lemma lem7234497 (m : nat) (f : nat -> real) (n : nat) : (term269 n f m) = (term270 m f n).
Proof. exact (MK_COMB (@lem7234496 m f n) (@lem7234386 m f n)). Qed.
Lemma lem7234498 (m : nat) (f : nat -> real) (n : nat) : (term270 m f n) = (term271 m f n).
Proof. exact (@lem1982792 (term259 m f n) (term259 m f n)). Qed.
Lemma lem7234499 (m : nat) (f : nat -> real) (n : nat) : (term272 m f n) = (term273 m f n).
Proof. exact (@lem1982781 (f m) term24 (term163 f n)). Qed.
Lemma lem7234500 (f : nat -> real) (n : nat) : (term274 f n) = (term275 f n).
Proof. exact (@lem1982749 term24 term24 (term128 f n)). Qed.
Lemma lem7234502 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234503 : term24 = term29.
Proof. exact (@lem7234502 term30). Qed.
Lemma lem7234505 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234506 : term24 = term29.
Proof. exact (@lem7234505 term30). Qed.
Lemma lem7234507 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234508 : term21 = term31.
Proof. exact (MK_COMB (@lem7234507) (@lem7234506)). Qed.
Lemma lem7234509 : term32 = term33.
Proof. exact (MK_COMB (@lem7234508) (@lem7234503)). Qed.
Lemma lem7234510 : term33 = term34.
Proof. exact (@lem1981613 term24 term24 term35 term35). Qed.
Lemma lem7234512 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234513 : term38 = term39.
Proof. exact (@lem7234512 term30 term30). Qed.
Lemma lem7234514 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234515 : term41 = term30.
Proof. exact (EQ_MP (@lem7234514) (@lem940073)). Qed.
Lemma lem7234516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234517 : term39 = term35.
Proof. exact (MK_COMB (@lem7234516) (@lem7234515)). Qed.
Lemma lem7234518 : term38 = term35.
Proof. exact (TRANS (@lem7234513) (@lem7234517)). Qed.
Lemma lem7234520 (m : nat) (n : nat) : (term42 m n) = (term37 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7234521 : term32 = term39.
Proof. exact (@lem7234520 term30 term30). Qed.
Lemma lem7234522 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234523 : term41 = term30.
Proof. exact (EQ_MP (@lem7234522) (@lem940073)). Qed.
Lemma lem7234524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234525 : term39 = term35.
Proof. exact (MK_COMB (@lem7234524) (@lem7234523)). Qed.
Lemma lem7234526 : term32 = term35.
Proof. exact (TRANS (@lem7234521) (@lem7234525)). Qed.
Lemma lem7234527 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7234528 : term43 = term44.
Proof. exact (MK_COMB (@lem7234527) (@lem7234526)). Qed.
Lemma lem7234529 : term34 = term45.
Proof. exact (MK_COMB (@lem7234528) (@lem7234518)). Qed.
Lemma lem7234530 : term33 = term45.
Proof. exact (TRANS (@lem7234510) (@lem7234529)). Qed.
Lemma lem7234531 : term32 = term45.
Proof. exact (TRANS (@lem7234509) (@lem7234530)). Qed.
Lemma lem7234533 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7234534 : term45 = term35.
Proof. exact (@lem7234533 term35). Qed.
Lemma lem7234535 : term32 = term35.
Proof. exact (TRANS (@lem7234531) (@lem7234534)). Qed.
Lemma lem7234536 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234537 : term47 = term48.
Proof. exact (MK_COMB (@lem7234536) (@lem7234535)). Qed.
Lemma lem7234538 (f : nat -> real) (n : nat) : (term128 f n) = (term128 f n).
Proof. exact (eq_refl (term128 f n)). Qed.
Lemma lem7234539 (f : nat -> real) (n : nat) : (term275 f n) = (term276 f n).
Proof. exact (MK_COMB (@lem7234537) (@lem7234538 f n)). Qed.
Lemma lem7234540 (f : nat -> real) (n : nat) : (term274 f n) = (term276 f n).
Proof. exact (TRANS (@lem7234500 f n) (@lem7234539 f n)). Qed.
Lemma lem7234541 (f : nat -> real) (n : nat) : (term276 f n) = (term128 f n).
Proof. exact (@lem1982709 (term128 f n)). Qed.
Lemma lem7234542 (f : nat -> real) (n : nat) : (term274 f n) = (term128 f n).
Proof. exact (TRANS (@lem7234540 f n) (@lem7234541 f n)). Qed.
Lemma lem7234545 (f : nat -> real) (m : nat) : (term277 f m) = (term277 f m).
Proof. exact (eq_refl (term277 f m)). Qed.
Lemma lem7234546 (m : nat) (f : nat -> real) (n : nat) : (term273 m f n) = (term251 m f n).
Proof. exact (MK_COMB (@lem7234545 f m) (@lem7234542 f n)). Qed.
Lemma lem7234547 (m : nat) (f : nat -> real) (n : nat) : (term272 m f n) = (term251 m f n).
Proof. exact (TRANS (@lem7234499 m f n) (@lem7234546 m f n)). Qed.
Lemma lem7234548 (m : nat) (f : nat -> real) (n : nat) : (term266 m f n) = (term266 m f n).
Proof. exact (eq_refl (term266 m f n)). Qed.
Lemma lem7234549 (m : nat) (f : nat -> real) (n : nat) : (term271 m f n) = (term278 m f n).
Proof. exact (MK_COMB (@lem7234548 m f n) (@lem7234547 m f n)). Qed.
Lemma lem7234550 (m : nat) (f : nat -> real) (n : nat) : (term278 m f n) = (term279 m f n).
Proof. exact (@lem1982753 (f m) (term167 f m) (term163 f n) (term128 f n)). Qed.
Lemma lem7234551 (f : nat -> real) (m : nat) : (term280 f m) = (term281 f m).
Proof. exact (@lem1982715 term24 (f m)). Qed.
Lemma lem7234553 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7234554 : term35 = term45.
Proof. exact (@lem7234553 term30). Qed.
Lemma lem7234556 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234557 : term24 = term29.
Proof. exact (@lem7234556 term30). Qed.
Lemma lem7234558 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7234559 : term65 = term66.
Proof. exact (MK_COMB (@lem7234558) (@lem7234557)). Qed.
Lemma lem7234560 : term67 = term68.
Proof. exact (MK_COMB (@lem7234559) (@lem7234554)). Qed.
Lemma lem7234561 : term69.
Proof. exact (@lem1981473 term24 term35 term35 term35 term2 term35). Qed.
Lemma lem7234563 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7234564 : term71 = term72.
Proof. exact (@lem7234563 (NUMERAL 0) term30). Qed.
Lemma lem7234565 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7234566 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7234567 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7234566 h1) (fun h1 : term72 = True => @lem7234565)). Qed.
Lemma lem7234568 : term72 = True.
Proof. exact (EQ_MP (@lem7234567) (@lem7234565)). Qed.
Lemma lem7234569 : term71 = True.
Proof. exact (TRANS (@lem7234564) (@lem7234568)). Qed.
Lemma lem7234570 : True = term71.
Proof. exact (SYM (@lem7234569)). Qed.
Lemma lem7234571 : term71.
Proof. exact (EQ_MP (@lem7234570) (@lem0)). Qed.
Lemma lem7234572 : term74.
Proof. exact (@lem7234561 (@lem7234571)). Qed.
Lemma lem7234574 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7234575 : term71 = term72.
Proof. exact (@lem7234574 (NUMERAL 0) term30). Qed.
Lemma lem7234576 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7234577 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7234578 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7234577 h1) (fun h1 : term72 = True => @lem7234576)). Qed.
Lemma lem7234579 : term72 = True.
Proof. exact (EQ_MP (@lem7234578) (@lem7234576)). Qed.
Lemma lem7234580 : term71 = True.
Proof. exact (TRANS (@lem7234575) (@lem7234579)). Qed.
Lemma lem7234581 : True = term71.
Proof. exact (SYM (@lem7234580)). Qed.
Lemma lem7234582 : term71.
Proof. exact (EQ_MP (@lem7234581) (@lem0)). Qed.
Lemma lem7234583 : term75.
Proof. exact (@lem7234572 (@lem7234582)). Qed.
Lemma lem7234585 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7234586 : term71 = term72.
Proof. exact (@lem7234585 (NUMERAL 0) term30). Qed.
Lemma lem7234587 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7234588 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7234589 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7234588 h1) (fun h1 : term72 = True => @lem7234587)). Qed.
Lemma lem7234590 : term72 = True.
Proof. exact (EQ_MP (@lem7234589) (@lem7234587)). Qed.
Lemma lem7234591 : term71 = True.
Proof. exact (TRANS (@lem7234586) (@lem7234590)). Qed.
Lemma lem7234592 : True = term71.
Proof. exact (SYM (@lem7234591)). Qed.
Lemma lem7234593 : term71.
Proof. exact (EQ_MP (@lem7234592) (@lem0)). Qed.
Lemma lem7234594 : term76.
Proof. exact (@lem7234583 (@lem7234593)). Qed.
Lemma lem7234596 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234597 : term38 = term39.
Proof. exact (@lem7234596 term30 term30). Qed.
Lemma lem7234598 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234599 : term41 = term30.
Proof. exact (EQ_MP (@lem7234598) (@lem940073)). Qed.
Lemma lem7234600 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234601 : term39 = term35.
Proof. exact (MK_COMB (@lem7234600) (@lem7234599)). Qed.
Lemma lem7234602 : term38 = term35.
Proof. exact (TRANS (@lem7234597) (@lem7234601)). Qed.
Lemma lem7234604 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7234605 : term79 = term80.
Proof. exact (@lem7234604 term30 term30). Qed.
Lemma lem7234606 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234607 : term41 = term30.
Proof. exact (EQ_MP (@lem7234606) (@lem940073)). Qed.
Lemma lem7234608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234609 : term39 = term35.
Proof. exact (MK_COMB (@lem7234608) (@lem7234607)). Qed.
Lemma lem7234610 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7234611 : term80 = term24.
Proof. exact (MK_COMB (@lem7234610) (@lem7234609)). Qed.
Lemma lem7234612 : term79 = term24.
Proof. exact (TRANS (@lem7234605) (@lem7234611)). Qed.
Lemma lem7234613 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7234614 : term81 = term65.
Proof. exact (MK_COMB (@lem7234613) (@lem7234612)). Qed.
Lemma lem7234615 : term82 = term67.
Proof. exact (MK_COMB (@lem7234614) (@lem7234602)). Qed.
Lemma lem7234617 (m : nat) : (term83 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7234618 : term67 = term2.
Proof. exact (@lem7234617 term30). Qed.
Lemma lem7234619 : term82 = term2.
Proof. exact (TRANS (@lem7234615) (@lem7234618)). Qed.
Lemma lem7234620 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234621 : term84 = term85.
Proof. exact (MK_COMB (@lem7234620) (@lem7234619)). Qed.
Lemma lem7234622 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7234623 : term86 = term87.
Proof. exact (MK_COMB (@lem7234621) (@lem7234622)). Qed.
Lemma lem7234625 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7234626 : term87 = term2.
Proof. exact (@lem7234625 term30). Qed.
Lemma lem7234627 : term86 = term2.
Proof. exact (TRANS (@lem7234623) (@lem7234626)). Qed.
Lemma lem7234629 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234630 : term38 = term39.
Proof. exact (@lem7234629 term30 term30). Qed.
Lemma lem7234631 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234632 : term41 = term30.
Proof. exact (EQ_MP (@lem7234631) (@lem940073)). Qed.
Lemma lem7234633 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234634 : term39 = term35.
Proof. exact (MK_COMB (@lem7234633) (@lem7234632)). Qed.
Lemma lem7234635 : term38 = term35.
Proof. exact (TRANS (@lem7234630) (@lem7234634)). Qed.
Lemma lem7234636 : term85 = term85.
Proof. exact (eq_refl term85). Qed.
Lemma lem7234637 : term89 = term87.
Proof. exact (MK_COMB (@lem7234636) (@lem7234635)). Qed.
Lemma lem7234639 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7234640 : term87 = term2.
Proof. exact (@lem7234639 term30). Qed.
Lemma lem7234641 : term89 = term2.
Proof. exact (TRANS (@lem7234637) (@lem7234640)). Qed.
Lemma lem7234642 : term2 = term89.
Proof. exact (SYM (@lem7234641)). Qed.
Lemma lem7234643 : term86 = term89.
Proof. exact (TRANS (@lem7234627) (@lem7234642)). Qed.
Lemma lem7234644 : term68 = term90.
Proof. exact (@lem7234594 (@lem7234643)). Qed.
Lemma lem7234645 : term67 = term90.
Proof. exact (TRANS (@lem7234560) (@lem7234644)). Qed.
Lemma lem7234647 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7234648 : term90 = term2.
Proof. exact (@lem7234647 term2). Qed.
Lemma lem7234649 : term67 = term2.
Proof. exact (TRANS (@lem7234645) (@lem7234648)). Qed.
Lemma lem7234650 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234651 : term91 = term85.
Proof. exact (MK_COMB (@lem7234650) (@lem7234649)). Qed.
Lemma lem7234652 (f : nat -> real) (m : nat) : (f m) = (f m).
Proof. exact (eq_refl (f m)). Qed.
Lemma lem7234653 (f : nat -> real) (m : nat) : (term281 f m) = (term282 f m).
Proof. exact (MK_COMB (@lem7234651) (@lem7234652 f m)). Qed.
Lemma lem7234654 (f : nat -> real) (m : nat) : (term280 f m) = (term282 f m).
Proof. exact (TRANS (@lem7234551 f m) (@lem7234653 f m)). Qed.
Lemma lem7234655 (f : nat -> real) (m : nat) : (term282 f m) = term2.
Proof. exact (@lem1982719 (f m)). Qed.
Lemma lem7234656 (f : nat -> real) (m : nat) : (term280 f m) = term2.
Proof. exact (TRANS (@lem7234654 f m) (@lem7234655 f m)). Qed.
Lemma lem7234657 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7234658 (f : nat -> real) (m : nat) : (term283 f m) = term94.
Proof. exact (MK_COMB (@lem7234657) (@lem7234656 f m)). Qed.
Lemma lem7234659 (f : nat -> real) (n : nat) : (term284 f n) = (term285 f n).
Proof. exact (@lem1982713 term24 (term128 f n)). Qed.
Lemma lem7234661 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7234662 : term35 = term45.
Proof. exact (@lem7234661 term30). Qed.
Lemma lem7234664 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234665 : term24 = term29.
Proof. exact (@lem7234664 term30). Qed.
Lemma lem7234666 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7234667 : term65 = term66.
Proof. exact (MK_COMB (@lem7234666) (@lem7234665)). Qed.
Lemma lem7234668 : term67 = term68.
Proof. exact (MK_COMB (@lem7234667) (@lem7234662)). Qed.
Lemma lem7234669 : term69.
Proof. exact (@lem1981473 term24 term35 term35 term35 term2 term35). Qed.
Lemma lem7234671 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7234672 : term71 = term72.
Proof. exact (@lem7234671 (NUMERAL 0) term30). Qed.
Lemma lem7234673 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7234674 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7234675 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7234674 h1) (fun h1 : term72 = True => @lem7234673)). Qed.
Lemma lem7234676 : term72 = True.
Proof. exact (EQ_MP (@lem7234675) (@lem7234673)). Qed.
Lemma lem7234677 : term71 = True.
Proof. exact (TRANS (@lem7234672) (@lem7234676)). Qed.
Lemma lem7234678 : True = term71.
Proof. exact (SYM (@lem7234677)). Qed.
Lemma lem7234679 : term71.
Proof. exact (EQ_MP (@lem7234678) (@lem0)). Qed.
Lemma lem7234680 : term74.
Proof. exact (@lem7234669 (@lem7234679)). Qed.
Lemma lem7234682 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7234683 : term71 = term72.
Proof. exact (@lem7234682 (NUMERAL 0) term30). Qed.
Lemma lem7234684 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7234685 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7234686 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7234685 h1) (fun h1 : term72 = True => @lem7234684)). Qed.
Lemma lem7234687 : term72 = True.
Proof. exact (EQ_MP (@lem7234686) (@lem7234684)). Qed.
Lemma lem7234688 : term71 = True.
Proof. exact (TRANS (@lem7234683) (@lem7234687)). Qed.
Lemma lem7234689 : True = term71.
Proof. exact (SYM (@lem7234688)). Qed.
Lemma lem7234690 : term71.
Proof. exact (EQ_MP (@lem7234689) (@lem0)). Qed.
Lemma lem7234691 : term75.
Proof. exact (@lem7234680 (@lem7234690)). Qed.
Lemma lem7234693 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7234694 : term71 = term72.
Proof. exact (@lem7234693 (NUMERAL 0) term30). Qed.
Lemma lem7234695 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7234696 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7234697 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7234696 h1) (fun h1 : term72 = True => @lem7234695)). Qed.
Lemma lem7234698 : term72 = True.
Proof. exact (EQ_MP (@lem7234697) (@lem7234695)). Qed.
Lemma lem7234699 : term71 = True.
Proof. exact (TRANS (@lem7234694) (@lem7234698)). Qed.
Lemma lem7234700 : True = term71.
Proof. exact (SYM (@lem7234699)). Qed.
Lemma lem7234701 : term71.
Proof. exact (EQ_MP (@lem7234700) (@lem0)). Qed.
Lemma lem7234702 : term76.
Proof. exact (@lem7234691 (@lem7234701)). Qed.
Lemma lem7234704 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234705 : term38 = term39.
Proof. exact (@lem7234704 term30 term30). Qed.
Lemma lem7234706 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234707 : term41 = term30.
Proof. exact (EQ_MP (@lem7234706) (@lem940073)). Qed.
Lemma lem7234708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234709 : term39 = term35.
Proof. exact (MK_COMB (@lem7234708) (@lem7234707)). Qed.
Lemma lem7234710 : term38 = term35.
Proof. exact (TRANS (@lem7234705) (@lem7234709)). Qed.
Lemma lem7234712 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7234713 : term79 = term80.
Proof. exact (@lem7234712 term30 term30). Qed.
Lemma lem7234714 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234715 : term41 = term30.
Proof. exact (EQ_MP (@lem7234714) (@lem940073)). Qed.
Lemma lem7234716 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234717 : term39 = term35.
Proof. exact (MK_COMB (@lem7234716) (@lem7234715)). Qed.
Lemma lem7234718 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7234719 : term80 = term24.
Proof. exact (MK_COMB (@lem7234718) (@lem7234717)). Qed.
Lemma lem7234720 : term79 = term24.
Proof. exact (TRANS (@lem7234713) (@lem7234719)). Qed.
Lemma lem7234721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7234722 : term81 = term65.
Proof. exact (MK_COMB (@lem7234721) (@lem7234720)). Qed.
Lemma lem7234723 : term82 = term67.
Proof. exact (MK_COMB (@lem7234722) (@lem7234710)). Qed.
Lemma lem7234725 (m : nat) : (term83 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7234726 : term67 = term2.
Proof. exact (@lem7234725 term30). Qed.
Lemma lem7234727 : term82 = term2.
Proof. exact (TRANS (@lem7234723) (@lem7234726)). Qed.
Lemma lem7234728 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234729 : term84 = term85.
Proof. exact (MK_COMB (@lem7234728) (@lem7234727)). Qed.
Lemma lem7234730 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7234731 : term86 = term87.
Proof. exact (MK_COMB (@lem7234729) (@lem7234730)). Qed.
Lemma lem7234733 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7234734 : term87 = term2.
Proof. exact (@lem7234733 term30). Qed.
Lemma lem7234735 : term86 = term2.
Proof. exact (TRANS (@lem7234731) (@lem7234734)). Qed.
Lemma lem7234737 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234738 : term38 = term39.
Proof. exact (@lem7234737 term30 term30). Qed.
Lemma lem7234739 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234740 : term41 = term30.
Proof. exact (EQ_MP (@lem7234739) (@lem940073)). Qed.
Lemma lem7234741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234742 : term39 = term35.
Proof. exact (MK_COMB (@lem7234741) (@lem7234740)). Qed.
Lemma lem7234743 : term38 = term35.
Proof. exact (TRANS (@lem7234738) (@lem7234742)). Qed.
Lemma lem7234744 : term85 = term85.
Proof. exact (eq_refl term85). Qed.
Lemma lem7234745 : term89 = term87.
Proof. exact (MK_COMB (@lem7234744) (@lem7234743)). Qed.
Lemma lem7234747 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7234748 : term87 = term2.
Proof. exact (@lem7234747 term30). Qed.
Lemma lem7234749 : term89 = term2.
Proof. exact (TRANS (@lem7234745) (@lem7234748)). Qed.
Lemma lem7234750 : term2 = term89.
Proof. exact (SYM (@lem7234749)). Qed.
Lemma lem7234751 : term86 = term89.
Proof. exact (TRANS (@lem7234735) (@lem7234750)). Qed.
Lemma lem7234752 : term68 = term90.
Proof. exact (@lem7234702 (@lem7234751)). Qed.
Lemma lem7234753 : term67 = term90.
Proof. exact (TRANS (@lem7234668) (@lem7234752)). Qed.
Lemma lem7234755 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7234756 : term90 = term2.
Proof. exact (@lem7234755 term2). Qed.
Lemma lem7234757 : term67 = term2.
Proof. exact (TRANS (@lem7234753) (@lem7234756)). Qed.
Lemma lem7234758 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234759 : term91 = term85.
Proof. exact (MK_COMB (@lem7234758) (@lem7234757)). Qed.
Lemma lem7234760 (f : nat -> real) (n : nat) : (term128 f n) = (term128 f n).
Proof. exact (eq_refl (term128 f n)). Qed.
Lemma lem7234761 (f : nat -> real) (n : nat) : (term285 f n) = (term286 f n).
Proof. exact (MK_COMB (@lem7234759) (@lem7234760 f n)). Qed.
Lemma lem7234762 (f : nat -> real) (n : nat) : (term284 f n) = (term286 f n).
Proof. exact (TRANS (@lem7234659 f n) (@lem7234761 f n)). Qed.
Lemma lem7234763 (f : nat -> real) (n : nat) : (term286 f n) = term2.
Proof. exact (@lem1982719 (term128 f n)). Qed.
Lemma lem7234764 (f : nat -> real) (n : nat) : (term284 f n) = term2.
Proof. exact (TRANS (@lem7234762 f n) (@lem7234763 f n)). Qed.
Lemma lem7234765 (m : nat) (f : nat -> real) (n : nat) : (term279 m f n) = term96.
Proof. exact (MK_COMB (@lem7234658 f m) (@lem7234764 f n)). Qed.
Lemma lem7234766 (m : nat) (f : nat -> real) (n : nat) : (term278 m f n) = term96.
Proof. exact (TRANS (@lem7234550 m f n) (@lem7234765 m f n)). Qed.
Lemma lem7234767 : term96 = term2.
Proof. exact (@lem1982721 term2). Qed.
Lemma lem7234768 (m : nat) (f : nat -> real) (n : nat) : (term278 m f n) = term2.
Proof. exact (TRANS (@lem7234766 m f n) (@lem7234767)). Qed.
Lemma lem7234769 (m : nat) (f : nat -> real) (n : nat) : (term271 m f n) = term2.
Proof. exact (TRANS (@lem7234549 m f n) (@lem7234768 m f n)). Qed.
Lemma lem7234770 (m : nat) (f : nat -> real) (n : nat) : (term270 m f n) = term2.
Proof. exact (TRANS (@lem7234498 m f n) (@lem7234769 m f n)). Qed.
Lemma lem7234771 (n : nat) (f : nat -> real) (m : nat) : (term269 n f m) = term2.
Proof. exact (TRANS (@lem7234497 m f n) (@lem7234770 m f n)). Qed.
Lemma lem7234772 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7234773 (n : nat) (f : nat -> real) (m : nat) : (term287 n f m) = term98.
Proof. exact (MK_COMB (@lem7234772) (@lem7234771 n f m)). Qed.
Lemma lem7234774 : term98 = term99.
Proof. exact (@lem1982785 term2). Qed.
Lemma lem7234776 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7234777 : term2 = term90.
Proof. exact (@lem7234776 (NUMERAL 0)). Qed.
Lemma lem7234779 (x : nat) : (term27 x) = (term28 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7234780 : term24 = term29.
Proof. exact (@lem7234779 term30). Qed.
Lemma lem7234781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7234782 : term21 = term31.
Proof. exact (MK_COMB (@lem7234781) (@lem7234780)). Qed.
Lemma lem7234783 : term99 = term100.
Proof. exact (MK_COMB (@lem7234782) (@lem7234777)). Qed.
Lemma lem7234784 : term100 = term101.
Proof. exact (@lem1981613 term24 term2 term35 term35). Qed.
Lemma lem7234786 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7234787 : term38 = term39.
Proof. exact (@lem7234786 term30 term30). Qed.
Lemma lem7234788 : (term40 = (BIT1 0)) = (term41 = term30).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7234789 : term41 = term30.
Proof. exact (EQ_MP (@lem7234788) (@lem940073)). Qed.
Lemma lem7234790 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7234791 : term39 = term35.
Proof. exact (MK_COMB (@lem7234790) (@lem7234789)). Qed.
Lemma lem7234792 : term38 = term35.
Proof. exact (TRANS (@lem7234787) (@lem7234791)). Qed.
Lemma lem7234794 (x : nat) : (term102 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7234795 : term99 = term2.
Proof. exact (@lem7234794 term30). Qed.
Lemma lem7234796 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7234797 : term103 = term104.
Proof. exact (MK_COMB (@lem7234796) (@lem7234795)). Qed.
Lemma lem7234798 : term101 = term90.
Proof. exact (MK_COMB (@lem7234797) (@lem7234792)). Qed.
Lemma lem7234799 : term100 = term90.
Proof. exact (TRANS (@lem7234784) (@lem7234798)). Qed.
Lemma lem7234800 : term99 = term90.
Proof. exact (TRANS (@lem7234783) (@lem7234799)). Qed.
Lemma lem7234802 (x : real) : (term46 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7234803 : term90 = term2.
Proof. exact (@lem7234802 term2). Qed.
Lemma lem7234804 : term99 = term2.
Proof. exact (TRANS (@lem7234800) (@lem7234803)). Qed.
Lemma lem7234805 : term98 = term2.
Proof. exact (TRANS (@lem7234774) (@lem7234804)). Qed.
Lemma lem7234806 (n : nat) (f : nat -> real) (m : nat) : (term288 n f m) = (term288 n f m).
Proof. exact (eq_refl (term288 n f m)). Qed.
Lemma lem7234807 (n : nat) (f : nat -> real) (m : nat) : ((term287 n f m) = term98) = ((term287 n f m) = term2).
Proof. exact (MK_COMB (@lem7234806 n f m) (@lem7234805)). Qed.
Lemma lem7234808 (n : nat) (f : nat -> real) (m : nat) : (term287 n f m) = term2.
Proof. exact (EQ_MP (@lem7234807 n f m) (@lem7234773 n f m)). Qed.
Lemma lem7234809 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7234810 (n : nat) (f : nat -> real) (m : nat) : (term289 n f m) = term107.
Proof. exact (MK_COMB (@lem7234809) (@lem7234808 n f m)). Qed.
Lemma lem7234811 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234812 (n : nat) (f : nat -> real) (m : nat) : (term290 n f m) = term109.
Proof. exact (MK_COMB (@lem7234810 n f m) (@lem7234811)). Qed.
Lemma lem7234813 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7234814 (n : nat) (f : nat -> real) (m : nat) : (term291 n f m) = term107.
Proof. exact (MK_COMB (@lem7234813) (@lem7234771 n f m)). Qed.
Lemma lem7234815 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7234816 (n : nat) (f : nat -> real) (m : nat) : (term292 n f m) = term109.
Proof. exact (MK_COMB (@lem7234814 n f m) (@lem7234815)). Qed.
Lemma lem7234817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7234818 (n : nat) (f : nat -> real) (m : nat) : (term293 n f m) = term113.
Proof. exact (MK_COMB (@lem7234817) (@lem7234816 n f m)). Qed.
Lemma lem7234819 (n : nat) (f : nat -> real) (m : nat) : (term248 n f m) = term114.
Proof. exact (MK_COMB (@lem7234818 n f m) (@lem7234812 n f m)). Qed.
Lemma lem7234820 (n : nat) (f : nat -> real) (m : nat) : (term233 n f m) = term114.
Proof. exact (TRANS (@lem7234319 n f m) (@lem7234819 n f m)). Qed.
Lemma lem7234822 (m : nat) (n : nat) : (term294 m n) = (term294 m n).
Proof. exact (eq_refl (term294 m n)). Qed.
Lemma lem7234823 (f : nat -> real) (m : nat) (n : nat) : (term243 n f m) = (term295 m n).
Proof. exact (MK_COMB (@lem7234822 m n) (@lem7234820 n f m)). Qed.
Lemma lem7234824 (f : nat -> real) (m : nat) : (term244 f m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem7234823 f m n)). Qed.
Lemma lem7234825 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234826 (f : nat -> real) (m : nat) : (term245 f m) = (term297 m).
Proof. exact (MK_COMB (@lem7234825) (@lem7234824 f m)). Qed.
Lemma lem7234827 (f : nat -> real) : (term246 f) = term298.
Proof. exact (fun_ext (fun m : nat => @lem7234826 f m)). Qed.
Lemma lem7234828 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234829 (f : nat -> real) : (term247 f) = term299.
Proof. exact (MK_COMB (@lem7234828) (@lem7234827 f)). Qed.
Lemma lem7234830 (f : nat -> real) : (term215 f) = term299.
Proof. exact (TRANS (@lem7234317 f) (@lem7234829 f)). Qed.
Lemma lem7234856 {A : Type'} (P : A -> Prop) (Q : Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem7234857 (P : nat -> Prop) (Q : Prop) : (term302 P Q) = (term303 P Q).
Proof. exact (@lem7234856 nat P Q). Qed.
Lemma lem7234858 (m : nat) : (term304 m) = (term305 m).
Proof. exact (@lem7234857 (term306 m) term114). Qed.
Lemma lem7234859 (m : nat) (n : nat) : (term307 m n) = (Peano.le m n).
Proof. exact (eq_refl (term307 m n)). Qed.
Lemma lem7234860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7234861 (m : nat) (n : nat) : (term308 m n) = (term294 m n).
Proof. exact (MK_COMB (@lem7234860) (@lem7234859 m n)). Qed.
Lemma lem7234862 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem7234863 (m : nat) (n : nat) : (term309 m n) = (term295 m n).
Proof. exact (MK_COMB (@lem7234861 m n) (@lem7234862)). Qed.
Lemma lem7234864 (m : nat) : (term310 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem7234863 m n)). Qed.
Lemma lem7234865 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234866 (m : nat) : (term304 m) = (term297 m).
Proof. exact (MK_COMB (@lem7234865) (@lem7234864 m)). Qed.
Lemma lem7234867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7234868 (m : nat) : (term311 m) = (term312 m).
Proof. exact (MK_COMB (@lem7234867) (@lem7234866 m)). Qed.
Lemma lem7234869 (m : nat) (n : nat) : (term307 m n) = (Peano.le m n).
Proof. exact (eq_refl (term307 m n)). Qed.
Lemma lem7234870 (m : nat) : (term313 m) = (term306 m).
Proof. exact (fun_ext (fun n : nat => @lem7234869 m n)). Qed.
Lemma lem7234871 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234872 (m : nat) : (term314 m) = (term315 m).
Proof. exact (MK_COMB (@lem7234871) (@lem7234870 m)). Qed.
Lemma lem7234873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7234874 (m : nat) : (term316 m) = (term317 m).
Proof. exact (MK_COMB (@lem7234873) (@lem7234872 m)). Qed.
Lemma lem7234875 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem7234876 (m : nat) : (term305 m) = (term318 m).
Proof. exact (MK_COMB (@lem7234874 m) (@lem7234875)). Qed.
Lemma lem7234877 (m : nat) : ((term304 m) = (term305 m)) = ((term297 m) = (term318 m)).
Proof. exact (MK_COMB (@lem7234868 m) (@lem7234876 m)). Qed.
Lemma lem7234878 (m : nat) : (term297 m) = (term318 m).
Proof. exact (EQ_MP (@lem7234877 m) (@lem7234858 m)). Qed.
Lemma lem7234883 : term298 = term319.
Proof. exact (fun_ext (fun m : nat => @lem7234878 m)). Qed.
Lemma lem7234884 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234885 : term299 = term320.
Proof. exact (MK_COMB (@lem7234884) (@lem7234883)). Qed.
Lemma lem7234907 {A : Type'} (P : A -> Prop) (Q : Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem7234908 (P : nat -> Prop) (Q : Prop) : (term302 P Q) = (term303 P Q).
Proof. exact (@lem7234907 nat P Q). Qed.
Lemma lem7234909 : term321 = term322.
Proof. exact (@lem7234908 term323 term114). Qed.
Lemma lem7234910 (m : nat) : (term324 m) = (term315 m).
Proof. exact (eq_refl (term324 m)). Qed.
Lemma lem7234911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7234912 (m : nat) : (term325 m) = (term317 m).
Proof. exact (MK_COMB (@lem7234911) (@lem7234910 m)). Qed.
Lemma lem7234913 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem7234914 (m : nat) : (term326 m) = (term318 m).
Proof. exact (MK_COMB (@lem7234912 m) (@lem7234913)). Qed.
Lemma lem7234915 : term327 = term319.
Proof. exact (fun_ext (fun m : nat => @lem7234914 m)). Qed.
Lemma lem7234916 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234917 : term321 = term320.
Proof. exact (MK_COMB (@lem7234916) (@lem7234915)). Qed.
Lemma lem7234918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7234919 : term328 = term329.
Proof. exact (MK_COMB (@lem7234918) (@lem7234917)). Qed.
Lemma lem7234920 (m : nat) : (term324 m) = (term315 m).
Proof. exact (eq_refl (term324 m)). Qed.
Lemma lem7234921 : term330 = term323.
Proof. exact (fun_ext (fun m : nat => @lem7234920 m)). Qed.
Lemma lem7234922 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234923 : term331 = term332.
Proof. exact (MK_COMB (@lem7234922) (@lem7234921)). Qed.
Lemma lem7234924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7234925 : term333 = term334.
Proof. exact (MK_COMB (@lem7234924) (@lem7234923)). Qed.
Lemma lem7234926 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem7234927 : term322 = term335.
Proof. exact (MK_COMB (@lem7234925) (@lem7234926)). Qed.
Lemma lem7234928 : (term321 = term322) = (term320 = term335).
Proof. exact (MK_COMB (@lem7234919) (@lem7234927)). Qed.
Lemma lem7234929 : term320 = term335.
Proof. exact (EQ_MP (@lem7234928) (@lem7234909)). Qed.
Lemma lem7234938 : term299 = term335.
Proof. exact (TRANS (@lem7234885) (@lem7234929)). Qed.
Lemma lem7234940 {A : Type'} (P : A -> Prop) (Q : Prop) : (term301 A P Q) = (term300 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7234941 (P : nat -> Prop) (Q : Prop) : (term303 P Q) = (term302 P Q).
Proof. exact (@lem7234940 nat P Q). Qed.
Lemma lem7234942 : term322 = term321.
Proof. exact (@lem7234941 term323 term114). Qed.
Lemma lem7234943 (m : nat) : (term324 m) = (term315 m).
Proof. exact (eq_refl (term324 m)). Qed.
Lemma lem7234944 : term330 = term323.
Proof. exact (fun_ext (fun m : nat => @lem7234943 m)). Qed.
Lemma lem7234945 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234946 : term331 = term332.
Proof. exact (MK_COMB (@lem7234945) (@lem7234944)). Qed.
Lemma lem7234947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7234948 : term333 = term334.
Proof. exact (MK_COMB (@lem7234947) (@lem7234946)). Qed.
Lemma lem7234949 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem7234950 : term322 = term335.
Proof. exact (MK_COMB (@lem7234948) (@lem7234949)). Qed.
Lemma lem7234951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7234952 : term336 = term337.
Proof. exact (MK_COMB (@lem7234951) (@lem7234950)). Qed.
Lemma lem7234953 (m : nat) : (term324 m) = (term315 m).
Proof. exact (eq_refl (term324 m)). Qed.
Lemma lem7234954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7234955 (m : nat) : (term325 m) = (term317 m).
Proof. exact (MK_COMB (@lem7234954) (@lem7234953 m)). Qed.
Lemma lem7234956 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem7234957 (m : nat) : (term326 m) = (term318 m).
Proof. exact (MK_COMB (@lem7234955 m) (@lem7234956)). Qed.
Lemma lem7234958 : term327 = term319.
Proof. exact (fun_ext (fun m : nat => @lem7234957 m)). Qed.
Lemma lem7234959 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234960 : term321 = term320.
Proof. exact (MK_COMB (@lem7234959) (@lem7234958)). Qed.
Lemma lem7234961 : (term322 = term321) = (term335 = term320).
Proof. exact (MK_COMB (@lem7234952) (@lem7234960)). Qed.
Lemma lem7234962 : term335 = term320.
Proof. exact (EQ_MP (@lem7234961) (@lem7234942)). Qed.
Lemma lem7234964 {A : Type'} (P : A -> Prop) (Q : Prop) : (term301 A P Q) = (term300 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7234965 (P : nat -> Prop) (Q : Prop) : (term303 P Q) = (term302 P Q).
Proof. exact (@lem7234964 nat P Q). Qed.
Lemma lem7234966 (m : nat) : (term305 m) = (term304 m).
Proof. exact (@lem7234965 (term306 m) term114). Qed.
Lemma lem7234967 (m : nat) (n : nat) : (term307 m n) = (Peano.le m n).
Proof. exact (eq_refl (term307 m n)). Qed.
Lemma lem7234968 (m : nat) : (term313 m) = (term306 m).
Proof. exact (fun_ext (fun n : nat => @lem7234967 m n)). Qed.
Lemma lem7234969 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234970 (m : nat) : (term314 m) = (term315 m).
Proof. exact (MK_COMB (@lem7234969) (@lem7234968 m)). Qed.
Lemma lem7234971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7234972 (m : nat) : (term316 m) = (term317 m).
Proof. exact (MK_COMB (@lem7234971) (@lem7234970 m)). Qed.
Lemma lem7234973 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem7234974 (m : nat) : (term305 m) = (term318 m).
Proof. exact (MK_COMB (@lem7234972 m) (@lem7234973)). Qed.
Lemma lem7234975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7234976 (m : nat) : (term338 m) = (term339 m).
Proof. exact (MK_COMB (@lem7234975) (@lem7234974 m)). Qed.
Lemma lem7234977 (m : nat) (n : nat) : (term307 m n) = (Peano.le m n).
Proof. exact (eq_refl (term307 m n)). Qed.
Lemma lem7234978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7234979 (m : nat) (n : nat) : (term308 m n) = (term294 m n).
Proof. exact (MK_COMB (@lem7234978) (@lem7234977 m n)). Qed.
Lemma lem7234980 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem7234981 (m : nat) (n : nat) : (term309 m n) = (term295 m n).
Proof. exact (MK_COMB (@lem7234979 m n) (@lem7234980)). Qed.
Lemma lem7234982 (m : nat) : (term310 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem7234981 m n)). Qed.
Lemma lem7234983 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234984 (m : nat) : (term304 m) = (term297 m).
Proof. exact (MK_COMB (@lem7234983) (@lem7234982 m)). Qed.
Lemma lem7234985 (m : nat) : ((term305 m) = (term304 m)) = ((term318 m) = (term297 m)).
Proof. exact (MK_COMB (@lem7234976 m) (@lem7234984 m)). Qed.
Lemma lem7234986 (m : nat) : (term318 m) = (term297 m).
Proof. exact (EQ_MP (@lem7234985 m) (@lem7234966 m)). Qed.
Lemma lem7234987 : term319 = term298.
Proof. exact (fun_ext (fun m : nat => @lem7234986 m)). Qed.
Lemma lem7234988 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7234989 : term320 = term299.
Proof. exact (MK_COMB (@lem7234988) (@lem7234987)). Qed.
Lemma lem7234990 : term335 = term299.
Proof. exact (TRANS (@lem7234962) (@lem7234989)). Qed.
Lemma lem7234991 : term299 = term299.
Proof. exact (TRANS (@lem7234938) (@lem7234990)). Qed.
Lemma lem7234994 (f : nat -> real) : (term215 f) = term299.
Proof. exact (TRANS (@lem7234830 f) (@lem7234991)). Qed.
Lemma lem7235011 (m : nat) (n : nat) : (term295 m n) = (term340 m n).
Proof. exact (@lem19158 term109 (Peano.le m n) term109). Qed.
Lemma lem7235012 (m : nat) : (term296 m) = (term341 m).
Proof. exact (fun_ext (fun n : nat => @lem7235011 m n)). Qed.
Lemma lem7235013 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7235014 (m : nat) : (term297 m) = (term342 m).
Proof. exact (MK_COMB (@lem7235013) (@lem7235012 m)). Qed.
Lemma lem7235015 : term298 = term343.
Proof. exact (fun_ext (fun m : nat => @lem7235014 m)). Qed.
Lemma lem7235016 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7235017 : term299 = term344.
Proof. exact (MK_COMB (@lem7235016) (@lem7235015)). Qed.
Lemma lem7235018 (f : nat -> real) : (term215 f) = term344.
Proof. exact (TRANS (@lem7234994 f) (@lem7235017)). Qed.
Lemma lem7235028 (m : nat) (n : nat) (h1 : term340 m n) : term340 m n.
Proof. exact (h1). Qed.
Lemma lem7235029 (m : nat) (n : nat) (h1 : term345 m n) : term345 m n.
Proof. exact (h1). Qed.
Lemma lem7235030 (m : nat) (n : nat) (h1 : term345 m n) : term109.
Proof. exact (proj2 (@lem7235029 m n h1)). Qed.
Lemma lem7235033 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7235034 : term109 = term115.
Proof. exact (@lem7235033 term2 term2). Qed.
Lemma lem7235036 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7235037 : term2 = term90.
Proof. exact (@lem7235036 (NUMERAL 0)). Qed.
Lemma lem7235039 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7235040 : term2 = term90.
Proof. exact (@lem7235039 (NUMERAL 0)). Qed.
Lemma lem7235041 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7235042 : term116 = term117.
Proof. exact (MK_COMB (@lem7235041) (@lem7235040)). Qed.
Lemma lem7235043 : term115 = term118.
Proof. exact (MK_COMB (@lem7235042) (@lem7235037)). Qed.
Lemma lem7235044 : term119.
Proof. exact (@lem1980255 term2 term35 term2 term35). Qed.
Lemma lem7235046 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7235047 : term71 = term72.
Proof. exact (@lem7235046 (NUMERAL 0) term30). Qed.
Lemma lem7235048 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7235049 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7235050 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7235049 h1) (fun h1 : term72 = True => @lem7235048)). Qed.
Lemma lem7235051 : term72 = True.
Proof. exact (EQ_MP (@lem7235050) (@lem7235048)). Qed.
Lemma lem7235052 : term71 = True.
Proof. exact (TRANS (@lem7235047) (@lem7235051)). Qed.
Lemma lem7235053 : True = term71.
Proof. exact (SYM (@lem7235052)). Qed.
Lemma lem7235054 : term71.
Proof. exact (EQ_MP (@lem7235053) (@lem0)). Qed.
Lemma lem7235055 : term120.
Proof. exact (@lem7235044 (@lem7235054)). Qed.
Lemma lem7235057 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7235058 : term71 = term72.
Proof. exact (@lem7235057 (NUMERAL 0) term30). Qed.
Lemma lem7235059 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7235060 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7235061 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7235060 h1) (fun h1 : term72 = True => @lem7235059)). Qed.
Lemma lem7235062 : term72 = True.
Proof. exact (EQ_MP (@lem7235061) (@lem7235059)). Qed.
Lemma lem7235063 : term71 = True.
Proof. exact (TRANS (@lem7235058) (@lem7235062)). Qed.
Lemma lem7235064 : True = term71.
Proof. exact (SYM (@lem7235063)). Qed.
Lemma lem7235065 : term71.
Proof. exact (EQ_MP (@lem7235064) (@lem0)). Qed.
Lemma lem7235066 : term118 = term121.
Proof. exact (@lem7235055 (@lem7235065)). Qed.
Lemma lem7235068 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7235069 : term87 = term2.
Proof. exact (@lem7235068 term30). Qed.
Lemma lem7235071 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7235072 : term87 = term2.
Proof. exact (@lem7235071 term30). Qed.
Lemma lem7235073 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7235074 : term122 = term116.
Proof. exact (MK_COMB (@lem7235073) (@lem7235072)). Qed.
Lemma lem7235075 : term121 = term115.
Proof. exact (MK_COMB (@lem7235074) (@lem7235069)). Qed.
Lemma lem7235077 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7235078 : term115 = term123.
Proof. exact (@lem7235077 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7235079 : term123 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7235080 : term115 = False.
Proof. exact (TRANS (@lem7235078) (@lem7235079)). Qed.
Lemma lem7235081 : term121 = False.
Proof. exact (TRANS (@lem7235075) (@lem7235080)). Qed.
Lemma lem7235082 : term118 = False.
Proof. exact (TRANS (@lem7235066) (@lem7235081)). Qed.
Lemma lem7235083 : term115 = False.
Proof. exact (TRANS (@lem7235043) (@lem7235082)). Qed.
Lemma lem7235084 : term109 = False.
Proof. exact (TRANS (@lem7235034) (@lem7235083)). Qed.
Lemma lem7235085 (m : nat) (n : nat) (h1 : term345 m n) : False.
Proof. exact (EQ_MP (@lem7235084) (@lem7235030 m n h1)). Qed.
Lemma lem7235086 (m : nat) (n : nat) (h1 : term345 m n) : term345 m n.
Proof. exact (h1). Qed.
Lemma lem7235087 (m : nat) (n : nat) (h1 : term345 m n) : term109.
Proof. exact (proj2 (@lem7235086 m n h1)). Qed.
Lemma lem7235090 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7235091 : term109 = term115.
Proof. exact (@lem7235090 term2 term2). Qed.
Lemma lem7235093 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7235094 : term2 = term90.
Proof. exact (@lem7235093 (NUMERAL 0)). Qed.
Lemma lem7235096 (x : nat) : (real_of_num x) = (term64 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7235097 : term2 = term90.
Proof. exact (@lem7235096 (NUMERAL 0)). Qed.
Lemma lem7235098 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7235099 : term116 = term117.
Proof. exact (MK_COMB (@lem7235098) (@lem7235097)). Qed.
Lemma lem7235100 : term115 = term118.
Proof. exact (MK_COMB (@lem7235099) (@lem7235094)). Qed.
Lemma lem7235101 : term119.
Proof. exact (@lem1980255 term2 term35 term2 term35). Qed.
Lemma lem7235103 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7235104 : term71 = term72.
Proof. exact (@lem7235103 (NUMERAL 0) term30). Qed.
Lemma lem7235105 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7235106 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7235107 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7235106 h1) (fun h1 : term72 = True => @lem7235105)). Qed.
Lemma lem7235108 : term72 = True.
Proof. exact (EQ_MP (@lem7235107) (@lem7235105)). Qed.
Lemma lem7235109 : term71 = True.
Proof. exact (TRANS (@lem7235104) (@lem7235108)). Qed.
Lemma lem7235110 : True = term71.
Proof. exact (SYM (@lem7235109)). Qed.
Lemma lem7235111 : term71.
Proof. exact (EQ_MP (@lem7235110) (@lem0)). Qed.
Lemma lem7235112 : term120.
Proof. exact (@lem7235101 (@lem7235111)). Qed.
Lemma lem7235114 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7235115 : term71 = term72.
Proof. exact (@lem7235114 (NUMERAL 0) term30). Qed.
Lemma lem7235116 : term73 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7235117 (h1 : term73 = (BIT1 0)) : term72 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7235118 : (term73 = (BIT1 0)) = (term72 = True).
Proof. exact (prop_ext (fun h1 : term73 = (BIT1 0) => @lem7235117 h1) (fun h1 : term72 = True => @lem7235116)). Qed.
Lemma lem7235119 : term72 = True.
Proof. exact (EQ_MP (@lem7235118) (@lem7235116)). Qed.
Lemma lem7235120 : term71 = True.
Proof. exact (TRANS (@lem7235115) (@lem7235119)). Qed.
Lemma lem7235121 : True = term71.
Proof. exact (SYM (@lem7235120)). Qed.
Lemma lem7235122 : term71.
Proof. exact (EQ_MP (@lem7235121) (@lem0)). Qed.
Lemma lem7235123 : term118 = term121.
Proof. exact (@lem7235112 (@lem7235122)). Qed.
Lemma lem7235125 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7235126 : term87 = term2.
Proof. exact (@lem7235125 term30). Qed.
Lemma lem7235128 (x : nat) : (term88 x) = term2.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7235129 : term87 = term2.
Proof. exact (@lem7235128 term30). Qed.
Lemma lem7235130 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7235131 : term122 = term116.
Proof. exact (MK_COMB (@lem7235130) (@lem7235129)). Qed.
Lemma lem7235132 : term121 = term115.
Proof. exact (MK_COMB (@lem7235131) (@lem7235126)). Qed.
Lemma lem7235134 (m : nat) (n : nat) : (term70 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7235135 : term115 = term123.
Proof. exact (@lem7235134 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7235136 : term123 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7235137 : term115 = False.
Proof. exact (TRANS (@lem7235135) (@lem7235136)). Qed.
Lemma lem7235138 : term121 = False.
Proof. exact (TRANS (@lem7235132) (@lem7235137)). Qed.
Lemma lem7235139 : term118 = False.
Proof. exact (TRANS (@lem7235123) (@lem7235138)). Qed.
Lemma lem7235140 : term115 = False.
Proof. exact (TRANS (@lem7235100) (@lem7235139)). Qed.
Lemma lem7235141 : term109 = False.
Proof. exact (TRANS (@lem7235091) (@lem7235140)). Qed.
Lemma lem7235142 (m : nat) (n : nat) (h1 : term345 m n) : False.
Proof. exact (EQ_MP (@lem7235141) (@lem7235087 m n h1)). Qed.
Lemma lem7235143 (m : nat) (n : nat) (h1 : term340 m n) : False.
Proof. exact (or_elim (@lem7235028 m n h1) (fun h0 : term345 m n => @lem7235085 m n h0) (fun h0 : term345 m n => @lem7235142 m n h0)). Qed.
Lemma lem7235145 (m : nat) (n : nat) (h1 : term340 m n) : term340 m n.
Proof. exact (h1). Qed.
Lemma lem7235146 (m : nat) (n : nat) (h1 : term340 m n) : (term340 m n) = False.
Proof. exact (prop_ext (fun h2 : term340 m n => @lem7235143 m n h1) (fun h2 : False => @lem7235145 m n h1)). Qed.
Lemma lem7235147 (m : nat) (n : nat) (h1 : term340 m n) : False.
Proof. exact (EQ_MP (@lem7235146 m n h1) (@lem7235145 m n h1)). Qed.
Lemma lem7235148 (m : nat) (h1 : term342 m) : term342 m.
Proof. exact (h1). Qed.
Lemma lem7235149 (m : nat) (h1 : term342 m) : False.
Proof. exact (ex_elim (@lem7235148 m h1) (fun n : nat => fun h0 : term341 m n => @lem7235147 m n h0)). Qed.
Lemma lem7235150 (h1 : term344) : term344.
Proof. exact (h1). Qed.
Lemma lem7235151 (h1 : term344) : False.
Proof. exact (ex_elim (@lem7235150 h1) (fun m : nat => fun h0 : term343 m => @lem7235149 m h0)). Qed.
Lemma lem7235152 (f : nat -> real) (h1 : term215 f) : term215 f.
Proof. exact (h1). Qed.
Lemma lem7235153 (f : nat -> real) (h1 : term215 f) : term344.
Proof. exact (EQ_MP (@lem7235018 f) (@lem7235152 f h1)). Qed.
Lemma lem7235154 (f : nat -> real) (h1 : term215 f) : term344 = False.
Proof. exact (prop_ext (fun h2 : term344 => @lem7235151 h2) (fun h2 : False => @lem7235153 f h1)). Qed.
Lemma lem7235155 (f : nat -> real) (h1 : term215 f) : False.
Proof. exact (EQ_MP (@lem7235154 f h1) (@lem7235153 f h1)). Qed.
Lemma lem7235156 (f : nat -> real) : term346 f.
Proof. exact (fun h0 : term215 f => @lem7235155 f h0). Qed.
Lemma lem7235157 (f : nat -> real) : term347 f.
Proof. exact (@lem1386578 (term204 f)). Qed.
Lemma lem7235160 (f : nat -> real) : term204 f.
Proof. exact (@lem7235157 f (@lem7235156 f)). Qed.
Lemma lem7235161 (f : nat -> real) : term192 f.
Proof. exact (EQ_MP (@lem7234171 f) (@lem7235160 f)). Qed.
Lemma lem7235162 (f : nat -> real) : term150 f.
Proof. exact (EQ_MP (@lem7234109 f) (@lem7235161 f)). Qed.
Lemma lem7235163 (f : nat -> real) : term149 f.
Proof. exact (EQ_MP (@lem7234043 f) (@lem7235162 f)). Qed.
