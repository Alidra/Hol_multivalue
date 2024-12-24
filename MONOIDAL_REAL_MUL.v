Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONOIDAL_REAL_MUL_term_abbrevs.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm17045_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982733_spec.
Require Import thm1982745_spec.
Require Import thm1982747_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm6910119_spec.
Require Import thm6911417_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6911419 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem6911420 {A : Type'} (op : type1400 A) : (term0 A op) = ((@monoidal A op) = (term1 A op)).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem6911423 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term1 A op).
Proof. exact (EQ_MP (@lem6911420 A op) (@lem6911419 A op)). Qed.
Lemma lem6911424 (op : type1627) : (@monoidal real op) = (term2 op).
Proof. exact (@lem6911423 real op). Qed.
Lemma lem6911425 : (@monoidal real real_mul) = term3.
Proof. exact (@lem6911424 real_mul). Qed.
Lemma lem6911461 : (@neutral real real_mul) = term4.
Proof. exact (EQ_MP (@lem6910119) (@lem6911417)). Qed.
Lemma lem6911462 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6911463 : term5 = term6.
Proof. exact (MK_COMB (@lem6911462) (@lem6911461)). Qed.
Lemma lem6911464 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6911465 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem6911463) (@lem6911464 x)). Qed.
Lemma lem6911466 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6911467 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem6911466) (@lem6911465 x)). Qed.
Lemma lem6911468 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6911469 (x : real) : ((term7 x) = x) = ((term8 x) = x).
Proof. exact (MK_COMB (@lem6911467 x) (@lem6911468 x)). Qed.
Lemma lem6911472 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem6911469 x)). Qed.
Lemma lem6911473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6911474 : term13 = term14.
Proof. exact (MK_COMB (@lem6911473) (@lem6911472)). Qed.
Lemma lem6911479 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem6911480 : term16 = term17.
Proof. exact (MK_COMB (@lem6911479) (@lem6911474)). Qed.
Lemma lem6911483 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem6911484 : term3 = term19.
Proof. exact (MK_COMB (@lem6911483) (@lem6911480)). Qed.
Lemma lem6911487 : (@monoidal real real_mul) = term19.
Proof. exact (TRANS (@lem6911425) (@lem6911484)). Qed.
Lemma lem6911488 : term19 = (@monoidal real real_mul).
Proof. exact (SYM (@lem6911487)). Qed.
Lemma lem6911522 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6911523 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem6911522 (term24 x)). Qed.
Lemma lem6911524 (y : real) (x : real) : (term25 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem6911525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6911527 (y : real) (x : real) : (term26 x y) = (term27 y x).
Proof. exact (MK_COMB (@lem6911525) (@lem6911524 y x)). Qed.
Lemma lem6911528 (x : real) : (term28 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem6911527 y x)). Qed.
Lemma lem6911529 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911530 (x : real) : (term23 x) = (term30 x).
Proof. exact (MK_COMB (@lem6911529) (@lem6911528 x)). Qed.
Lemma lem6911531 (x : real) : (term22 x) = (term30 x).
Proof. exact (TRANS (@lem6911523 x) (@lem6911530 x)). Qed.
Lemma lem6911532 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6911533 : term31 = term32.
Proof. exact (@lem6911532 term33). Qed.
Lemma lem6911534 (x : real) : (term34 x) = (term35 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem6911535 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6911536 (x : real) : (term36 x) = (term22 x).
Proof. exact (MK_COMB (@lem6911535) (@lem6911534 x)). Qed.
Lemma lem6911537 (x : real) : (term36 x) = (term30 x).
Proof. exact (TRANS (@lem6911536 x) (@lem6911531 x)). Qed.
Lemma lem6911538 : term37 = term38.
Proof. exact (fun_ext (fun x : real => @lem6911537 x)). Qed.
Lemma lem6911539 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911540 : term32 = term39.
Proof. exact (MK_COMB (@lem6911539) (@lem6911538)). Qed.
Lemma lem6911541 : term31 = term39.
Proof. exact (TRANS (@lem6911533) (@lem6911540)). Qed.
Lemma lem6911543 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6911544 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (@lem6911543 (term42 x y)). Qed.
Lemma lem6911545 (x : real) (y : real) (z : real) : (term43 x y z) = ((term44 x y z) = (term45 x y z)).
Proof. exact (eq_refl (term43 x y z)). Qed.
Lemma lem6911546 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6911548 (x : real) (y : real) (z : real) : (term46 x y z) = (term47 x y z).
Proof. exact (MK_COMB (@lem6911546) (@lem6911545 x y z)). Qed.
Lemma lem6911549 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (fun_ext (fun z : real => @lem6911548 x y z)). Qed.
Lemma lem6911550 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911551 (x : real) (y : real) : (term41 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem6911550) (@lem6911549 x y)). Qed.
Lemma lem6911552 (x : real) (y : real) : (term40 x y) = (term50 x y).
Proof. exact (TRANS (@lem6911544 x y) (@lem6911551 x y)). Qed.
Lemma lem6911553 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6911554 (x : real) : (term51 x) = (term52 x).
Proof. exact (@lem6911553 (term53 x)). Qed.
Lemma lem6911555 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem6911556 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6911557 (x : real) (y : real) : (term56 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem6911556) (@lem6911555 x y)). Qed.
Lemma lem6911558 (x : real) (y : real) : (term56 x y) = (term50 x y).
Proof. exact (TRANS (@lem6911557 x y) (@lem6911552 x y)). Qed.
Lemma lem6911559 (x : real) : (term57 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem6911558 x y)). Qed.
Lemma lem6911560 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911561 (x : real) : (term52 x) = (term59 x).
Proof. exact (MK_COMB (@lem6911560) (@lem6911559 x)). Qed.
Lemma lem6911562 (x : real) : (term51 x) = (term59 x).
Proof. exact (TRANS (@lem6911554 x) (@lem6911561 x)). Qed.
Lemma lem6911563 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6911564 : term60 = term61.
Proof. exact (@lem6911563 term62). Qed.
Lemma lem6911565 (x : real) : (term63 x) = (term64 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem6911566 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6911567 (x : real) : (term65 x) = (term51 x).
Proof. exact (MK_COMB (@lem6911566) (@lem6911565 x)). Qed.
Lemma lem6911568 (x : real) : (term65 x) = (term59 x).
Proof. exact (TRANS (@lem6911567 x) (@lem6911562 x)). Qed.
Lemma lem6911569 : term66 = term67.
Proof. exact (fun_ext (fun x : real => @lem6911568 x)). Qed.
Lemma lem6911570 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911571 : term61 = term68.
Proof. exact (MK_COMB (@lem6911570) (@lem6911569)). Qed.
Lemma lem6911572 : term60 = term68.
Proof. exact (TRANS (@lem6911564) (@lem6911571)). Qed.
Lemma lem6911574 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6911575 : term69 = term70.
Proof. exact (@lem6911574 term12). Qed.
Lemma lem6911576 (x : real) : (term71 x) = ((term8 x) = x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem6911577 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6911579 (x : real) : (term72 x) = (term73 x).
Proof. exact (MK_COMB (@lem6911577) (@lem6911576 x)). Qed.
Lemma lem6911580 : term74 = term75.
Proof. exact (fun_ext (fun x : real => @lem6911579 x)). Qed.
Lemma lem6911581 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911582 : term70 = term76.
Proof. exact (MK_COMB (@lem6911581) (@lem6911580)). Qed.
Lemma lem6911583 : term69 = term76.
Proof. exact (TRANS (@lem6911575) (@lem6911582)). Qed.
Lemma lem6911584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6911585 : term77 = term78.
Proof. exact (MK_COMB (@lem6911584) (@lem6911572)). Qed.
Lemma lem6911586 : term79 = term80.
Proof. exact (MK_COMB (@lem6911585) (@lem6911583)). Qed.
Lemma lem6911587 : term81 = term79.
Proof. exact (@lem17045 term82 term14). Qed.
Lemma lem6911588 : term81 = term80.
Proof. exact (TRANS (@lem6911587) (@lem6911586)). Qed.
Lemma lem6911589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6911590 : term83 = term84.
Proof. exact (MK_COMB (@lem6911589) (@lem6911541)). Qed.
Lemma lem6911591 : term85 = term86.
Proof. exact (MK_COMB (@lem6911590) (@lem6911588)). Qed.
Lemma lem6911592 : term87 = term85.
Proof. exact (@lem17045 term88 term17). Qed.
Lemma lem6911594 : term87 = term86.
Proof. exact (TRANS (@lem6911592) (@lem6911591)). Qed.
Lemma lem6911597 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (eq_refl (term27 y x)). Qed.
Lemma lem6911598 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem6911597 y x)). Qed.
Lemma lem6911599 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911600 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem6911599) (@lem6911598 x)). Qed.
Lemma lem6911601 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem6911600 x)). Qed.
Lemma lem6911602 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911603 : term39 = term39.
Proof. exact (MK_COMB (@lem6911602) (@lem6911601)). Qed.
Lemma lem6911606 (x : real) (y : real) (z : real) : (term47 x y z) = (term47 x y z).
Proof. exact (eq_refl (term47 x y z)). Qed.
Lemma lem6911607 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (fun_ext (fun z : real => @lem6911606 x y z)). Qed.
Lemma lem6911608 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911609 (x : real) (y : real) : (term50 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem6911608) (@lem6911607 x y)). Qed.
Lemma lem6911610 (x : real) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem6911609 x y)). Qed.
Lemma lem6911611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911612 (x : real) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem6911611) (@lem6911610 x)). Qed.
Lemma lem6911613 : term67 = term67.
Proof. exact (fun_ext (fun x : real => @lem6911612 x)). Qed.
Lemma lem6911614 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911615 : term68 = term68.
Proof. exact (MK_COMB (@lem6911614) (@lem6911613)). Qed.
Lemma lem6911618 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem6911619 : term75 = term75.
Proof. exact (fun_ext (fun x : real => @lem6911618 x)). Qed.
Lemma lem6911620 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911621 : term76 = term76.
Proof. exact (MK_COMB (@lem6911620) (@lem6911619)). Qed.
Lemma lem6911622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6911623 : term78 = term78.
Proof. exact (MK_COMB (@lem6911622) (@lem6911615)). Qed.
Lemma lem6911624 : term80 = term80.
Proof. exact (MK_COMB (@lem6911623) (@lem6911621)). Qed.
Lemma lem6911625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6911626 : term84 = term84.
Proof. exact (MK_COMB (@lem6911625) (@lem6911603)). Qed.
Lemma lem6911627 : term86 = term86.
Proof. exact (MK_COMB (@lem6911626) (@lem6911624)). Qed.
Lemma lem6911628 : term87 = term86.
Proof. exact (TRANS (@lem6911594) (@lem6911627)). Qed.
Lemma lem6911629 (y : real) (x : real) : (term27 y x) = (term89 y x).
Proof. exact (@lem1988318 (real_mul x y) (real_mul y x)). Qed.
Lemma lem6911636 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1982747 x y). Qed.
Lemma lem6911645 (x : real) (y : real) : (term90 x y) = (term90 x y).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem6911646 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (MK_COMB (@lem6911645 x y) (@lem6911636 x y)). Qed.
Lemma lem6911647 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (@lem1982792 (real_mul x y) (real_mul x y)). Qed.
Lemma lem6911651 (x : real) (y : real) : (term93 x y) = (term94 x y).
Proof. exact (@lem1982715 term95 (real_mul x y)). Qed.
Lemma lem6911653 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6911654 : term4 = term97.
Proof. exact (@lem6911653 term98). Qed.
Lemma lem6911656 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6911657 : term95 = term101.
Proof. exact (@lem6911656 term98). Qed.
Lemma lem6911658 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6911659 : term102 = term103.
Proof. exact (MK_COMB (@lem6911658) (@lem6911657)). Qed.
Lemma lem6911660 : term104 = term105.
Proof. exact (MK_COMB (@lem6911659) (@lem6911654)). Qed.
Lemma lem6911661 : term106.
Proof. exact (@lem1981473 term95 term4 term4 term4 term107 term4). Qed.
Lemma lem6911663 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6911664 : term109 = term110.
Proof. exact (@lem6911663 (NUMERAL 0) term98). Qed.
Lemma lem6911665 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6911666 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6911667 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6911666 h1) (fun h1 : term110 = True => @lem6911665)). Qed.
Lemma lem6911668 : term110 = True.
Proof. exact (EQ_MP (@lem6911667) (@lem6911665)). Qed.
Lemma lem6911669 : term109 = True.
Proof. exact (TRANS (@lem6911664) (@lem6911668)). Qed.
Lemma lem6911670 : True = term109.
Proof. exact (SYM (@lem6911669)). Qed.
Lemma lem6911671 : term109.
Proof. exact (EQ_MP (@lem6911670) (@lem0)). Qed.
Lemma lem6911672 : term112.
Proof. exact (@lem6911661 (@lem6911671)). Qed.
Lemma lem6911674 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6911675 : term109 = term110.
Proof. exact (@lem6911674 (NUMERAL 0) term98). Qed.
Lemma lem6911676 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6911677 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6911678 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6911677 h1) (fun h1 : term110 = True => @lem6911676)). Qed.
Lemma lem6911679 : term110 = True.
Proof. exact (EQ_MP (@lem6911678) (@lem6911676)). Qed.
Lemma lem6911680 : term109 = True.
Proof. exact (TRANS (@lem6911675) (@lem6911679)). Qed.
Lemma lem6911681 : True = term109.
Proof. exact (SYM (@lem6911680)). Qed.
Lemma lem6911682 : term109.
Proof. exact (EQ_MP (@lem6911681) (@lem0)). Qed.
Lemma lem6911683 : term113.
Proof. exact (@lem6911672 (@lem6911682)). Qed.
Lemma lem6911685 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6911686 : term109 = term110.
Proof. exact (@lem6911685 (NUMERAL 0) term98). Qed.
Lemma lem6911687 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6911688 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6911689 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6911688 h1) (fun h1 : term110 = True => @lem6911687)). Qed.
Lemma lem6911690 : term110 = True.
Proof. exact (EQ_MP (@lem6911689) (@lem6911687)). Qed.
Lemma lem6911691 : term109 = True.
Proof. exact (TRANS (@lem6911686) (@lem6911690)). Qed.
Lemma lem6911692 : True = term109.
Proof. exact (SYM (@lem6911691)). Qed.
Lemma lem6911693 : term109.
Proof. exact (EQ_MP (@lem6911692) (@lem0)). Qed.
Lemma lem6911694 : term114.
Proof. exact (@lem6911683 (@lem6911693)). Qed.
Lemma lem6911696 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6911697 : term117 = term118.
Proof. exact (@lem6911696 term98 term98). Qed.
Lemma lem6911698 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6911699 : term120 = term98.
Proof. exact (EQ_MP (@lem6911698) (@lem940073)). Qed.
Lemma lem6911700 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6911701 : term118 = term4.
Proof. exact (MK_COMB (@lem6911700) (@lem6911699)). Qed.
Lemma lem6911702 : term117 = term4.
Proof. exact (TRANS (@lem6911697) (@lem6911701)). Qed.
Lemma lem6911704 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6911705 : term123 = term124.
Proof. exact (@lem6911704 term98 term98). Qed.
Lemma lem6911706 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6911707 : term120 = term98.
Proof. exact (EQ_MP (@lem6911706) (@lem940073)). Qed.
Lemma lem6911708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6911709 : term118 = term4.
Proof. exact (MK_COMB (@lem6911708) (@lem6911707)). Qed.
Lemma lem6911710 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6911711 : term124 = term95.
Proof. exact (MK_COMB (@lem6911710) (@lem6911709)). Qed.
Lemma lem6911712 : term123 = term95.
Proof. exact (TRANS (@lem6911705) (@lem6911711)). Qed.
Lemma lem6911713 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6911714 : term125 = term102.
Proof. exact (MK_COMB (@lem6911713) (@lem6911712)). Qed.
Lemma lem6911715 : term126 = term104.
Proof. exact (MK_COMB (@lem6911714) (@lem6911702)). Qed.
Lemma lem6911717 (m : nat) : (term127 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6911718 : term104 = term107.
Proof. exact (@lem6911717 term98). Qed.
Lemma lem6911719 : term126 = term107.
Proof. exact (TRANS (@lem6911715) (@lem6911718)). Qed.
Lemma lem6911720 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6911721 : term128 = term129.
Proof. exact (MK_COMB (@lem6911720) (@lem6911719)). Qed.
Lemma lem6911722 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem6911723 : term130 = term131.
Proof. exact (MK_COMB (@lem6911721) (@lem6911722)). Qed.
Lemma lem6911725 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6911726 : term131 = term107.
Proof. exact (@lem6911725 term98). Qed.
Lemma lem6911727 : term130 = term107.
Proof. exact (TRANS (@lem6911723) (@lem6911726)). Qed.
Lemma lem6911729 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6911730 : term117 = term118.
Proof. exact (@lem6911729 term98 term98). Qed.
Lemma lem6911731 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6911732 : term120 = term98.
Proof. exact (EQ_MP (@lem6911731) (@lem940073)). Qed.
Lemma lem6911733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6911734 : term118 = term4.
Proof. exact (MK_COMB (@lem6911733) (@lem6911732)). Qed.
Lemma lem6911735 : term117 = term4.
Proof. exact (TRANS (@lem6911730) (@lem6911734)). Qed.
Lemma lem6911736 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem6911737 : term133 = term131.
Proof. exact (MK_COMB (@lem6911736) (@lem6911735)). Qed.
Lemma lem6911739 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6911740 : term131 = term107.
Proof. exact (@lem6911739 term98). Qed.
Lemma lem6911741 : term133 = term107.
Proof. exact (TRANS (@lem6911737) (@lem6911740)). Qed.
Lemma lem6911742 : term107 = term133.
Proof. exact (SYM (@lem6911741)). Qed.
Lemma lem6911743 : term130 = term133.
Proof. exact (TRANS (@lem6911727) (@lem6911742)). Qed.
Lemma lem6911744 : term105 = term134.
Proof. exact (@lem6911694 (@lem6911743)). Qed.
Lemma lem6911745 : term104 = term134.
Proof. exact (TRANS (@lem6911660) (@lem6911744)). Qed.
Lemma lem6911747 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6911748 : term134 = term107.
Proof. exact (@lem6911747 term107). Qed.
Lemma lem6911749 : term104 = term107.
Proof. exact (TRANS (@lem6911745) (@lem6911748)). Qed.
Lemma lem6911750 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6911751 : term136 = term129.
Proof. exact (MK_COMB (@lem6911750) (@lem6911749)). Qed.
Lemma lem6911752 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem6911753 (x : real) (y : real) : (term94 x y) = (term137 x y).
Proof. exact (MK_COMB (@lem6911751) (@lem6911752 x y)). Qed.
Lemma lem6911754 (x : real) (y : real) : (term93 x y) = (term137 x y).
Proof. exact (TRANS (@lem6911651 x y) (@lem6911753 x y)). Qed.
Lemma lem6911755 (x : real) (y : real) : (term137 x y) = term107.
Proof. exact (@lem1982719 (real_mul x y)). Qed.
Lemma lem6911757 (x : real) (y : real) : (term93 x y) = term107.
Proof. exact (TRANS (@lem6911754 x y) (@lem6911755 x y)). Qed.
Lemma lem6911758 (x : real) (y : real) : (term92 x y) = term107.
Proof. exact (TRANS (@lem6911647 x y) (@lem6911757 x y)). Qed.
Lemma lem6911759 (y : real) (x : real) : (term91 y x) = term107.
Proof. exact (TRANS (@lem6911646 x y) (@lem6911758 x y)). Qed.
Lemma lem6911760 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6911761 (y : real) (x : real) : (term138 y x) = term139.
Proof. exact (MK_COMB (@lem6911760) (@lem6911759 y x)). Qed.
Lemma lem6911762 : term139 = term140.
Proof. exact (@lem1982785 term107). Qed.
Lemma lem6911764 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6911765 : term107 = term134.
Proof. exact (@lem6911764 (NUMERAL 0)). Qed.
Lemma lem6911767 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6911768 : term95 = term101.
Proof. exact (@lem6911767 term98). Qed.
Lemma lem6911769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6911770 : term141 = term142.
Proof. exact (MK_COMB (@lem6911769) (@lem6911768)). Qed.
Lemma lem6911771 : term140 = term143.
Proof. exact (MK_COMB (@lem6911770) (@lem6911765)). Qed.
Lemma lem6911772 : term143 = term144.
Proof. exact (@lem1981613 term95 term107 term4 term4). Qed.
Lemma lem6911774 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6911775 : term117 = term118.
Proof. exact (@lem6911774 term98 term98). Qed.
Lemma lem6911776 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6911777 : term120 = term98.
Proof. exact (EQ_MP (@lem6911776) (@lem940073)). Qed.
Lemma lem6911778 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6911779 : term118 = term4.
Proof. exact (MK_COMB (@lem6911778) (@lem6911777)). Qed.
Lemma lem6911780 : term117 = term4.
Proof. exact (TRANS (@lem6911775) (@lem6911779)). Qed.
Lemma lem6911782 (x : nat) : (term145 x) = term107.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6911783 : term140 = term107.
Proof. exact (@lem6911782 term98). Qed.
Lemma lem6911784 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6911785 : term146 = term147.
Proof. exact (MK_COMB (@lem6911784) (@lem6911783)). Qed.
Lemma lem6911786 : term144 = term134.
Proof. exact (MK_COMB (@lem6911785) (@lem6911780)). Qed.
Lemma lem6911787 : term143 = term134.
Proof. exact (TRANS (@lem6911772) (@lem6911786)). Qed.
Lemma lem6911788 : term140 = term134.
Proof. exact (TRANS (@lem6911771) (@lem6911787)). Qed.
Lemma lem6911790 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6911791 : term134 = term107.
Proof. exact (@lem6911790 term107). Qed.
Lemma lem6911792 : term140 = term107.
Proof. exact (TRANS (@lem6911788) (@lem6911791)). Qed.
Lemma lem6911793 : term139 = term107.
Proof. exact (TRANS (@lem6911762) (@lem6911792)). Qed.
Lemma lem6911794 (y : real) (x : real) : (term148 y x) = (term148 y x).
Proof. exact (eq_refl (term148 y x)). Qed.
Lemma lem6911795 (y : real) (x : real) : ((term138 y x) = term139) = ((term138 y x) = term107).
Proof. exact (MK_COMB (@lem6911794 y x) (@lem6911793)). Qed.
Lemma lem6911796 (y : real) (x : real) : (term138 y x) = term107.
Proof. exact (EQ_MP (@lem6911795 y x) (@lem6911761 y x)). Qed.
Lemma lem6911797 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem6911798 (y : real) (x : real) : (term149 y x) = term150.
Proof. exact (MK_COMB (@lem6911797) (@lem6911796 y x)). Qed.
Lemma lem6911799 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6911800 (y : real) (x : real) : (term151 y x) = term152.
Proof. exact (MK_COMB (@lem6911798 y x) (@lem6911799)). Qed.
Lemma lem6911801 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem6911802 (y : real) (x : real) : (term153 y x) = term150.
Proof. exact (MK_COMB (@lem6911801) (@lem6911759 y x)). Qed.
Lemma lem6911803 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6911804 (y : real) (x : real) : (term154 y x) = term152.
Proof. exact (MK_COMB (@lem6911802 y x) (@lem6911803)). Qed.
Lemma lem6911805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6911806 (y : real) (x : real) : (term155 y x) = term156.
Proof. exact (MK_COMB (@lem6911805) (@lem6911804 y x)). Qed.
Lemma lem6911807 (y : real) (x : real) : (term89 y x) = term157.
Proof. exact (MK_COMB (@lem6911806 y x) (@lem6911800 y x)). Qed.
Lemma lem6911808 (y : real) (x : real) : (term27 y x) = term157.
Proof. exact (TRANS (@lem6911629 y x) (@lem6911807 y x)). Qed.
Lemma lem6911809 (x : real) : (term29 x) = term158.
Proof. exact (fun_ext (fun y : real => @lem6911808 y x)). Qed.
Lemma lem6911810 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911811 (x : real) : (term30 x) = term159.
Proof. exact (MK_COMB (@lem6911810) (@lem6911809 x)). Qed.
Lemma lem6911812 : term38 = term160.
Proof. exact (fun_ext (fun x : real => @lem6911811 x)). Qed.
Lemma lem6911813 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6911814 : term39 = term161.
Proof. exact (MK_COMB (@lem6911813) (@lem6911812)). Qed.
Lemma lem6911815 (x : real) (y : real) (z : real) : (term47 x y z) = (term162 x y z).
Proof. exact (@lem1988318 (term44 x y z) (term45 x y z)). Qed.
Lemma lem6911832 (x : real) (y : real) (z : real) : (term45 x y z) = (term44 x y z).
Proof. exact (@lem1982745 x y z). Qed.
Lemma lem6911847 (x : real) (y : real) (z : real) : (term163 x y z) = (term163 x y z).
Proof. exact (eq_refl (term163 x y z)). Qed.
Lemma lem6911848 (x : real) (y : real) (z : real) : (term164 x y z) = (term165 x y z).
Proof. exact (MK_COMB (@lem6911847 x y z) (@lem6911832 x y z)). Qed.
Lemma lem6911849 (x : real) (y : real) (z : real) : (term165 x y z) = (term166 x y z).
Proof. exact (@lem1982792 (term44 x y z) (term44 x y z)). Qed.
Lemma lem6911853 (x : real) (y : real) (z : real) : (term166 x y z) = (term167 x y z).
Proof. exact (@lem1982715 term95 (term44 x y z)). Qed.
Lemma lem6911855 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6911856 : term4 = term97.
Proof. exact (@lem6911855 term98). Qed.
Lemma lem6911858 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6911859 : term95 = term101.
Proof. exact (@lem6911858 term98). Qed.
Lemma lem6911860 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6911861 : term102 = term103.
Proof. exact (MK_COMB (@lem6911860) (@lem6911859)). Qed.
Lemma lem6911862 : term104 = term105.
Proof. exact (MK_COMB (@lem6911861) (@lem6911856)). Qed.
Lemma lem6911863 : term106.
Proof. exact (@lem1981473 term95 term4 term4 term4 term107 term4). Qed.
Lemma lem6911865 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6911866 : term109 = term110.
Proof. exact (@lem6911865 (NUMERAL 0) term98). Qed.
Lemma lem6911867 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6911868 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6911869 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6911868 h1) (fun h1 : term110 = True => @lem6911867)). Qed.
Lemma lem6911870 : term110 = True.
Proof. exact (EQ_MP (@lem6911869) (@lem6911867)). Qed.
Lemma lem6911871 : term109 = True.
Proof. exact (TRANS (@lem6911866) (@lem6911870)). Qed.
Lemma lem6911872 : True = term109.
Proof. exact (SYM (@lem6911871)). Qed.
Lemma lem6911873 : term109.
Proof. exact (EQ_MP (@lem6911872) (@lem0)). Qed.
Lemma lem6911874 : term112.
Proof. exact (@lem6911863 (@lem6911873)). Qed.
Lemma lem6911876 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6911877 : term109 = term110.
Proof. exact (@lem6911876 (NUMERAL 0) term98). Qed.
Lemma lem6911878 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6911879 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6911880 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6911879 h1) (fun h1 : term110 = True => @lem6911878)). Qed.
Lemma lem6911881 : term110 = True.
Proof. exact (EQ_MP (@lem6911880) (@lem6911878)). Qed.
Lemma lem6911882 : term109 = True.
Proof. exact (TRANS (@lem6911877) (@lem6911881)). Qed.
Lemma lem6911883 : True = term109.
Proof. exact (SYM (@lem6911882)). Qed.
Lemma lem6911884 : term109.
Proof. exact (EQ_MP (@lem6911883) (@lem0)). Qed.
Lemma lem6911885 : term113.
Proof. exact (@lem6911874 (@lem6911884)). Qed.
Lemma lem6911887 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6911888 : term109 = term110.
Proof. exact (@lem6911887 (NUMERAL 0) term98). Qed.
Lemma lem6911889 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6911890 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6911891 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6911890 h1) (fun h1 : term110 = True => @lem6911889)). Qed.
Lemma lem6911892 : term110 = True.
Proof. exact (EQ_MP (@lem6911891) (@lem6911889)). Qed.
Lemma lem6911893 : term109 = True.
Proof. exact (TRANS (@lem6911888) (@lem6911892)). Qed.
Lemma lem6911894 : True = term109.
Proof. exact (SYM (@lem6911893)). Qed.
Lemma lem6911895 : term109.
Proof. exact (EQ_MP (@lem6911894) (@lem0)). Qed.
Lemma lem6911896 : term114.
Proof. exact (@lem6911885 (@lem6911895)). Qed.
Lemma lem6911898 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6911899 : term117 = term118.
Proof. exact (@lem6911898 term98 term98). Qed.
Lemma lem6911900 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6911901 : term120 = term98.
Proof. exact (EQ_MP (@lem6911900) (@lem940073)). Qed.
Lemma lem6911902 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6911903 : term118 = term4.
Proof. exact (MK_COMB (@lem6911902) (@lem6911901)). Qed.
Lemma lem6911904 : term117 = term4.
Proof. exact (TRANS (@lem6911899) (@lem6911903)). Qed.
Lemma lem6911906 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6911907 : term123 = term124.
Proof. exact (@lem6911906 term98 term98). Qed.
Lemma lem6911908 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6911909 : term120 = term98.
Proof. exact (EQ_MP (@lem6911908) (@lem940073)). Qed.
Lemma lem6911910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6911911 : term118 = term4.
Proof. exact (MK_COMB (@lem6911910) (@lem6911909)). Qed.
Lemma lem6911912 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6911913 : term124 = term95.
Proof. exact (MK_COMB (@lem6911912) (@lem6911911)). Qed.
Lemma lem6911914 : term123 = term95.
Proof. exact (TRANS (@lem6911907) (@lem6911913)). Qed.
Lemma lem6911915 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6911916 : term125 = term102.
Proof. exact (MK_COMB (@lem6911915) (@lem6911914)). Qed.
Lemma lem6911917 : term126 = term104.
Proof. exact (MK_COMB (@lem6911916) (@lem6911904)). Qed.
Lemma lem6911919 (m : nat) : (term127 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6911920 : term104 = term107.
Proof. exact (@lem6911919 term98). Qed.
Lemma lem6911921 : term126 = term107.
Proof. exact (TRANS (@lem6911917) (@lem6911920)). Qed.
Lemma lem6911922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6911923 : term128 = term129.
Proof. exact (MK_COMB (@lem6911922) (@lem6911921)). Qed.
Lemma lem6911924 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem6911925 : term130 = term131.
Proof. exact (MK_COMB (@lem6911923) (@lem6911924)). Qed.
Lemma lem6911927 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6911928 : term131 = term107.
Proof. exact (@lem6911927 term98). Qed.
Lemma lem6911929 : term130 = term107.
Proof. exact (TRANS (@lem6911925) (@lem6911928)). Qed.
Lemma lem6911931 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6911932 : term117 = term118.
Proof. exact (@lem6911931 term98 term98). Qed.
Lemma lem6911933 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6911934 : term120 = term98.
Proof. exact (EQ_MP (@lem6911933) (@lem940073)). Qed.
Lemma lem6911935 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6911936 : term118 = term4.
Proof. exact (MK_COMB (@lem6911935) (@lem6911934)). Qed.
Lemma lem6911937 : term117 = term4.
Proof. exact (TRANS (@lem6911932) (@lem6911936)). Qed.
Lemma lem6911938 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem6911939 : term133 = term131.
Proof. exact (MK_COMB (@lem6911938) (@lem6911937)). Qed.
Lemma lem6911941 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6911942 : term131 = term107.
Proof. exact (@lem6911941 term98). Qed.
Lemma lem6911943 : term133 = term107.
Proof. exact (TRANS (@lem6911939) (@lem6911942)). Qed.
Lemma lem6911944 : term107 = term133.
Proof. exact (SYM (@lem6911943)). Qed.
Lemma lem6911945 : term130 = term133.
Proof. exact (TRANS (@lem6911929) (@lem6911944)). Qed.
Lemma lem6911946 : term105 = term134.
Proof. exact (@lem6911896 (@lem6911945)). Qed.
Lemma lem6911947 : term104 = term134.
Proof. exact (TRANS (@lem6911862) (@lem6911946)). Qed.
Lemma lem6911949 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6911950 : term134 = term107.
Proof. exact (@lem6911949 term107). Qed.
Lemma lem6911951 : term104 = term107.
Proof. exact (TRANS (@lem6911947) (@lem6911950)). Qed.
Lemma lem6911952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6911953 : term136 = term129.
Proof. exact (MK_COMB (@lem6911952) (@lem6911951)). Qed.
Lemma lem6911954 (x : real) (y : real) (z : real) : (term44 x y z) = (term44 x y z).
Proof. exact (eq_refl (term44 x y z)). Qed.
Lemma lem6911955 (x : real) (y : real) (z : real) : (term167 x y z) = (term168 x y z).
Proof. exact (MK_COMB (@lem6911953) (@lem6911954 x y z)). Qed.
Lemma lem6911956 (x : real) (y : real) (z : real) : (term166 x y z) = (term168 x y z).
Proof. exact (TRANS (@lem6911853 x y z) (@lem6911955 x y z)). Qed.
Lemma lem6911957 (x : real) (y : real) (z : real) : (term168 x y z) = term107.
Proof. exact (@lem1982719 (term44 x y z)). Qed.
Lemma lem6911959 (x : real) (y : real) (z : real) : (term166 x y z) = term107.
Proof. exact (TRANS (@lem6911956 x y z) (@lem6911957 x y z)). Qed.
Lemma lem6911960 (x : real) (y : real) (z : real) : (term165 x y z) = term107.
Proof. exact (TRANS (@lem6911849 x y z) (@lem6911959 x y z)). Qed.
Lemma lem6911961 (x : real) (y : real) (z : real) : (term164 x y z) = term107.
Proof. exact (TRANS (@lem6911848 x y z) (@lem6911960 x y z)). Qed.
Lemma lem6911962 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6911963 (x : real) (y : real) (z : real) : (term169 x y z) = term139.
Proof. exact (MK_COMB (@lem6911962) (@lem6911961 x y z)). Qed.
Lemma lem6911964 : term139 = term140.
Proof. exact (@lem1982785 term107). Qed.
Lemma lem6911966 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6911967 : term107 = term134.
Proof. exact (@lem6911966 (NUMERAL 0)). Qed.
Lemma lem6911969 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6911970 : term95 = term101.
Proof. exact (@lem6911969 term98). Qed.
Lemma lem6911971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6911972 : term141 = term142.
Proof. exact (MK_COMB (@lem6911971) (@lem6911970)). Qed.
Lemma lem6911973 : term140 = term143.
Proof. exact (MK_COMB (@lem6911972) (@lem6911967)). Qed.
Lemma lem6911974 : term143 = term144.
Proof. exact (@lem1981613 term95 term107 term4 term4). Qed.
Lemma lem6911976 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6911977 : term117 = term118.
Proof. exact (@lem6911976 term98 term98). Qed.
Lemma lem6911978 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6911979 : term120 = term98.
Proof. exact (EQ_MP (@lem6911978) (@lem940073)). Qed.
Lemma lem6911980 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6911981 : term118 = term4.
Proof. exact (MK_COMB (@lem6911980) (@lem6911979)). Qed.
Lemma lem6911982 : term117 = term4.
Proof. exact (TRANS (@lem6911977) (@lem6911981)). Qed.
Lemma lem6911984 (x : nat) : (term145 x) = term107.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6911985 : term140 = term107.
Proof. exact (@lem6911984 term98). Qed.
Lemma lem6911986 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6911987 : term146 = term147.
Proof. exact (MK_COMB (@lem6911986) (@lem6911985)). Qed.
Lemma lem6911988 : term144 = term134.
Proof. exact (MK_COMB (@lem6911987) (@lem6911982)). Qed.
Lemma lem6911989 : term143 = term134.
Proof. exact (TRANS (@lem6911974) (@lem6911988)). Qed.
Lemma lem6911990 : term140 = term134.
Proof. exact (TRANS (@lem6911973) (@lem6911989)). Qed.
Lemma lem6911992 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6911993 : term134 = term107.
Proof. exact (@lem6911992 term107). Qed.
Lemma lem6911994 : term140 = term107.
Proof. exact (TRANS (@lem6911990) (@lem6911993)). Qed.
Lemma lem6911995 : term139 = term107.
Proof. exact (TRANS (@lem6911964) (@lem6911994)). Qed.
Lemma lem6911996 (x : real) (y : real) (z : real) : (term170 x y z) = (term170 x y z).
Proof. exact (eq_refl (term170 x y z)). Qed.
Lemma lem6911997 (x : real) (y : real) (z : real) : ((term169 x y z) = term139) = ((term169 x y z) = term107).
Proof. exact (MK_COMB (@lem6911996 x y z) (@lem6911995)). Qed.
Lemma lem6911998 (x : real) (y : real) (z : real) : (term169 x y z) = term107.
Proof. exact (EQ_MP (@lem6911997 x y z) (@lem6911963 x y z)). Qed.
Lemma lem6911999 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem6912000 (x : real) (y : real) (z : real) : (term171 x y z) = term150.
Proof. exact (MK_COMB (@lem6911999) (@lem6911998 x y z)). Qed.
Lemma lem6912001 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6912002 (x : real) (y : real) (z : real) : (term172 x y z) = term152.
Proof. exact (MK_COMB (@lem6912000 x y z) (@lem6912001)). Qed.
Lemma lem6912003 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem6912004 (x : real) (y : real) (z : real) : (term173 x y z) = term150.
Proof. exact (MK_COMB (@lem6912003) (@lem6911961 x y z)). Qed.
Lemma lem6912005 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6912006 (x : real) (y : real) (z : real) : (term174 x y z) = term152.
Proof. exact (MK_COMB (@lem6912004 x y z) (@lem6912005)). Qed.
Lemma lem6912007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912008 (x : real) (y : real) (z : real) : (term175 x y z) = term156.
Proof. exact (MK_COMB (@lem6912007) (@lem6912006 x y z)). Qed.
Lemma lem6912009 (x : real) (y : real) (z : real) : (term162 x y z) = term157.
Proof. exact (MK_COMB (@lem6912008 x y z) (@lem6912002 x y z)). Qed.
Lemma lem6912010 (x : real) (y : real) (z : real) : (term47 x y z) = term157.
Proof. exact (TRANS (@lem6911815 x y z) (@lem6912009 x y z)). Qed.
Lemma lem6912011 (x : real) (y : real) : (term49 x y) = term158.
Proof. exact (fun_ext (fun z : real => @lem6912010 x y z)). Qed.
Lemma lem6912012 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912013 (x : real) (y : real) : (term50 x y) = term159.
Proof. exact (MK_COMB (@lem6912012) (@lem6912011 x y)). Qed.
Lemma lem6912014 (x : real) : (term58 x) = term160.
Proof. exact (fun_ext (fun y : real => @lem6912013 x y)). Qed.
Lemma lem6912015 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912016 (x : real) : (term59 x) = term161.
Proof. exact (MK_COMB (@lem6912015) (@lem6912014 x)). Qed.
Lemma lem6912017 : term67 = term176.
Proof. exact (fun_ext (fun x : real => @lem6912016 x)). Qed.
Lemma lem6912018 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912019 : term68 = term177.
Proof. exact (MK_COMB (@lem6912018) (@lem6912017)). Qed.
Lemma lem6912020 (x : real) : (term73 x) = (term178 x).
Proof. exact (@lem1988318 (term8 x) x). Qed.
Lemma lem6912021 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6912028 (x : real) : (term8 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem6912029 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem6912030 (x : real) : (term179 x) = (real_sub x).
Proof. exact (MK_COMB (@lem6912029) (@lem6912028 x)). Qed.
Lemma lem6912031 (x : real) : (term180 x) = (real_sub x x).
Proof. exact (MK_COMB (@lem6912030 x) (@lem6912021 x)). Qed.
Lemma lem6912032 (x : real) : (real_sub x x) = (term181 x).
Proof. exact (@lem1982792 x x). Qed.
Lemma lem6912036 (x : real) : (term181 x) = (term182 x).
Proof. exact (@lem1982715 term95 x). Qed.
Lemma lem6912038 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912039 : term4 = term97.
Proof. exact (@lem6912038 term98). Qed.
Lemma lem6912041 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6912042 : term95 = term101.
Proof. exact (@lem6912041 term98). Qed.
Lemma lem6912043 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6912044 : term102 = term103.
Proof. exact (MK_COMB (@lem6912043) (@lem6912042)). Qed.
Lemma lem6912045 : term104 = term105.
Proof. exact (MK_COMB (@lem6912044) (@lem6912039)). Qed.
Lemma lem6912046 : term106.
Proof. exact (@lem1981473 term95 term4 term4 term4 term107 term4). Qed.
Lemma lem6912048 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912049 : term109 = term110.
Proof. exact (@lem6912048 (NUMERAL 0) term98). Qed.
Lemma lem6912050 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912051 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912052 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912051 h1) (fun h1 : term110 = True => @lem6912050)). Qed.
Lemma lem6912053 : term110 = True.
Proof. exact (EQ_MP (@lem6912052) (@lem6912050)). Qed.
Lemma lem6912054 : term109 = True.
Proof. exact (TRANS (@lem6912049) (@lem6912053)). Qed.
Lemma lem6912055 : True = term109.
Proof. exact (SYM (@lem6912054)). Qed.
Lemma lem6912056 : term109.
Proof. exact (EQ_MP (@lem6912055) (@lem0)). Qed.
Lemma lem6912057 : term112.
Proof. exact (@lem6912046 (@lem6912056)). Qed.
Lemma lem6912059 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912060 : term109 = term110.
Proof. exact (@lem6912059 (NUMERAL 0) term98). Qed.
Lemma lem6912061 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912062 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912063 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912062 h1) (fun h1 : term110 = True => @lem6912061)). Qed.
Lemma lem6912064 : term110 = True.
Proof. exact (EQ_MP (@lem6912063) (@lem6912061)). Qed.
Lemma lem6912065 : term109 = True.
Proof. exact (TRANS (@lem6912060) (@lem6912064)). Qed.
Lemma lem6912066 : True = term109.
Proof. exact (SYM (@lem6912065)). Qed.
Lemma lem6912067 : term109.
Proof. exact (EQ_MP (@lem6912066) (@lem0)). Qed.
Lemma lem6912068 : term113.
Proof. exact (@lem6912057 (@lem6912067)). Qed.
Lemma lem6912070 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912071 : term109 = term110.
Proof. exact (@lem6912070 (NUMERAL 0) term98). Qed.
Lemma lem6912072 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912073 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912074 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912073 h1) (fun h1 : term110 = True => @lem6912072)). Qed.
Lemma lem6912075 : term110 = True.
Proof. exact (EQ_MP (@lem6912074) (@lem6912072)). Qed.
Lemma lem6912076 : term109 = True.
Proof. exact (TRANS (@lem6912071) (@lem6912075)). Qed.
Lemma lem6912077 : True = term109.
Proof. exact (SYM (@lem6912076)). Qed.
Lemma lem6912078 : term109.
Proof. exact (EQ_MP (@lem6912077) (@lem0)). Qed.
Lemma lem6912079 : term114.
Proof. exact (@lem6912068 (@lem6912078)). Qed.
Lemma lem6912081 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6912082 : term117 = term118.
Proof. exact (@lem6912081 term98 term98). Qed.
Lemma lem6912083 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6912084 : term120 = term98.
Proof. exact (EQ_MP (@lem6912083) (@lem940073)). Qed.
Lemma lem6912085 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6912086 : term118 = term4.
Proof. exact (MK_COMB (@lem6912085) (@lem6912084)). Qed.
Lemma lem6912087 : term117 = term4.
Proof. exact (TRANS (@lem6912082) (@lem6912086)). Qed.
Lemma lem6912089 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6912090 : term123 = term124.
Proof. exact (@lem6912089 term98 term98). Qed.
Lemma lem6912091 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6912092 : term120 = term98.
Proof. exact (EQ_MP (@lem6912091) (@lem940073)). Qed.
Lemma lem6912093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6912094 : term118 = term4.
Proof. exact (MK_COMB (@lem6912093) (@lem6912092)). Qed.
Lemma lem6912095 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6912096 : term124 = term95.
Proof. exact (MK_COMB (@lem6912095) (@lem6912094)). Qed.
Lemma lem6912097 : term123 = term95.
Proof. exact (TRANS (@lem6912090) (@lem6912096)). Qed.
Lemma lem6912098 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6912099 : term125 = term102.
Proof. exact (MK_COMB (@lem6912098) (@lem6912097)). Qed.
Lemma lem6912100 : term126 = term104.
Proof. exact (MK_COMB (@lem6912099) (@lem6912087)). Qed.
Lemma lem6912102 (m : nat) : (term127 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6912103 : term104 = term107.
Proof. exact (@lem6912102 term98). Qed.
Lemma lem6912104 : term126 = term107.
Proof. exact (TRANS (@lem6912100) (@lem6912103)). Qed.
Lemma lem6912105 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6912106 : term128 = term129.
Proof. exact (MK_COMB (@lem6912105) (@lem6912104)). Qed.
Lemma lem6912107 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem6912108 : term130 = term131.
Proof. exact (MK_COMB (@lem6912106) (@lem6912107)). Qed.
Lemma lem6912110 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912111 : term131 = term107.
Proof. exact (@lem6912110 term98). Qed.
Lemma lem6912112 : term130 = term107.
Proof. exact (TRANS (@lem6912108) (@lem6912111)). Qed.
Lemma lem6912114 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6912115 : term117 = term118.
Proof. exact (@lem6912114 term98 term98). Qed.
Lemma lem6912116 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6912117 : term120 = term98.
Proof. exact (EQ_MP (@lem6912116) (@lem940073)). Qed.
Lemma lem6912118 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6912119 : term118 = term4.
Proof. exact (MK_COMB (@lem6912118) (@lem6912117)). Qed.
Lemma lem6912120 : term117 = term4.
Proof. exact (TRANS (@lem6912115) (@lem6912119)). Qed.
Lemma lem6912121 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem6912122 : term133 = term131.
Proof. exact (MK_COMB (@lem6912121) (@lem6912120)). Qed.
Lemma lem6912124 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912125 : term131 = term107.
Proof. exact (@lem6912124 term98). Qed.
Lemma lem6912126 : term133 = term107.
Proof. exact (TRANS (@lem6912122) (@lem6912125)). Qed.
Lemma lem6912127 : term107 = term133.
Proof. exact (SYM (@lem6912126)). Qed.
Lemma lem6912128 : term130 = term133.
Proof. exact (TRANS (@lem6912112) (@lem6912127)). Qed.
Lemma lem6912129 : term105 = term134.
Proof. exact (@lem6912079 (@lem6912128)). Qed.
Lemma lem6912130 : term104 = term134.
Proof. exact (TRANS (@lem6912045) (@lem6912129)). Qed.
Lemma lem6912132 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6912133 : term134 = term107.
Proof. exact (@lem6912132 term107). Qed.
Lemma lem6912134 : term104 = term107.
Proof. exact (TRANS (@lem6912130) (@lem6912133)). Qed.
Lemma lem6912135 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6912136 : term136 = term129.
Proof. exact (MK_COMB (@lem6912135) (@lem6912134)). Qed.
Lemma lem6912137 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6912138 (x : real) : (term182 x) = (term183 x).
Proof. exact (MK_COMB (@lem6912136) (@lem6912137 x)). Qed.
Lemma lem6912139 (x : real) : (term181 x) = (term183 x).
Proof. exact (TRANS (@lem6912036 x) (@lem6912138 x)). Qed.
Lemma lem6912140 (x : real) : (term183 x) = term107.
Proof. exact (@lem1982719 x). Qed.
Lemma lem6912142 (x : real) : (term181 x) = term107.
Proof. exact (TRANS (@lem6912139 x) (@lem6912140 x)). Qed.
Lemma lem6912143 (x : real) : (real_sub x x) = term107.
Proof. exact (TRANS (@lem6912032 x) (@lem6912142 x)). Qed.
Lemma lem6912144 (x : real) : (term180 x) = term107.
Proof. exact (TRANS (@lem6912031 x) (@lem6912143 x)). Qed.
Lemma lem6912145 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6912146 (x : real) : (term184 x) = term139.
Proof. exact (MK_COMB (@lem6912145) (@lem6912144 x)). Qed.
Lemma lem6912147 : term139 = term140.
Proof. exact (@lem1982785 term107). Qed.
Lemma lem6912149 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912150 : term107 = term134.
Proof. exact (@lem6912149 (NUMERAL 0)). Qed.
Lemma lem6912152 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6912153 : term95 = term101.
Proof. exact (@lem6912152 term98). Qed.
Lemma lem6912154 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6912155 : term141 = term142.
Proof. exact (MK_COMB (@lem6912154) (@lem6912153)). Qed.
Lemma lem6912156 : term140 = term143.
Proof. exact (MK_COMB (@lem6912155) (@lem6912150)). Qed.
Lemma lem6912157 : term143 = term144.
Proof. exact (@lem1981613 term95 term107 term4 term4). Qed.
Lemma lem6912159 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6912160 : term117 = term118.
Proof. exact (@lem6912159 term98 term98). Qed.
Lemma lem6912161 : (term119 = (BIT1 0)) = (term120 = term98).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6912162 : term120 = term98.
Proof. exact (EQ_MP (@lem6912161) (@lem940073)). Qed.
Lemma lem6912163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6912164 : term118 = term4.
Proof. exact (MK_COMB (@lem6912163) (@lem6912162)). Qed.
Lemma lem6912165 : term117 = term4.
Proof. exact (TRANS (@lem6912160) (@lem6912164)). Qed.
Lemma lem6912167 (x : nat) : (term145 x) = term107.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6912168 : term140 = term107.
Proof. exact (@lem6912167 term98). Qed.
Lemma lem6912169 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6912170 : term146 = term147.
Proof. exact (MK_COMB (@lem6912169) (@lem6912168)). Qed.
Lemma lem6912171 : term144 = term134.
Proof. exact (MK_COMB (@lem6912170) (@lem6912165)). Qed.
Lemma lem6912172 : term143 = term134.
Proof. exact (TRANS (@lem6912157) (@lem6912171)). Qed.
Lemma lem6912173 : term140 = term134.
Proof. exact (TRANS (@lem6912156) (@lem6912172)). Qed.
Lemma lem6912175 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6912176 : term134 = term107.
Proof. exact (@lem6912175 term107). Qed.
Lemma lem6912177 : term140 = term107.
Proof. exact (TRANS (@lem6912173) (@lem6912176)). Qed.
Lemma lem6912178 : term139 = term107.
Proof. exact (TRANS (@lem6912147) (@lem6912177)). Qed.
Lemma lem6912179 (x : real) : (term185 x) = (term185 x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem6912180 (x : real) : ((term184 x) = term139) = ((term184 x) = term107).
Proof. exact (MK_COMB (@lem6912179 x) (@lem6912178)). Qed.
Lemma lem6912181 (x : real) : (term184 x) = term107.
Proof. exact (EQ_MP (@lem6912180 x) (@lem6912146 x)). Qed.
Lemma lem6912182 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem6912183 (x : real) : (term186 x) = term150.
Proof. exact (MK_COMB (@lem6912182) (@lem6912181 x)). Qed.
Lemma lem6912184 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6912185 (x : real) : (term187 x) = term152.
Proof. exact (MK_COMB (@lem6912183 x) (@lem6912184)). Qed.
Lemma lem6912186 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem6912187 (x : real) : (term188 x) = term150.
Proof. exact (MK_COMB (@lem6912186) (@lem6912144 x)). Qed.
Lemma lem6912188 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6912189 (x : real) : (term189 x) = term152.
Proof. exact (MK_COMB (@lem6912187 x) (@lem6912188)). Qed.
Lemma lem6912190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912191 (x : real) : (term190 x) = term156.
Proof. exact (MK_COMB (@lem6912190) (@lem6912189 x)). Qed.
Lemma lem6912192 (x : real) : (term178 x) = term157.
Proof. exact (MK_COMB (@lem6912191 x) (@lem6912185 x)). Qed.
Lemma lem6912193 (x : real) : (term73 x) = term157.
Proof. exact (TRANS (@lem6912020 x) (@lem6912192 x)). Qed.
Lemma lem6912194 : term75 = term158.
Proof. exact (fun_ext (fun x : real => @lem6912193 x)). Qed.
Lemma lem6912195 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912196 : term76 = term159.
Proof. exact (MK_COMB (@lem6912195) (@lem6912194)). Qed.
Lemma lem6912197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912198 : term78 = term191.
Proof. exact (MK_COMB (@lem6912197) (@lem6912019)). Qed.
Lemma lem6912199 : term80 = term192.
Proof. exact (MK_COMB (@lem6912198) (@lem6912196)). Qed.
Lemma lem6912200 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912201 : term84 = term193.
Proof. exact (MK_COMB (@lem6912200) (@lem6911814)). Qed.
Lemma lem6912202 : term86 = term194.
Proof. exact (MK_COMB (@lem6912201) (@lem6912199)). Qed.
Lemma lem6912203 : term87 = term194.
Proof. exact (TRANS (@lem6911628) (@lem6912202)). Qed.
Lemma lem6912205 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912206 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912205 real t). Qed.
Lemma lem6912207 : term161 = term159.
Proof. exact (@lem6912206 term159). Qed.
Lemma lem6912209 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6912210 (P : real -> Prop) (Q : real -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6912209 real P Q). Qed.
Lemma lem6912211 : term201 = term202.
Proof. exact (@lem6912210 term203 term203). Qed.
Lemma lem6912212 (y : real) : (term204 y) = term152.
Proof. exact (eq_refl (term204 y)). Qed.
Lemma lem6912213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912214 (y : real) : (term205 y) = term156.
Proof. exact (MK_COMB (@lem6912213) (@lem6912212 y)). Qed.
Lemma lem6912215 (y : real) : (term204 y) = term152.
Proof. exact (eq_refl (term204 y)). Qed.
Lemma lem6912216 (y : real) : (term206 y) = term157.
Proof. exact (MK_COMB (@lem6912214 y) (@lem6912215 y)). Qed.
Lemma lem6912217 : term207 = term158.
Proof. exact (fun_ext (fun y : real => @lem6912216 y)). Qed.
Lemma lem6912218 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912219 : term201 = term159.
Proof. exact (MK_COMB (@lem6912218) (@lem6912217)). Qed.
Lemma lem6912220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6912221 : term208 = term209.
Proof. exact (MK_COMB (@lem6912220) (@lem6912219)). Qed.
Lemma lem6912222 (y : real) : (term204 y) = term152.
Proof. exact (eq_refl (term204 y)). Qed.
Lemma lem6912223 : term210 = term203.
Proof. exact (fun_ext (fun y : real => @lem6912222 y)). Qed.
Lemma lem6912224 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912225 : term211 = term212.
Proof. exact (MK_COMB (@lem6912224) (@lem6912223)). Qed.
Lemma lem6912226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912227 : term213 = term214.
Proof. exact (MK_COMB (@lem6912226) (@lem6912225)). Qed.
Lemma lem6912228 (y : real) : (term204 y) = term152.
Proof. exact (eq_refl (term204 y)). Qed.
Lemma lem6912229 : term210 = term203.
Proof. exact (fun_ext (fun y : real => @lem6912228 y)). Qed.
Lemma lem6912230 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912231 : term211 = term212.
Proof. exact (MK_COMB (@lem6912230) (@lem6912229)). Qed.
Lemma lem6912232 : term202 = term215.
Proof. exact (MK_COMB (@lem6912227) (@lem6912231)). Qed.
Lemma lem6912233 : (term201 = term202) = (term159 = term215).
Proof. exact (MK_COMB (@lem6912221) (@lem6912232)). Qed.
Lemma lem6912234 : term159 = term215.
Proof. exact (EQ_MP (@lem6912233) (@lem6912211)). Qed.
Lemma lem6912235 : term161 = term215.
Proof. exact (TRANS (@lem6912207) (@lem6912234)). Qed.
Lemma lem6912237 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912238 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912237 real t). Qed.
Lemma lem6912239 : term212 = term152.
Proof. exact (@lem6912238 term152). Qed.
Lemma lem6912240 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912241 : term214 = term156.
Proof. exact (MK_COMB (@lem6912240) (@lem6912239)). Qed.
Lemma lem6912243 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912244 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912243 real t). Qed.
Lemma lem6912245 : term212 = term152.
Proof. exact (@lem6912244 term152). Qed.
Lemma lem6912246 : term215 = term157.
Proof. exact (MK_COMB (@lem6912241) (@lem6912245)). Qed.
Lemma lem6912247 : term161 = term157.
Proof. exact (TRANS (@lem6912235) (@lem6912246)). Qed.
Lemma lem6912248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912249 : term193 = term216.
Proof. exact (MK_COMB (@lem6912248) (@lem6912247)). Qed.
Lemma lem6912251 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912252 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912251 real t). Qed.
Lemma lem6912253 : term177 = term161.
Proof. exact (@lem6912252 term161). Qed.
Lemma lem6912255 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912256 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912255 real t). Qed.
Lemma lem6912257 : term161 = term159.
Proof. exact (@lem6912256 term159). Qed.
Lemma lem6912259 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6912260 (P : real -> Prop) (Q : real -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6912259 real P Q). Qed.
Lemma lem6912261 : term201 = term202.
Proof. exact (@lem6912260 term203 term203). Qed.
Lemma lem6912262 (z : real) : (term204 z) = term152.
Proof. exact (eq_refl (term204 z)). Qed.
Lemma lem6912263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912264 (z : real) : (term205 z) = term156.
Proof. exact (MK_COMB (@lem6912263) (@lem6912262 z)). Qed.
Lemma lem6912265 (z : real) : (term204 z) = term152.
Proof. exact (eq_refl (term204 z)). Qed.
Lemma lem6912266 (z : real) : (term206 z) = term157.
Proof. exact (MK_COMB (@lem6912264 z) (@lem6912265 z)). Qed.
Lemma lem6912267 : term207 = term158.
Proof. exact (fun_ext (fun z : real => @lem6912266 z)). Qed.
Lemma lem6912268 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912269 : term201 = term159.
Proof. exact (MK_COMB (@lem6912268) (@lem6912267)). Qed.
Lemma lem6912270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6912271 : term208 = term209.
Proof. exact (MK_COMB (@lem6912270) (@lem6912269)). Qed.
Lemma lem6912272 (z : real) : (term204 z) = term152.
Proof. exact (eq_refl (term204 z)). Qed.
Lemma lem6912273 : term210 = term203.
Proof. exact (fun_ext (fun z : real => @lem6912272 z)). Qed.
Lemma lem6912274 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912275 : term211 = term212.
Proof. exact (MK_COMB (@lem6912274) (@lem6912273)). Qed.
Lemma lem6912276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912277 : term213 = term214.
Proof. exact (MK_COMB (@lem6912276) (@lem6912275)). Qed.
Lemma lem6912278 (z : real) : (term204 z) = term152.
Proof. exact (eq_refl (term204 z)). Qed.
Lemma lem6912279 : term210 = term203.
Proof. exact (fun_ext (fun z : real => @lem6912278 z)). Qed.
Lemma lem6912280 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912281 : term211 = term212.
Proof. exact (MK_COMB (@lem6912280) (@lem6912279)). Qed.
Lemma lem6912282 : term202 = term215.
Proof. exact (MK_COMB (@lem6912277) (@lem6912281)). Qed.
Lemma lem6912283 : (term201 = term202) = (term159 = term215).
Proof. exact (MK_COMB (@lem6912271) (@lem6912282)). Qed.
Lemma lem6912284 : term159 = term215.
Proof. exact (EQ_MP (@lem6912283) (@lem6912261)). Qed.
Lemma lem6912285 : term161 = term215.
Proof. exact (TRANS (@lem6912257) (@lem6912284)). Qed.
Lemma lem6912286 : term177 = term215.
Proof. exact (TRANS (@lem6912253) (@lem6912285)). Qed.
Lemma lem6912288 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912289 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912288 real t). Qed.
Lemma lem6912290 : term212 = term152.
Proof. exact (@lem6912289 term152). Qed.
Lemma lem6912291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912292 : term214 = term156.
Proof. exact (MK_COMB (@lem6912291) (@lem6912290)). Qed.
Lemma lem6912294 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912295 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912294 real t). Qed.
Lemma lem6912296 : term212 = term152.
Proof. exact (@lem6912295 term152). Qed.
Lemma lem6912297 : term215 = term157.
Proof. exact (MK_COMB (@lem6912292) (@lem6912296)). Qed.
Lemma lem6912298 : term177 = term157.
Proof. exact (TRANS (@lem6912286) (@lem6912297)). Qed.
Lemma lem6912299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912300 : term191 = term216.
Proof. exact (MK_COMB (@lem6912299) (@lem6912298)). Qed.
Lemma lem6912302 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6912303 (P : real -> Prop) (Q : real -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6912302 real P Q). Qed.
Lemma lem6912304 : term201 = term202.
Proof. exact (@lem6912303 term203 term203). Qed.
Lemma lem6912305 (x : real) : (term204 x) = term152.
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem6912306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912307 (x : real) : (term205 x) = term156.
Proof. exact (MK_COMB (@lem6912306) (@lem6912305 x)). Qed.
Lemma lem6912308 (x : real) : (term204 x) = term152.
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem6912309 (x : real) : (term206 x) = term157.
Proof. exact (MK_COMB (@lem6912307 x) (@lem6912308 x)). Qed.
Lemma lem6912310 : term207 = term158.
Proof. exact (fun_ext (fun x : real => @lem6912309 x)). Qed.
Lemma lem6912311 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912312 : term201 = term159.
Proof. exact (MK_COMB (@lem6912311) (@lem6912310)). Qed.
Lemma lem6912313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6912314 : term208 = term209.
Proof. exact (MK_COMB (@lem6912313) (@lem6912312)). Qed.
Lemma lem6912315 (x : real) : (term204 x) = term152.
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem6912316 : term210 = term203.
Proof. exact (fun_ext (fun x : real => @lem6912315 x)). Qed.
Lemma lem6912317 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912318 : term211 = term212.
Proof. exact (MK_COMB (@lem6912317) (@lem6912316)). Qed.
Lemma lem6912319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912320 : term213 = term214.
Proof. exact (MK_COMB (@lem6912319) (@lem6912318)). Qed.
Lemma lem6912321 (x : real) : (term204 x) = term152.
Proof. exact (eq_refl (term204 x)). Qed.
Lemma lem6912322 : term210 = term203.
Proof. exact (fun_ext (fun x : real => @lem6912321 x)). Qed.
Lemma lem6912323 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6912324 : term211 = term212.
Proof. exact (MK_COMB (@lem6912323) (@lem6912322)). Qed.
Lemma lem6912325 : term202 = term215.
Proof. exact (MK_COMB (@lem6912320) (@lem6912324)). Qed.
Lemma lem6912326 : (term201 = term202) = (term159 = term215).
Proof. exact (MK_COMB (@lem6912314) (@lem6912325)). Qed.
Lemma lem6912327 : term159 = term215.
Proof. exact (EQ_MP (@lem6912326) (@lem6912304)). Qed.
Lemma lem6912329 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912330 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912329 real t). Qed.
Lemma lem6912331 : term212 = term152.
Proof. exact (@lem6912330 term152). Qed.
Lemma lem6912332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6912333 : term214 = term156.
Proof. exact (MK_COMB (@lem6912332) (@lem6912331)). Qed.
Lemma lem6912335 {A : Type'} (t : Prop) : (term195 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6912336 (t : Prop) : (term196 t) = t.
Proof. exact (@lem6912335 real t). Qed.
Lemma lem6912337 : term212 = term152.
Proof. exact (@lem6912336 term152). Qed.
Lemma lem6912338 : term215 = term157.
Proof. exact (MK_COMB (@lem6912333) (@lem6912337)). Qed.
Lemma lem6912339 : term159 = term157.
Proof. exact (TRANS (@lem6912327) (@lem6912338)). Qed.
Lemma lem6912340 : term192 = term217.
Proof. exact (MK_COMB (@lem6912300) (@lem6912339)). Qed.
Lemma lem6912343 : term194 = term218.
Proof. exact (MK_COMB (@lem6912249) (@lem6912340)). Qed.
Lemma lem6912368 : term87 = term218.
Proof. exact (TRANS (@lem6912203) (@lem6912343)). Qed.
Lemma lem6912402 (h1 : term218) : term218.
Proof. exact (h1). Qed.
Lemma lem6912403 (h1 : term157) : term157.
Proof. exact (h1). Qed.
Lemma lem6912404 (h1 : term152) : term152.
Proof. exact (h1). Qed.
Lemma lem6912406 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6912407 : term152 = term219.
Proof. exact (@lem6912406 term107 term107). Qed.
Lemma lem6912409 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912410 : term107 = term134.
Proof. exact (@lem6912409 (NUMERAL 0)). Qed.
Lemma lem6912412 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912413 : term107 = term134.
Proof. exact (@lem6912412 (NUMERAL 0)). Qed.
Lemma lem6912414 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912415 : term220 = term221.
Proof. exact (MK_COMB (@lem6912414) (@lem6912413)). Qed.
Lemma lem6912416 : term219 = term222.
Proof. exact (MK_COMB (@lem6912415) (@lem6912410)). Qed.
Lemma lem6912417 : term223.
Proof. exact (@lem1980255 term107 term4 term107 term4). Qed.
Lemma lem6912419 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912420 : term109 = term110.
Proof. exact (@lem6912419 (NUMERAL 0) term98). Qed.
Lemma lem6912421 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912422 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912423 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912422 h1) (fun h1 : term110 = True => @lem6912421)). Qed.
Lemma lem6912424 : term110 = True.
Proof. exact (EQ_MP (@lem6912423) (@lem6912421)). Qed.
Lemma lem6912425 : term109 = True.
Proof. exact (TRANS (@lem6912420) (@lem6912424)). Qed.
Lemma lem6912426 : True = term109.
Proof. exact (SYM (@lem6912425)). Qed.
Lemma lem6912427 : term109.
Proof. exact (EQ_MP (@lem6912426) (@lem0)). Qed.
Lemma lem6912428 : term224.
Proof. exact (@lem6912417 (@lem6912427)). Qed.
Lemma lem6912430 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912431 : term109 = term110.
Proof. exact (@lem6912430 (NUMERAL 0) term98). Qed.
Lemma lem6912432 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912433 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912434 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912433 h1) (fun h1 : term110 = True => @lem6912432)). Qed.
Lemma lem6912435 : term110 = True.
Proof. exact (EQ_MP (@lem6912434) (@lem6912432)). Qed.
Lemma lem6912436 : term109 = True.
Proof. exact (TRANS (@lem6912431) (@lem6912435)). Qed.
Lemma lem6912437 : True = term109.
Proof. exact (SYM (@lem6912436)). Qed.
Lemma lem6912438 : term109.
Proof. exact (EQ_MP (@lem6912437) (@lem0)). Qed.
Lemma lem6912439 : term222 = term225.
Proof. exact (@lem6912428 (@lem6912438)). Qed.
Lemma lem6912441 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912442 : term131 = term107.
Proof. exact (@lem6912441 term98). Qed.
Lemma lem6912444 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912445 : term131 = term107.
Proof. exact (@lem6912444 term98). Qed.
Lemma lem6912446 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912447 : term226 = term220.
Proof. exact (MK_COMB (@lem6912446) (@lem6912445)). Qed.
Lemma lem6912448 : term225 = term219.
Proof. exact (MK_COMB (@lem6912447) (@lem6912442)). Qed.
Lemma lem6912450 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912451 : term219 = term227.
Proof. exact (@lem6912450 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem6912452 : term227 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem6912453 : term219 = False.
Proof. exact (TRANS (@lem6912451) (@lem6912452)). Qed.
Lemma lem6912454 : term225 = False.
Proof. exact (TRANS (@lem6912448) (@lem6912453)). Qed.
Lemma lem6912455 : term222 = False.
Proof. exact (TRANS (@lem6912439) (@lem6912454)). Qed.
Lemma lem6912456 : term219 = False.
Proof. exact (TRANS (@lem6912416) (@lem6912455)). Qed.
Lemma lem6912457 : term152 = False.
Proof. exact (TRANS (@lem6912407) (@lem6912456)). Qed.
Lemma lem6912458 (h1 : term152) : False.
Proof. exact (EQ_MP (@lem6912457) (@lem6912404 h1)). Qed.
Lemma lem6912459 (h1 : term152) : term152.
Proof. exact (h1). Qed.
Lemma lem6912461 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6912462 : term152 = term219.
Proof. exact (@lem6912461 term107 term107). Qed.
Lemma lem6912464 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912465 : term107 = term134.
Proof. exact (@lem6912464 (NUMERAL 0)). Qed.
Lemma lem6912467 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912468 : term107 = term134.
Proof. exact (@lem6912467 (NUMERAL 0)). Qed.
Lemma lem6912469 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912470 : term220 = term221.
Proof. exact (MK_COMB (@lem6912469) (@lem6912468)). Qed.
Lemma lem6912471 : term219 = term222.
Proof. exact (MK_COMB (@lem6912470) (@lem6912465)). Qed.
Lemma lem6912472 : term223.
Proof. exact (@lem1980255 term107 term4 term107 term4). Qed.
Lemma lem6912474 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912475 : term109 = term110.
Proof. exact (@lem6912474 (NUMERAL 0) term98). Qed.
Lemma lem6912476 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912477 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912478 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912477 h1) (fun h1 : term110 = True => @lem6912476)). Qed.
Lemma lem6912479 : term110 = True.
Proof. exact (EQ_MP (@lem6912478) (@lem6912476)). Qed.
Lemma lem6912480 : term109 = True.
Proof. exact (TRANS (@lem6912475) (@lem6912479)). Qed.
Lemma lem6912481 : True = term109.
Proof. exact (SYM (@lem6912480)). Qed.
Lemma lem6912482 : term109.
Proof. exact (EQ_MP (@lem6912481) (@lem0)). Qed.
Lemma lem6912483 : term224.
Proof. exact (@lem6912472 (@lem6912482)). Qed.
Lemma lem6912485 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912486 : term109 = term110.
Proof. exact (@lem6912485 (NUMERAL 0) term98). Qed.
Lemma lem6912487 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912488 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912489 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912488 h1) (fun h1 : term110 = True => @lem6912487)). Qed.
Lemma lem6912490 : term110 = True.
Proof. exact (EQ_MP (@lem6912489) (@lem6912487)). Qed.
Lemma lem6912491 : term109 = True.
Proof. exact (TRANS (@lem6912486) (@lem6912490)). Qed.
Lemma lem6912492 : True = term109.
Proof. exact (SYM (@lem6912491)). Qed.
Lemma lem6912493 : term109.
Proof. exact (EQ_MP (@lem6912492) (@lem0)). Qed.
Lemma lem6912494 : term222 = term225.
Proof. exact (@lem6912483 (@lem6912493)). Qed.
Lemma lem6912496 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912497 : term131 = term107.
Proof. exact (@lem6912496 term98). Qed.
Lemma lem6912499 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912500 : term131 = term107.
Proof. exact (@lem6912499 term98). Qed.
Lemma lem6912501 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912502 : term226 = term220.
Proof. exact (MK_COMB (@lem6912501) (@lem6912500)). Qed.
Lemma lem6912503 : term225 = term219.
Proof. exact (MK_COMB (@lem6912502) (@lem6912497)). Qed.
Lemma lem6912505 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912506 : term219 = term227.
Proof. exact (@lem6912505 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem6912507 : term227 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem6912508 : term219 = False.
Proof. exact (TRANS (@lem6912506) (@lem6912507)). Qed.
Lemma lem6912509 : term225 = False.
Proof. exact (TRANS (@lem6912503) (@lem6912508)). Qed.
Lemma lem6912510 : term222 = False.
Proof. exact (TRANS (@lem6912494) (@lem6912509)). Qed.
Lemma lem6912511 : term219 = False.
Proof. exact (TRANS (@lem6912471) (@lem6912510)). Qed.
Lemma lem6912512 : term152 = False.
Proof. exact (TRANS (@lem6912462) (@lem6912511)). Qed.
Lemma lem6912513 (h1 : term152) : False.
Proof. exact (EQ_MP (@lem6912512) (@lem6912459 h1)). Qed.
Lemma lem6912514 (h1 : term157) : False.
Proof. exact (or_elim (@lem6912403 h1) (fun h0 : term152 => @lem6912458 h0) (fun h0 : term152 => @lem6912513 h0)). Qed.
Lemma lem6912515 (h1 : term217) : term217.
Proof. exact (h1). Qed.
Lemma lem6912516 (h1 : term157) : term157.
Proof. exact (h1). Qed.
Lemma lem6912517 (h1 : term152) : term152.
Proof. exact (h1). Qed.
Lemma lem6912519 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6912520 : term152 = term219.
Proof. exact (@lem6912519 term107 term107). Qed.
Lemma lem6912522 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912523 : term107 = term134.
Proof. exact (@lem6912522 (NUMERAL 0)). Qed.
Lemma lem6912525 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912526 : term107 = term134.
Proof. exact (@lem6912525 (NUMERAL 0)). Qed.
Lemma lem6912527 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912528 : term220 = term221.
Proof. exact (MK_COMB (@lem6912527) (@lem6912526)). Qed.
Lemma lem6912529 : term219 = term222.
Proof. exact (MK_COMB (@lem6912528) (@lem6912523)). Qed.
Lemma lem6912530 : term223.
Proof. exact (@lem1980255 term107 term4 term107 term4). Qed.
Lemma lem6912532 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912533 : term109 = term110.
Proof. exact (@lem6912532 (NUMERAL 0) term98). Qed.
Lemma lem6912534 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912535 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912536 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912535 h1) (fun h1 : term110 = True => @lem6912534)). Qed.
Lemma lem6912537 : term110 = True.
Proof. exact (EQ_MP (@lem6912536) (@lem6912534)). Qed.
Lemma lem6912538 : term109 = True.
Proof. exact (TRANS (@lem6912533) (@lem6912537)). Qed.
Lemma lem6912539 : True = term109.
Proof. exact (SYM (@lem6912538)). Qed.
Lemma lem6912540 : term109.
Proof. exact (EQ_MP (@lem6912539) (@lem0)). Qed.
Lemma lem6912541 : term224.
Proof. exact (@lem6912530 (@lem6912540)). Qed.
Lemma lem6912543 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912544 : term109 = term110.
Proof. exact (@lem6912543 (NUMERAL 0) term98). Qed.
Lemma lem6912545 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912546 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912547 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912546 h1) (fun h1 : term110 = True => @lem6912545)). Qed.
Lemma lem6912548 : term110 = True.
Proof. exact (EQ_MP (@lem6912547) (@lem6912545)). Qed.
Lemma lem6912549 : term109 = True.
Proof. exact (TRANS (@lem6912544) (@lem6912548)). Qed.
Lemma lem6912550 : True = term109.
Proof. exact (SYM (@lem6912549)). Qed.
Lemma lem6912551 : term109.
Proof. exact (EQ_MP (@lem6912550) (@lem0)). Qed.
Lemma lem6912552 : term222 = term225.
Proof. exact (@lem6912541 (@lem6912551)). Qed.
Lemma lem6912554 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912555 : term131 = term107.
Proof. exact (@lem6912554 term98). Qed.
Lemma lem6912557 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912558 : term131 = term107.
Proof. exact (@lem6912557 term98). Qed.
Lemma lem6912559 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912560 : term226 = term220.
Proof. exact (MK_COMB (@lem6912559) (@lem6912558)). Qed.
Lemma lem6912561 : term225 = term219.
Proof. exact (MK_COMB (@lem6912560) (@lem6912555)). Qed.
Lemma lem6912563 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912564 : term219 = term227.
Proof. exact (@lem6912563 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem6912565 : term227 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem6912566 : term219 = False.
Proof. exact (TRANS (@lem6912564) (@lem6912565)). Qed.
Lemma lem6912567 : term225 = False.
Proof. exact (TRANS (@lem6912561) (@lem6912566)). Qed.
Lemma lem6912568 : term222 = False.
Proof. exact (TRANS (@lem6912552) (@lem6912567)). Qed.
Lemma lem6912569 : term219 = False.
Proof. exact (TRANS (@lem6912529) (@lem6912568)). Qed.
Lemma lem6912570 : term152 = False.
Proof. exact (TRANS (@lem6912520) (@lem6912569)). Qed.
Lemma lem6912571 (h1 : term152) : False.
Proof. exact (EQ_MP (@lem6912570) (@lem6912517 h1)). Qed.
Lemma lem6912572 (h1 : term152) : term152.
Proof. exact (h1). Qed.
Lemma lem6912574 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6912575 : term152 = term219.
Proof. exact (@lem6912574 term107 term107). Qed.
Lemma lem6912577 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912578 : term107 = term134.
Proof. exact (@lem6912577 (NUMERAL 0)). Qed.
Lemma lem6912580 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912581 : term107 = term134.
Proof. exact (@lem6912580 (NUMERAL 0)). Qed.
Lemma lem6912582 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912583 : term220 = term221.
Proof. exact (MK_COMB (@lem6912582) (@lem6912581)). Qed.
Lemma lem6912584 : term219 = term222.
Proof. exact (MK_COMB (@lem6912583) (@lem6912578)). Qed.
Lemma lem6912585 : term223.
Proof. exact (@lem1980255 term107 term4 term107 term4). Qed.
Lemma lem6912587 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912588 : term109 = term110.
Proof. exact (@lem6912587 (NUMERAL 0) term98). Qed.
Lemma lem6912589 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912590 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912591 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912590 h1) (fun h1 : term110 = True => @lem6912589)). Qed.
Lemma lem6912592 : term110 = True.
Proof. exact (EQ_MP (@lem6912591) (@lem6912589)). Qed.
Lemma lem6912593 : term109 = True.
Proof. exact (TRANS (@lem6912588) (@lem6912592)). Qed.
Lemma lem6912594 : True = term109.
Proof. exact (SYM (@lem6912593)). Qed.
Lemma lem6912595 : term109.
Proof. exact (EQ_MP (@lem6912594) (@lem0)). Qed.
Lemma lem6912596 : term224.
Proof. exact (@lem6912585 (@lem6912595)). Qed.
Lemma lem6912598 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912599 : term109 = term110.
Proof. exact (@lem6912598 (NUMERAL 0) term98). Qed.
Lemma lem6912600 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912601 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912602 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912601 h1) (fun h1 : term110 = True => @lem6912600)). Qed.
Lemma lem6912603 : term110 = True.
Proof. exact (EQ_MP (@lem6912602) (@lem6912600)). Qed.
Lemma lem6912604 : term109 = True.
Proof. exact (TRANS (@lem6912599) (@lem6912603)). Qed.
Lemma lem6912605 : True = term109.
Proof. exact (SYM (@lem6912604)). Qed.
Lemma lem6912606 : term109.
Proof. exact (EQ_MP (@lem6912605) (@lem0)). Qed.
Lemma lem6912607 : term222 = term225.
Proof. exact (@lem6912596 (@lem6912606)). Qed.
Lemma lem6912609 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912610 : term131 = term107.
Proof. exact (@lem6912609 term98). Qed.
Lemma lem6912612 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912613 : term131 = term107.
Proof. exact (@lem6912612 term98). Qed.
Lemma lem6912614 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912615 : term226 = term220.
Proof. exact (MK_COMB (@lem6912614) (@lem6912613)). Qed.
Lemma lem6912616 : term225 = term219.
Proof. exact (MK_COMB (@lem6912615) (@lem6912610)). Qed.
Lemma lem6912618 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912619 : term219 = term227.
Proof. exact (@lem6912618 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem6912620 : term227 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem6912621 : term219 = False.
Proof. exact (TRANS (@lem6912619) (@lem6912620)). Qed.
Lemma lem6912622 : term225 = False.
Proof. exact (TRANS (@lem6912616) (@lem6912621)). Qed.
Lemma lem6912623 : term222 = False.
Proof. exact (TRANS (@lem6912607) (@lem6912622)). Qed.
Lemma lem6912624 : term219 = False.
Proof. exact (TRANS (@lem6912584) (@lem6912623)). Qed.
Lemma lem6912625 : term152 = False.
Proof. exact (TRANS (@lem6912575) (@lem6912624)). Qed.
Lemma lem6912626 (h1 : term152) : False.
Proof. exact (EQ_MP (@lem6912625) (@lem6912572 h1)). Qed.
Lemma lem6912627 (h1 : term157) : False.
Proof. exact (or_elim (@lem6912516 h1) (fun h0 : term152 => @lem6912571 h0) (fun h0 : term152 => @lem6912626 h0)). Qed.
Lemma lem6912628 (h1 : term157) : term157.
Proof. exact (h1). Qed.
Lemma lem6912629 (h1 : term152) : term152.
Proof. exact (h1). Qed.
Lemma lem6912631 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6912632 : term152 = term219.
Proof. exact (@lem6912631 term107 term107). Qed.
Lemma lem6912634 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912635 : term107 = term134.
Proof. exact (@lem6912634 (NUMERAL 0)). Qed.
Lemma lem6912637 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912638 : term107 = term134.
Proof. exact (@lem6912637 (NUMERAL 0)). Qed.
Lemma lem6912639 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912640 : term220 = term221.
Proof. exact (MK_COMB (@lem6912639) (@lem6912638)). Qed.
Lemma lem6912641 : term219 = term222.
Proof. exact (MK_COMB (@lem6912640) (@lem6912635)). Qed.
Lemma lem6912642 : term223.
Proof. exact (@lem1980255 term107 term4 term107 term4). Qed.
Lemma lem6912644 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912645 : term109 = term110.
Proof. exact (@lem6912644 (NUMERAL 0) term98). Qed.
Lemma lem6912646 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912647 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912648 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912647 h1) (fun h1 : term110 = True => @lem6912646)). Qed.
Lemma lem6912649 : term110 = True.
Proof. exact (EQ_MP (@lem6912648) (@lem6912646)). Qed.
Lemma lem6912650 : term109 = True.
Proof. exact (TRANS (@lem6912645) (@lem6912649)). Qed.
Lemma lem6912651 : True = term109.
Proof. exact (SYM (@lem6912650)). Qed.
Lemma lem6912652 : term109.
Proof. exact (EQ_MP (@lem6912651) (@lem0)). Qed.
Lemma lem6912653 : term224.
Proof. exact (@lem6912642 (@lem6912652)). Qed.
Lemma lem6912655 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912656 : term109 = term110.
Proof. exact (@lem6912655 (NUMERAL 0) term98). Qed.
Lemma lem6912657 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912658 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912659 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912658 h1) (fun h1 : term110 = True => @lem6912657)). Qed.
Lemma lem6912660 : term110 = True.
Proof. exact (EQ_MP (@lem6912659) (@lem6912657)). Qed.
Lemma lem6912661 : term109 = True.
Proof. exact (TRANS (@lem6912656) (@lem6912660)). Qed.
Lemma lem6912662 : True = term109.
Proof. exact (SYM (@lem6912661)). Qed.
Lemma lem6912663 : term109.
Proof. exact (EQ_MP (@lem6912662) (@lem0)). Qed.
Lemma lem6912664 : term222 = term225.
Proof. exact (@lem6912653 (@lem6912663)). Qed.
Lemma lem6912666 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912667 : term131 = term107.
Proof. exact (@lem6912666 term98). Qed.
Lemma lem6912669 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912670 : term131 = term107.
Proof. exact (@lem6912669 term98). Qed.
Lemma lem6912671 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912672 : term226 = term220.
Proof. exact (MK_COMB (@lem6912671) (@lem6912670)). Qed.
Lemma lem6912673 : term225 = term219.
Proof. exact (MK_COMB (@lem6912672) (@lem6912667)). Qed.
Lemma lem6912675 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912676 : term219 = term227.
Proof. exact (@lem6912675 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem6912677 : term227 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem6912678 : term219 = False.
Proof. exact (TRANS (@lem6912676) (@lem6912677)). Qed.
Lemma lem6912679 : term225 = False.
Proof. exact (TRANS (@lem6912673) (@lem6912678)). Qed.
Lemma lem6912680 : term222 = False.
Proof. exact (TRANS (@lem6912664) (@lem6912679)). Qed.
Lemma lem6912681 : term219 = False.
Proof. exact (TRANS (@lem6912641) (@lem6912680)). Qed.
Lemma lem6912682 : term152 = False.
Proof. exact (TRANS (@lem6912632) (@lem6912681)). Qed.
Lemma lem6912683 (h1 : term152) : False.
Proof. exact (EQ_MP (@lem6912682) (@lem6912629 h1)). Qed.
Lemma lem6912684 (h1 : term152) : term152.
Proof. exact (h1). Qed.
Lemma lem6912686 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6912687 : term152 = term219.
Proof. exact (@lem6912686 term107 term107). Qed.
Lemma lem6912689 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912690 : term107 = term134.
Proof. exact (@lem6912689 (NUMERAL 0)). Qed.
Lemma lem6912692 (x : nat) : (real_of_num x) = (term96 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6912693 : term107 = term134.
Proof. exact (@lem6912692 (NUMERAL 0)). Qed.
Lemma lem6912694 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912695 : term220 = term221.
Proof. exact (MK_COMB (@lem6912694) (@lem6912693)). Qed.
Lemma lem6912696 : term219 = term222.
Proof. exact (MK_COMB (@lem6912695) (@lem6912690)). Qed.
Lemma lem6912697 : term223.
Proof. exact (@lem1980255 term107 term4 term107 term4). Qed.
Lemma lem6912699 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912700 : term109 = term110.
Proof. exact (@lem6912699 (NUMERAL 0) term98). Qed.
Lemma lem6912701 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912702 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912703 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912702 h1) (fun h1 : term110 = True => @lem6912701)). Qed.
Lemma lem6912704 : term110 = True.
Proof. exact (EQ_MP (@lem6912703) (@lem6912701)). Qed.
Lemma lem6912705 : term109 = True.
Proof. exact (TRANS (@lem6912700) (@lem6912704)). Qed.
Lemma lem6912706 : True = term109.
Proof. exact (SYM (@lem6912705)). Qed.
Lemma lem6912707 : term109.
Proof. exact (EQ_MP (@lem6912706) (@lem0)). Qed.
Lemma lem6912708 : term224.
Proof. exact (@lem6912697 (@lem6912707)). Qed.
Lemma lem6912710 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912711 : term109 = term110.
Proof. exact (@lem6912710 (NUMERAL 0) term98). Qed.
Lemma lem6912712 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6912713 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6912714 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem6912713 h1) (fun h1 : term110 = True => @lem6912712)). Qed.
Lemma lem6912715 : term110 = True.
Proof. exact (EQ_MP (@lem6912714) (@lem6912712)). Qed.
Lemma lem6912716 : term109 = True.
Proof. exact (TRANS (@lem6912711) (@lem6912715)). Qed.
Lemma lem6912717 : True = term109.
Proof. exact (SYM (@lem6912716)). Qed.
Lemma lem6912718 : term109.
Proof. exact (EQ_MP (@lem6912717) (@lem0)). Qed.
Lemma lem6912719 : term222 = term225.
Proof. exact (@lem6912708 (@lem6912718)). Qed.
Lemma lem6912721 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912722 : term131 = term107.
Proof. exact (@lem6912721 term98). Qed.
Lemma lem6912724 (x : nat) : (term132 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6912725 : term131 = term107.
Proof. exact (@lem6912724 term98). Qed.
Lemma lem6912726 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6912727 : term226 = term220.
Proof. exact (MK_COMB (@lem6912726) (@lem6912725)). Qed.
Lemma lem6912728 : term225 = term219.
Proof. exact (MK_COMB (@lem6912727) (@lem6912722)). Qed.
Lemma lem6912730 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6912731 : term219 = term227.
Proof. exact (@lem6912730 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem6912732 : term227 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem6912733 : term219 = False.
Proof. exact (TRANS (@lem6912731) (@lem6912732)). Qed.
Lemma lem6912734 : term225 = False.
Proof. exact (TRANS (@lem6912728) (@lem6912733)). Qed.
Lemma lem6912735 : term222 = False.
Proof. exact (TRANS (@lem6912719) (@lem6912734)). Qed.
Lemma lem6912736 : term219 = False.
Proof. exact (TRANS (@lem6912696) (@lem6912735)). Qed.
Lemma lem6912737 : term152 = False.
Proof. exact (TRANS (@lem6912687) (@lem6912736)). Qed.
Lemma lem6912738 (h1 : term152) : False.
Proof. exact (EQ_MP (@lem6912737) (@lem6912684 h1)). Qed.
Lemma lem6912739 (h1 : term157) : False.
Proof. exact (or_elim (@lem6912628 h1) (fun h0 : term152 => @lem6912683 h0) (fun h0 : term152 => @lem6912738 h0)). Qed.
Lemma lem6912740 (h1 : term217) : False.
Proof. exact (or_elim (@lem6912515 h1) (fun h0 : term157 => @lem6912627 h0) (fun h0 : term157 => @lem6912739 h0)). Qed.
Lemma lem6912741 (h1 : term218) : False.
Proof. exact (or_elim (@lem6912402 h1) (fun h0 : term157 => @lem6912514 h0) (fun h0 : term217 => @lem6912740 h0)). Qed.
Lemma lem6912743 (h1 : term218) : term218.
Proof. exact (h1). Qed.
Lemma lem6912744 (h1 : term218) : term218 = False.
Proof. exact (prop_ext (fun h2 : term218 => @lem6912741 h1) (fun h2 : False => @lem6912743 h1)). Qed.
Lemma lem6912745 (h1 : term218) : False.
Proof. exact (EQ_MP (@lem6912744 h1) (@lem6912743 h1)). Qed.
Lemma lem6912746 (h1 : term87) : term87.
Proof. exact (h1). Qed.
Lemma lem6912747 (h1 : term87) : term218.
Proof. exact (EQ_MP (@lem6912368) (@lem6912746 h1)). Qed.
Lemma lem6912748 (h1 : term87) : term218 = False.
Proof. exact (prop_ext (fun h2 : term218 => @lem6912745 h2) (fun h2 : False => @lem6912747 h1)). Qed.
Lemma lem6912749 (h1 : term87) : False.
Proof. exact (EQ_MP (@lem6912748 h1) (@lem6912747 h1)). Qed.
Lemma lem6912750 : term228.
Proof. exact (fun h0 : term87 => @lem6912749 h0). Qed.
Lemma lem6912751 : term229.
Proof. exact (@lem1386578 term19). Qed.
Lemma lem6912754 : term19.
Proof. exact (@lem6912751 (@lem6912750)). Qed.
Lemma lem6912755 : @monoidal real real_mul.
Proof. exact (EQ_MP (@lem6911488) (@lem6912754)). Qed.
