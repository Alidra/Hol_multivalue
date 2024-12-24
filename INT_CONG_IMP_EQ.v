Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_CONG_IMP_EQ_term_abbrevs.
Require Import INT_DIVIDES_LE_spec.
Require Import int_congruent_spec.
Require Import int_divides_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
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
Require Import thm1482679_spec.
Require Import thm1482981_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
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
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
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
Require Import thm2318526_spec.
Require Import thm2318527_spec.
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
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2437519 (x : int) : term0 x.
Proof. exact (@lem2436585 x). Qed.
Lemma lem2437520 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2437521 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2437520 x) (@lem2437519 x)). Qed.
Lemma lem2437522 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2437521 x y). Qed.
Lemma lem2437523 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2437527 (b : int) (a : int) (h1 : (int_divides a b) = (term4 b a)) : (int_divides a b) = (term4 b a).
Proof. exact (h1). Qed.
Lemma lem2437528 (b : int) (a : int) (h1 : (int_divides a b) = (term4 b a)) : (term4 b a) = (int_divides a b).
Proof. exact (SYM (@lem2437527 b a h1)). Qed.
Lemma lem2437529 (a : int) (b : int) (h1 : (term4 b a) = (int_divides a b)) : (term4 b a) = (int_divides a b).
Proof. exact (h1). Qed.
Lemma lem2437530 (a : int) (b : int) (h1 : (term4 b a) = (int_divides a b)) : (int_divides a b) = (term4 b a).
Proof. exact (SYM (@lem2437529 a b h1)). Qed.
Lemma lem2437531 (a : int) (b : int) : ((int_divides a b) = (term4 b a)) = ((term4 b a) = (int_divides a b)).
Proof. exact (prop_ext (fun h1 : (int_divides a b) = (term4 b a) => @lem2437528 b a h1) (fun h1 : (term4 b a) = (int_divides a b) => @lem2437530 a b h1)). Qed.
Lemma lem2437532 (b : int) : (term5 b) = (term6 b).
Proof. exact (fun_ext (fun a : int => @lem2437531 a b)). Qed.
Lemma lem2437533 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2437534 (b : int) : (term7 b) = (term8 b).
Proof. exact (MK_COMB (@lem2437533) (@lem2437532 b)). Qed.
Lemma lem2437535 : term9 = term10.
Proof. exact (fun_ext (fun b : int => @lem2437534 b)). Qed.
Lemma lem2437536 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2437537 : term11 = term12.
Proof. exact (MK_COMB (@lem2437536) (@lem2437535)). Qed.
Lemma lem2437538 : term12.
Proof. exact (EQ_MP (@lem2437537) (@lem2429416)). Qed.
Lemma lem2437539 (b : int) : term13 b.
Proof. exact (@lem2437538 b). Qed.
Lemma lem2437540 (b : int) : (term13 b) = (term8 b).
Proof. exact (eq_refl (term13 b)). Qed.
Lemma lem2437541 (b : int) : term8 b.
Proof. exact (EQ_MP (@lem2437540 b) (@lem2437539 b)). Qed.
Lemma lem2437542 (b : int) (a : int) : term14 b a.
Proof. exact (@lem2437541 b a). Qed.
Lemma lem2437543 (a : int) (b : int) : (term14 b a) = ((term4 b a) = (int_divides a b)).
Proof. exact (eq_refl (term14 b a)). Qed.
Lemma lem2437545 (x : int) : term15 x.
Proof. exact (@lem2437518 x). Qed.
Lemma lem2437546 (x : int) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem2437547 (x : int) : term16 x.
Proof. exact (EQ_MP (@lem2437546 x) (@lem2437545 x)). Qed.
Lemma lem2437548 (x : int) (y : int) : term17 x y.
Proof. exact (@lem2437547 x y). Qed.
Lemma lem2437549 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem2437550 (x : int) (y : int) : term18 x y.
Proof. exact (EQ_MP (@lem2437549 x y) (@lem2437548 x y)). Qed.
Lemma lem2437551 (x : int) (y : int) (n : int) : term19 x y n.
Proof. exact (@lem2437550 x y n). Qed.
Lemma lem2437552 (x : int) (y : int) (n : int) : (term19 x y n) = ((term20 x y n) = (term21 x y n)).
Proof. exact (eq_refl (term19 x y n)). Qed.
Lemma lem2437571 (x : int) (y : int) (n : int) : (term20 x y n) = (term21 x y n).
Proof. exact (EQ_MP (@lem2437552 x y n) (@lem2437551 x y n)). Qed.
Lemma lem2437573 (a : int) (b : int) : (term4 b a) = (int_divides a b).
Proof. exact (EQ_MP (@lem2437543 a b) (@lem2437542 b a)). Qed.
Lemma lem2437574 (n : int) (x : int) (y : int) : (term21 x y n) = (term22 n x y).
Proof. exact (@lem2437573 n (int_sub x y)). Qed.
Lemma lem2437575 (n : int) (x : int) (y : int) : (term20 x y n) = (term22 n x y).
Proof. exact (TRANS (@lem2437571 x y n) (@lem2437574 n x y)). Qed.
Lemma lem2437576 (x : int) (y : int) (n : int) : (term23 x y n) = (term23 x y n).
Proof. exact (eq_refl (term23 x y n)). Qed.
Lemma lem2437577 (n : int) (x : int) (y : int) : (term24 x y n) = (term25 n x y).
Proof. exact (MK_COMB (@lem2437576 x y n) (@lem2437575 n x y)). Qed.
Lemma lem2437580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2437581 (n : int) (x : int) (y : int) : (term26 x y n) = (term27 n x y).
Proof. exact (MK_COMB (@lem2437580) (@lem2437577 n x y)). Qed.
Lemma lem2437584 (x : int) (y : int) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem2437585 (n : int) (x : int) (y : int) : (term28 n x y) = (term29 n x y).
Proof. exact (MK_COMB (@lem2437581 n x y) (@lem2437584 x y)). Qed.
Lemma lem2437588 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (fun_ext (fun n : int => @lem2437585 n x y)). Qed.
Lemma lem2437589 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2437590 (x : int) (y : int) : (term32 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem2437589) (@lem2437588 x y)). Qed.
Lemma lem2437595 (x : int) : (term34 x) = (term35 x).
Proof. exact (fun_ext (fun y : int => @lem2437590 x y)). Qed.
Lemma lem2437596 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2437597 (x : int) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem2437596) (@lem2437595 x)). Qed.
Lemma lem2437602 : term38 = term39.
Proof. exact (fun_ext (fun x : int => @lem2437597 x)). Qed.
Lemma lem2437603 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2437604 : term40 = term41.
Proof. exact (MK_COMB (@lem2437603) (@lem2437602)). Qed.
Lemma lem2437609 : term41 = term40.
Proof. exact (SYM (@lem2437604)). Qed.
Lemma lem2437610 (n : int) (x : int) (y : int) (h1 : term25 n x y) : term25 n x y.
Proof. exact (h1). Qed.
Lemma lem2437611 (n : int) (x : int) (y : int) (h1 : term22 n x y) : term22 n x y.
Proof. exact (h1). Qed.
Lemma lem2437612 (x : int) (y : int) (n : int) (h1 : term42 x y n) : term42 x y n.
Proof. exact (h1). Qed.
Lemma lem2437614 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2437523 x y) (@lem2437522 x y)). Qed.
Lemma lem2437615 (n : int) (x : int) (y : int) : term43 n x y.
Proof. exact (@lem2437614 n (int_sub x y)). Qed.
Lemma lem2437616 (n : int) (x : int) (y : int) (h1 : term22 n x y) : term44 n x y.
Proof. exact (@lem2437615 n x y (@lem2437611 n x y h1)). Qed.
Lemma lem2437617 (n : int) (x : int) (y : int) : (term45 n x y) = (term46 n x y).
Proof. exact (@lem2318604 (term46 n x y)). Qed.
Lemma lem2437643 (n : int) (x : int) (y : int) : (term47 n x y) = (term48 n x y).
Proof. exact (@lem17362 (term44 n x y) (x = y)). Qed.
Lemma lem2437645 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2437646 (n : int) (x : int) (y : int) : (term50 n x y) = (term51 n x y).
Proof. exact (MK_COMB (@lem2437645 n x y) (@lem2437643 n x y)). Qed.
Lemma lem2437647 (n : int) (x : int) (y : int) : (term52 n x y) = (term50 n x y).
Proof. exact (@lem17362 (term22 n x y) (term53 n x y)). Qed.
Lemma lem2437648 (n : int) (x : int) (y : int) : (term52 n x y) = (term51 n x y).
Proof. exact (TRANS (@lem2437647 n x y) (@lem2437646 n x y)). Qed.
Lemma lem2437650 (x : int) (y : int) (n : int) : (term23 x y n) = (term23 x y n).
Proof. exact (eq_refl (term23 x y n)). Qed.
Lemma lem2437651 (n : int) (x : int) (y : int) : (term54 n x y) = (term55 n x y).
Proof. exact (MK_COMB (@lem2437650 x y n) (@lem2437648 n x y)). Qed.
Lemma lem2437652 (n : int) (x : int) (y : int) : (term56 n x y) = (term54 n x y).
Proof. exact (@lem17362 (term42 x y n) (term57 n x y)). Qed.
Lemma lem2437674 (n : int) (x : int) (y : int) : (term56 n x y) = (term55 n x y).
Proof. exact (TRANS (@lem2437652 n x y) (@lem2437651 n x y)). Qed.
Lemma lem2437676 (x : int) (y : int) : (int_lt x y) = (term58 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2437677 (x : int) (y : int) (n : int) : (term42 x y n) = (term59 x y n).
Proof. exact (@lem2437676 (term60 x y) n). Qed.
Lemma lem2437679 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2437680 (x : int) (y : int) (n : int) : (term59 x y n) = (term62 x y n).
Proof. exact (@lem2437679 (term63 x y) n). Qed.
Lemma lem2437682 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2437683 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (@lem2437682 (term60 x y) term68). Qed.
Lemma lem2437685 (x : int) : (term69 x) = (term70 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2437686 (x : int) (y : int) : (term71 x y) = (term72 x y).
Proof. exact (@lem2437685 (int_sub x y)). Qed.
Lemma lem2437688 (x : int) (y : int) : (term73 x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2437689 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2437690 (x : int) (y : int) : (term72 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem2437689) (@lem2437688 x y)). Qed.
Lemma lem2437691 (x : int) (y : int) : (term71 x y) = (term75 x y).
Proof. exact (TRANS (@lem2437686 x y) (@lem2437690 x y)). Qed.
Lemma lem2437692 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2437693 (x : int) (y : int) : (term76 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem2437692) (@lem2437691 x y)). Qed.
Lemma lem2437695 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2437696 : term79 = term80.
Proof. exact (@lem2437695 term81). Qed.
Lemma lem2437697 (x : int) (y : int) : (term67 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem2437693 x y) (@lem2437696)). Qed.
Lemma lem2437698 (x : int) (y : int) : (term66 x y) = (term82 x y).
Proof. exact (TRANS (@lem2437683 x y) (@lem2437697 x y)). Qed.
Lemma lem2437699 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2437700 (x : int) (y : int) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem2437699) (@lem2437698 x y)). Qed.
Lemma lem2437701 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2437702 (x : int) (y : int) (n : int) : (term62 x y n) = (term85 x y n).
Proof. exact (MK_COMB (@lem2437700 x y) (@lem2437701 n)). Qed.
Lemma lem2437703 (x : int) (y : int) (n : int) : (term59 x y n) = (term85 x y n).
Proof. exact (TRANS (@lem2437680 x y n) (@lem2437702 x y n)). Qed.
Lemma lem2437704 (x : int) (y : int) (n : int) : (term42 x y n) = (term85 x y n).
Proof. exact (TRANS (@lem2437677 x y n) (@lem2437703 x y n)). Qed.
Lemma lem2437710 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2437711 (n : int) (x : int) (y : int) : (term86 n x y) = (term87 n x y).
Proof. exact (@lem2437710 (int_abs n) (term60 x y)). Qed.
Lemma lem2437713 (x : int) : (term69 x) = (term70 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2437714 (n : int) : (term69 n) = (term70 n).
Proof. exact (@lem2437713 n). Qed.
Lemma lem2437715 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2437716 (n : int) : (term88 n) = (term89 n).
Proof. exact (MK_COMB (@lem2437715) (@lem2437714 n)). Qed.
Lemma lem2437718 (x : int) : (term69 x) = (term70 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2437719 (x : int) (y : int) : (term71 x y) = (term72 x y).
Proof. exact (@lem2437718 (int_sub x y)). Qed.
Lemma lem2437721 (x : int) (y : int) : (term73 x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2437722 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2437723 (x : int) (y : int) : (term72 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem2437722) (@lem2437721 x y)). Qed.
Lemma lem2437724 (x : int) (y : int) : (term71 x y) = (term75 x y).
Proof. exact (TRANS (@lem2437719 x y) (@lem2437723 x y)). Qed.
Lemma lem2437725 (n : int) (x : int) (y : int) : (term87 n x y) = (term90 n x y).
Proof. exact (MK_COMB (@lem2437716 n) (@lem2437724 x y)). Qed.
Lemma lem2437727 (n : int) (x : int) (y : int) : (term86 n x y) = (term90 n x y).
Proof. exact (TRANS (@lem2437711 n x y) (@lem2437725 n x y)). Qed.
Lemma lem2437730 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2437731 (x : int) (y : int) : ((int_sub x y) = term91) = ((term73 x y) = term92).
Proof. exact (@lem2437730 (int_sub x y) term91). Qed.
Lemma lem2437735 (x : int) (y : int) : (term73 x y) = (term74 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2437736 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2437737 (x : int) (y : int) : (term93 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem2437736) (@lem2437735 x y)). Qed.
Lemma lem2437739 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2437740 : term92 = term95.
Proof. exact (@lem2437739 (NUMERAL 0)). Qed.
Lemma lem2437741 (x : int) (y : int) : ((term73 x y) = term92) = ((term74 x y) = term95).
Proof. exact (MK_COMB (@lem2437737 x y) (@lem2437740)). Qed.
Lemma lem2437743 (x : int) (y : int) : ((int_sub x y) = term91) = ((term74 x y) = term95).
Proof. exact (TRANS (@lem2437731 x y) (@lem2437741 x y)). Qed.
Lemma lem2437744 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2437745 (n : int) (x : int) (y : int) : (term96 n x y) = (term97 n x y).
Proof. exact (MK_COMB (@lem2437744) (@lem2437727 n x y)). Qed.
Lemma lem2437746 (n : int) (x : int) (y : int) : (term44 n x y) = (term98 n x y).
Proof. exact (MK_COMB (@lem2437745 n x y) (@lem2437743 x y)). Qed.
Lemma lem2437748 (y : int) (x : int) : (term99 x y) = (term100 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2437750 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2437751 (x : int) (y : int) : (term58 x y) = (term101 x y).
Proof. exact (@lem2437750 (term102 x) y). Qed.
Lemma lem2437753 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2437754 (x : int) : (term103 x) = (term104 x).
Proof. exact (@lem2437753 x term68). Qed.
Lemma lem2437756 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2437757 : term79 = term80.
Proof. exact (@lem2437756 term81). Qed.
Lemma lem2437758 (x : int) : (term105 x) = (term105 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2437759 (x : int) : (term104 x) = (term106 x).
Proof. exact (MK_COMB (@lem2437758 x) (@lem2437757)). Qed.
Lemma lem2437760 (x : int) : (term103 x) = (term106 x).
Proof. exact (TRANS (@lem2437754 x) (@lem2437759 x)). Qed.
Lemma lem2437761 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2437762 (x : int) : (term107 x) = (term108 x).
Proof. exact (MK_COMB (@lem2437761) (@lem2437760 x)). Qed.
Lemma lem2437763 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2437764 (x : int) (y : int) : (term101 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem2437762 x) (@lem2437763 y)). Qed.
Lemma lem2437765 (x : int) (y : int) : (term58 x y) = (term109 x y).
Proof. exact (TRANS (@lem2437751 x y) (@lem2437764 x y)). Qed.
Lemma lem2437766 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2437767 (x : int) (y : int) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem2437766) (@lem2437765 x y)). Qed.
Lemma lem2437769 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2437770 (y : int) (x : int) : (term58 y x) = (term101 y x).
Proof. exact (@lem2437769 (term102 y) x). Qed.
Lemma lem2437772 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2437773 (y : int) : (term103 y) = (term104 y).
Proof. exact (@lem2437772 y term68). Qed.
Lemma lem2437775 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2437776 : term79 = term80.
Proof. exact (@lem2437775 term81). Qed.
Lemma lem2437777 (y : int) : (term105 y) = (term105 y).
Proof. exact (eq_refl (term105 y)). Qed.
Lemma lem2437778 (y : int) : (term104 y) = (term106 y).
Proof. exact (MK_COMB (@lem2437777 y) (@lem2437776)). Qed.
Lemma lem2437779 (y : int) : (term103 y) = (term106 y).
Proof. exact (TRANS (@lem2437773 y) (@lem2437778 y)). Qed.
Lemma lem2437780 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2437781 (y : int) : (term107 y) = (term108 y).
Proof. exact (MK_COMB (@lem2437780) (@lem2437779 y)). Qed.
Lemma lem2437782 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2437783 (y : int) (x : int) : (term101 y x) = (term109 y x).
Proof. exact (MK_COMB (@lem2437781 y) (@lem2437782 x)). Qed.
Lemma lem2437784 (y : int) (x : int) : (term58 y x) = (term109 y x).
Proof. exact (TRANS (@lem2437770 y x) (@lem2437783 y x)). Qed.
Lemma lem2437785 (y : int) (x : int) : (term100 y x) = (term112 y x).
Proof. exact (MK_COMB (@lem2437767 x y) (@lem2437784 y x)). Qed.
Lemma lem2437786 (y : int) (x : int) : (term99 x y) = (term112 y x).
Proof. exact (TRANS (@lem2437748 y x) (@lem2437785 y x)). Qed.
Lemma lem2437787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2437788 (n : int) (x : int) (y : int) : (term113 n x y) = (term114 n x y).
Proof. exact (MK_COMB (@lem2437787) (@lem2437746 n x y)). Qed.
Lemma lem2437789 (n : int) (y : int) (x : int) : (term48 n x y) = (term115 n y x).
Proof. exact (MK_COMB (@lem2437788 n x y) (@lem2437786 y x)). Qed.
Lemma lem2437791 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2437792 (n : int) (y : int) (x : int) : (term51 n x y) = (term116 n y x).
Proof. exact (MK_COMB (@lem2437791 n x y) (@lem2437789 n y x)). Qed.
Lemma lem2437793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2437794 (x : int) (y : int) (n : int) : (term23 x y n) = (term117 x y n).
Proof. exact (MK_COMB (@lem2437793) (@lem2437704 x y n)). Qed.
Lemma lem2437795 (n : int) (y : int) (x : int) : (term55 n x y) = (term118 n y x).
Proof. exact (MK_COMB (@lem2437794 x y n) (@lem2437792 n y x)). Qed.
Lemma lem2437796 (n : int) (y : int) (x : int) : (term56 n x y) = (term118 n y x).
Proof. exact (TRANS (@lem2437674 n x y) (@lem2437795 n y x)). Qed.
Lemma lem2437800 (t : Prop) : (term119 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2437856 (n : int) (y : int) (x : int) : (term120 n y x) = (term118 n y x).
Proof. exact (@lem2437800 (term118 n y x)). Qed.
Lemma lem2437857 (n : int) (x : int) (y : int) : (term85 x y n) = (term121 n x y).
Proof. exact (@lem1988287 (real_of_int n) (term82 x y)). Qed.
Lemma lem2437858 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2437871 (x : int) (y : int) : (term74 x y) = (term122 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2437872 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2437873 (x : int) (y : int) : (term75 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem2437872) (@lem2437871 x y)). Qed.
Lemma lem2437874 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2437875 (x : int) (y : int) : (term77 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem2437874) (@lem2437873 x y)). Qed.
Lemma lem2437878 (x : int) (y : int) : (term82 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem2437875 x y) (@lem2437858)). Qed.
Lemma lem2437881 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2437882 (n : int) (x : int) (y : int) : (term127 n x y) = (term128 n x y).
Proof. exact (MK_COMB (@lem2437881 n) (@lem2437878 x y)). Qed.
Lemma lem2437883 (n : int) (x : int) (y : int) : (term128 n x y) = (term129 n x y).
Proof. exact (@lem1982792 (real_of_int n) (term125 x y)). Qed.
Lemma lem2437884 (x : int) (y : int) : (term130 x y) = (term131 x y).
Proof. exact (@lem1982781 (term123 x y) term132 term80). Qed.
Lemma lem2437886 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2437887 : term80 = term134.
Proof. exact (@lem2437886 term81). Qed.
Lemma lem2437889 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2437890 : term132 = term137.
Proof. exact (@lem2437889 term81). Qed.
Lemma lem2437891 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2437892 : term138 = term139.
Proof. exact (MK_COMB (@lem2437891) (@lem2437890)). Qed.
Lemma lem2437893 : term140 = term141.
Proof. exact (MK_COMB (@lem2437892) (@lem2437887)). Qed.
Lemma lem2437894 : term141 = term142.
Proof. exact (@lem1981613 term132 term80 term80 term80). Qed.
Lemma lem2437896 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2437897 : term145 = term146.
Proof. exact (@lem2437896 term81 term81). Qed.
Lemma lem2437898 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2437899 : term148 = term81.
Proof. exact (EQ_MP (@lem2437898) (@lem940073)). Qed.
Lemma lem2437900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2437901 : term146 = term80.
Proof. exact (MK_COMB (@lem2437900) (@lem2437899)). Qed.
Lemma lem2437902 : term145 = term80.
Proof. exact (TRANS (@lem2437897) (@lem2437901)). Qed.
Lemma lem2437904 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2437905 : term140 = term151.
Proof. exact (@lem2437904 term81 term81). Qed.
Lemma lem2437906 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2437907 : term148 = term81.
Proof. exact (EQ_MP (@lem2437906) (@lem940073)). Qed.
Lemma lem2437908 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2437909 : term146 = term80.
Proof. exact (MK_COMB (@lem2437908) (@lem2437907)). Qed.
Lemma lem2437910 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2437911 : term151 = term132.
Proof. exact (MK_COMB (@lem2437910) (@lem2437909)). Qed.
Lemma lem2437912 : term140 = term132.
Proof. exact (TRANS (@lem2437905) (@lem2437911)). Qed.
Lemma lem2437913 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2437914 : term152 = term153.
Proof. exact (MK_COMB (@lem2437913) (@lem2437912)). Qed.
Lemma lem2437915 : term142 = term137.
Proof. exact (MK_COMB (@lem2437914) (@lem2437902)). Qed.
Lemma lem2437916 : term141 = term137.
Proof. exact (TRANS (@lem2437894) (@lem2437915)). Qed.
Lemma lem2437917 : term140 = term137.
Proof. exact (TRANS (@lem2437893) (@lem2437916)). Qed.
Lemma lem2437919 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2437920 : term137 = term132.
Proof. exact (@lem2437919 term132). Qed.
Lemma lem2437921 : term140 = term132.
Proof. exact (TRANS (@lem2437917) (@lem2437920)). Qed.
Lemma lem2437924 (x : int) (y : int) : (term155 x y) = (term155 x y).
Proof. exact (eq_refl (term155 x y)). Qed.
Lemma lem2437925 (x : int) (y : int) : (term131 x y) = (term156 x y).
Proof. exact (MK_COMB (@lem2437924 x y) (@lem2437921)). Qed.
Lemma lem2437926 (x : int) (y : int) : (term130 x y) = (term156 x y).
Proof. exact (TRANS (@lem2437884 x y) (@lem2437925 x y)). Qed.
Lemma lem2437927 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2437928 (n : int) (x : int) (y : int) : (term129 n x y) = (term157 n x y).
Proof. exact (MK_COMB (@lem2437927 n) (@lem2437926 x y)). Qed.
Lemma lem2437933 (x : int) (y : int) (n : int) : (term157 n x y) = (term158 x y n).
Proof. exact (@lem1982757 (term159 x y) (real_of_int n) term132). Qed.
Lemma lem2437934 (x : int) (y : int) (n : int) : (term129 n x y) = (term158 x y n).
Proof. exact (TRANS (@lem2437928 n x y) (@lem2437933 x y n)). Qed.
Lemma lem2437935 (x : int) (y : int) (n : int) : (term128 n x y) = (term158 x y n).
Proof. exact (TRANS (@lem2437883 n x y) (@lem2437934 x y n)). Qed.
Lemma lem2437936 (x : int) (y : int) (n : int) : (term127 n x y) = (term158 x y n).
Proof. exact (TRANS (@lem2437882 n x y) (@lem2437935 x y n)). Qed.
Lemma lem2437937 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2437938 (x : int) (y : int) (n : int) : (term160 n x y) = (term161 x y n).
Proof. exact (MK_COMB (@lem2437937) (@lem2437936 x y n)). Qed.
Lemma lem2437939 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2437940 (x : int) (y : int) (n : int) : (term121 n x y) = (term162 x y n).
Proof. exact (MK_COMB (@lem2437938 x y n) (@lem2437939)). Qed.
Lemma lem2437941 (x : int) (y : int) (n : int) : (term85 x y n) = (term162 x y n).
Proof. exact (TRANS (@lem2437857 n x y) (@lem2437940 x y n)). Qed.
Lemma lem2437943 (x : int) (y : int) (n : int) : (term90 n x y) = (term163 x y n).
Proof. exact (@lem1988287 (term75 x y) (term70 n)). Qed.
Lemma lem2437946 (n : int) : (term70 n) = (term70 n).
Proof. exact (eq_refl (term70 n)). Qed.
Lemma lem2437959 (x : int) (y : int) : (term74 x y) = (term122 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2437960 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2437961 (x : int) (y : int) : (term75 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem2437960) (@lem2437959 x y)). Qed.
Lemma lem2437962 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2437963 (x : int) (y : int) : (term164 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem2437962) (@lem2437961 x y)). Qed.
Lemma lem2437964 (x : int) (y : int) (n : int) : (term166 x y n) = (term167 x y n).
Proof. exact (MK_COMB (@lem2437963 x y) (@lem2437946 n)). Qed.
Lemma lem2437965 (x : int) (y : int) (n : int) : (term167 x y n) = (term168 x y n).
Proof. exact (@lem1982792 (term123 x y) (term70 n)). Qed.
Lemma lem2437970 (n : int) (x : int) (y : int) : (term168 x y n) = (term169 n x y).
Proof. exact (@lem1982761 (term170 n) (term123 x y)). Qed.
Lemma lem2437971 (n : int) (x : int) (y : int) : (term167 x y n) = (term169 n x y).
Proof. exact (TRANS (@lem2437965 x y n) (@lem2437970 n x y)). Qed.
Lemma lem2437972 (n : int) (x : int) (y : int) : (term166 x y n) = (term169 n x y).
Proof. exact (TRANS (@lem2437964 x y n) (@lem2437971 n x y)). Qed.
Lemma lem2437973 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2437974 (n : int) (x : int) (y : int) : (term171 x y n) = (term172 n x y).
Proof. exact (MK_COMB (@lem2437973) (@lem2437972 n x y)). Qed.
Lemma lem2437975 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2437976 (n : int) (x : int) (y : int) : (term163 x y n) = (term173 n x y).
Proof. exact (MK_COMB (@lem2437974 n x y) (@lem2437975)). Qed.
Lemma lem2437977 (n : int) (x : int) (y : int) : (term90 n x y) = (term173 n x y).
Proof. exact (TRANS (@lem2437943 x y n) (@lem2437976 n x y)). Qed.
Lemma lem2437978 (x : int) (y : int) : ((term74 x y) = term95) = ((term174 x y) = term95).
Proof. exact (@lem1988293 (term74 x y) term95). Qed.
Lemma lem2437979 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2437992 (x : int) (y : int) : (term74 x y) = (term122 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2437993 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2437994 (x : int) (y : int) : (term175 x y) = (term176 x y).
Proof. exact (MK_COMB (@lem2437993) (@lem2437992 x y)). Qed.
Lemma lem2437995 (x : int) (y : int) : (term174 x y) = (term177 x y).
Proof. exact (MK_COMB (@lem2437994 x y) (@lem2437979)). Qed.
Lemma lem2437996 (x : int) (y : int) : (term177 x y) = (term178 x y).
Proof. exact (@lem1982792 (term122 x y) term95). Qed.
Lemma lem2437998 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2437999 : term95 = term179.
Proof. exact (@lem2437998 (NUMERAL 0)). Qed.
Lemma lem2438001 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438002 : term132 = term137.
Proof. exact (@lem2438001 term81). Qed.
Lemma lem2438003 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438004 : term138 = term139.
Proof. exact (MK_COMB (@lem2438003) (@lem2438002)). Qed.
Lemma lem2438005 : term180 = term181.
Proof. exact (MK_COMB (@lem2438004) (@lem2437999)). Qed.
Lemma lem2438006 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2438008 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438009 : term145 = term146.
Proof. exact (@lem2438008 term81 term81). Qed.
Lemma lem2438010 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438011 : term148 = term81.
Proof. exact (EQ_MP (@lem2438010) (@lem940073)). Qed.
Lemma lem2438012 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438013 : term146 = term80.
Proof. exact (MK_COMB (@lem2438012) (@lem2438011)). Qed.
Lemma lem2438014 : term145 = term80.
Proof. exact (TRANS (@lem2438009) (@lem2438013)). Qed.
Lemma lem2438016 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2438017 : term180 = term95.
Proof. exact (@lem2438016 term81). Qed.
Lemma lem2438018 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438019 : term184 = term185.
Proof. exact (MK_COMB (@lem2438018) (@lem2438017)). Qed.
Lemma lem2438020 : term182 = term179.
Proof. exact (MK_COMB (@lem2438019) (@lem2438014)). Qed.
Lemma lem2438021 : term181 = term179.
Proof. exact (TRANS (@lem2438006) (@lem2438020)). Qed.
Lemma lem2438022 : term180 = term179.
Proof. exact (TRANS (@lem2438005) (@lem2438021)). Qed.
Lemma lem2438024 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438025 : term179 = term95.
Proof. exact (@lem2438024 term95). Qed.
Lemma lem2438026 : term180 = term95.
Proof. exact (TRANS (@lem2438022) (@lem2438025)). Qed.
Lemma lem2438027 (x : int) (y : int) : (term186 x y) = (term186 x y).
Proof. exact (eq_refl (term186 x y)). Qed.
Lemma lem2438028 (x : int) (y : int) : (term178 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem2438027 x y) (@lem2438026)). Qed.
Lemma lem2438029 (x : int) (y : int) : (term187 x y) = (term122 x y).
Proof. exact (@lem1982723 (term122 x y)). Qed.
Lemma lem2438030 (x : int) (y : int) : (term178 x y) = (term122 x y).
Proof. exact (TRANS (@lem2438028 x y) (@lem2438029 x y)). Qed.
Lemma lem2438031 (x : int) (y : int) : (term177 x y) = (term122 x y).
Proof. exact (TRANS (@lem2437996 x y) (@lem2438030 x y)). Qed.
Lemma lem2438032 (x : int) (y : int) : (term174 x y) = (term122 x y).
Proof. exact (TRANS (@lem2437995 x y) (@lem2438031 x y)). Qed.
Lemma lem2438033 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2438034 (x : int) (y : int) : (term188 x y) = (term189 x y).
Proof. exact (MK_COMB (@lem2438033) (@lem2438032 x y)). Qed.
Lemma lem2438035 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438036 (x : int) (y : int) : ((term174 x y) = term95) = ((term122 x y) = term95).
Proof. exact (MK_COMB (@lem2438034 x y) (@lem2438035)). Qed.
Lemma lem2438037 (x : int) (y : int) : ((term74 x y) = term95) = ((term122 x y) = term95).
Proof. exact (TRANS (@lem2437978 x y) (@lem2438036 x y)). Qed.
Lemma lem2438038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2438039 (n : int) (x : int) (y : int) : (term97 n x y) = (term190 n x y).
Proof. exact (MK_COMB (@lem2438038) (@lem2437977 n x y)). Qed.
Lemma lem2438040 (n : int) (x : int) (y : int) : (term98 n x y) = (term191 n x y).
Proof. exact (MK_COMB (@lem2438039 n x y) (@lem2438037 x y)). Qed.
Lemma lem2438041 (y : int) (x : int) : (term109 x y) = (term192 y x).
Proof. exact (@lem1988287 (real_of_int y) (term106 x)). Qed.
Lemma lem2438053 (y : int) (x : int) : (term193 y x) = (term194 y x).
Proof. exact (@lem1982792 (real_of_int y) (term106 x)). Qed.
Lemma lem2438054 (x : int) : (term195 x) = (term196 x).
Proof. exact (@lem1982781 (real_of_int x) term132 term80). Qed.
Lemma lem2438056 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2438057 : term80 = term134.
Proof. exact (@lem2438056 term81). Qed.
Lemma lem2438059 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438060 : term132 = term137.
Proof. exact (@lem2438059 term81). Qed.
Lemma lem2438061 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438062 : term138 = term139.
Proof. exact (MK_COMB (@lem2438061) (@lem2438060)). Qed.
Lemma lem2438063 : term140 = term141.
Proof. exact (MK_COMB (@lem2438062) (@lem2438057)). Qed.
Lemma lem2438064 : term141 = term142.
Proof. exact (@lem1981613 term132 term80 term80 term80). Qed.
Lemma lem2438066 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438067 : term145 = term146.
Proof. exact (@lem2438066 term81 term81). Qed.
Lemma lem2438068 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438069 : term148 = term81.
Proof. exact (EQ_MP (@lem2438068) (@lem940073)). Qed.
Lemma lem2438070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438071 : term146 = term80.
Proof. exact (MK_COMB (@lem2438070) (@lem2438069)). Qed.
Lemma lem2438072 : term145 = term80.
Proof. exact (TRANS (@lem2438067) (@lem2438071)). Qed.
Lemma lem2438074 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2438075 : term140 = term151.
Proof. exact (@lem2438074 term81 term81). Qed.
Lemma lem2438076 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438077 : term148 = term81.
Proof. exact (EQ_MP (@lem2438076) (@lem940073)). Qed.
Lemma lem2438078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438079 : term146 = term80.
Proof. exact (MK_COMB (@lem2438078) (@lem2438077)). Qed.
Lemma lem2438080 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2438081 : term151 = term132.
Proof. exact (MK_COMB (@lem2438080) (@lem2438079)). Qed.
Lemma lem2438082 : term140 = term132.
Proof. exact (TRANS (@lem2438075) (@lem2438081)). Qed.
Lemma lem2438083 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438084 : term152 = term153.
Proof. exact (MK_COMB (@lem2438083) (@lem2438082)). Qed.
Lemma lem2438085 : term142 = term137.
Proof. exact (MK_COMB (@lem2438084) (@lem2438072)). Qed.
Lemma lem2438086 : term141 = term137.
Proof. exact (TRANS (@lem2438064) (@lem2438085)). Qed.
Lemma lem2438087 : term140 = term137.
Proof. exact (TRANS (@lem2438063) (@lem2438086)). Qed.
Lemma lem2438089 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438090 : term137 = term132.
Proof. exact (@lem2438089 term132). Qed.
Lemma lem2438091 : term140 = term132.
Proof. exact (TRANS (@lem2438087) (@lem2438090)). Qed.
Lemma lem2438094 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2438095 (x : int) : (term196 x) = (term198 x).
Proof. exact (MK_COMB (@lem2438094 x) (@lem2438091)). Qed.
Lemma lem2438096 (x : int) : (term195 x) = (term198 x).
Proof. exact (TRANS (@lem2438054 x) (@lem2438095 x)). Qed.
Lemma lem2438097 (y : int) : (term105 y) = (term105 y).
Proof. exact (eq_refl (term105 y)). Qed.
Lemma lem2438098 (y : int) (x : int) : (term194 y x) = (term199 y x).
Proof. exact (MK_COMB (@lem2438097 y) (@lem2438096 x)). Qed.
Lemma lem2438103 (x : int) (y : int) : (term199 y x) = (term200 x y).
Proof. exact (@lem1982757 (term201 x) (real_of_int y) term132). Qed.
Lemma lem2438104 (x : int) (y : int) : (term194 y x) = (term200 x y).
Proof. exact (TRANS (@lem2438098 y x) (@lem2438103 x y)). Qed.
Lemma lem2438106 (x : int) (y : int) : (term193 y x) = (term200 x y).
Proof. exact (TRANS (@lem2438053 y x) (@lem2438104 x y)). Qed.
Lemma lem2438107 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438108 (x : int) (y : int) : (term202 y x) = (term203 x y).
Proof. exact (MK_COMB (@lem2438107) (@lem2438106 x y)). Qed.
Lemma lem2438109 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438110 (x : int) (y : int) : (term192 y x) = (term204 x y).
Proof. exact (MK_COMB (@lem2438108 x y) (@lem2438109)). Qed.
Lemma lem2438111 (x : int) (y : int) : (term109 x y) = (term204 x y).
Proof. exact (TRANS (@lem2438041 y x) (@lem2438110 x y)). Qed.
Lemma lem2438112 (x : int) (y : int) : (term109 y x) = (term192 x y).
Proof. exact (@lem1988287 (real_of_int x) (term106 y)). Qed.
Lemma lem2438124 (x : int) (y : int) : (term193 x y) = (term194 x y).
Proof. exact (@lem1982792 (real_of_int x) (term106 y)). Qed.
Lemma lem2438125 (y : int) : (term195 y) = (term196 y).
Proof. exact (@lem1982781 (real_of_int y) term132 term80). Qed.
Lemma lem2438127 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2438128 : term80 = term134.
Proof. exact (@lem2438127 term81). Qed.
Lemma lem2438130 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438131 : term132 = term137.
Proof. exact (@lem2438130 term81). Qed.
Lemma lem2438132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438133 : term138 = term139.
Proof. exact (MK_COMB (@lem2438132) (@lem2438131)). Qed.
Lemma lem2438134 : term140 = term141.
Proof. exact (MK_COMB (@lem2438133) (@lem2438128)). Qed.
Lemma lem2438135 : term141 = term142.
Proof. exact (@lem1981613 term132 term80 term80 term80). Qed.
Lemma lem2438137 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438138 : term145 = term146.
Proof. exact (@lem2438137 term81 term81). Qed.
Lemma lem2438139 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438140 : term148 = term81.
Proof. exact (EQ_MP (@lem2438139) (@lem940073)). Qed.
Lemma lem2438141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438142 : term146 = term80.
Proof. exact (MK_COMB (@lem2438141) (@lem2438140)). Qed.
Lemma lem2438143 : term145 = term80.
Proof. exact (TRANS (@lem2438138) (@lem2438142)). Qed.
Lemma lem2438145 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2438146 : term140 = term151.
Proof. exact (@lem2438145 term81 term81). Qed.
Lemma lem2438147 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438148 : term148 = term81.
Proof. exact (EQ_MP (@lem2438147) (@lem940073)). Qed.
Lemma lem2438149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438150 : term146 = term80.
Proof. exact (MK_COMB (@lem2438149) (@lem2438148)). Qed.
Lemma lem2438151 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2438152 : term151 = term132.
Proof. exact (MK_COMB (@lem2438151) (@lem2438150)). Qed.
Lemma lem2438153 : term140 = term132.
Proof. exact (TRANS (@lem2438146) (@lem2438152)). Qed.
Lemma lem2438154 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438155 : term152 = term153.
Proof. exact (MK_COMB (@lem2438154) (@lem2438153)). Qed.
Lemma lem2438156 : term142 = term137.
Proof. exact (MK_COMB (@lem2438155) (@lem2438143)). Qed.
Lemma lem2438157 : term141 = term137.
Proof. exact (TRANS (@lem2438135) (@lem2438156)). Qed.
Lemma lem2438158 : term140 = term137.
Proof. exact (TRANS (@lem2438134) (@lem2438157)). Qed.
Lemma lem2438160 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438161 : term137 = term132.
Proof. exact (@lem2438160 term132). Qed.
Lemma lem2438162 : term140 = term132.
Proof. exact (TRANS (@lem2438158) (@lem2438161)). Qed.
Lemma lem2438165 (y : int) : (term197 y) = (term197 y).
Proof. exact (eq_refl (term197 y)). Qed.
Lemma lem2438166 (y : int) : (term196 y) = (term198 y).
Proof. exact (MK_COMB (@lem2438165 y) (@lem2438162)). Qed.
Lemma lem2438167 (y : int) : (term195 y) = (term198 y).
Proof. exact (TRANS (@lem2438125 y) (@lem2438166 y)). Qed.
Lemma lem2438168 (x : int) : (term105 x) = (term105 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2438171 (x : int) (y : int) : (term194 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem2438168 x) (@lem2438167 y)). Qed.
Lemma lem2438173 (x : int) (y : int) : (term193 x y) = (term199 x y).
Proof. exact (TRANS (@lem2438124 x y) (@lem2438171 x y)). Qed.
Lemma lem2438174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438175 (x : int) (y : int) : (term202 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem2438174) (@lem2438173 x y)). Qed.
Lemma lem2438176 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438177 (x : int) (y : int) : (term192 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem2438175 x y) (@lem2438176)). Qed.
Lemma lem2438178 (x : int) (y : int) : (term109 y x) = (term206 x y).
Proof. exact (TRANS (@lem2438112 x y) (@lem2438177 x y)). Qed.
Lemma lem2438179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2438180 (x : int) (y : int) : (term111 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem2438179) (@lem2438111 x y)). Qed.
Lemma lem2438181 (x : int) (y : int) : (term112 y x) = (term208 x y).
Proof. exact (MK_COMB (@lem2438180 x y) (@lem2438178 x y)). Qed.
Lemma lem2438182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438183 (n : int) (x : int) (y : int) : (term114 n x y) = (term209 n x y).
Proof. exact (MK_COMB (@lem2438182) (@lem2438040 n x y)). Qed.
Lemma lem2438184 (n : int) (x : int) (y : int) : (term115 n y x) = (term210 n x y).
Proof. exact (MK_COMB (@lem2438183 n x y) (@lem2438181 x y)). Qed.
Lemma lem2438186 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2438187 (n : int) (x : int) (y : int) : (term116 n y x) = (term211 n x y).
Proof. exact (MK_COMB (@lem2438186 n x y) (@lem2438184 n x y)). Qed.
Lemma lem2438188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438189 (x : int) (y : int) (n : int) : (term117 x y n) = (term212 x y n).
Proof. exact (MK_COMB (@lem2438188) (@lem2437941 x y n)). Qed.
Lemma lem2438190 (n : int) (x : int) (y : int) : (term118 n y x) = (term213 n x y).
Proof. exact (MK_COMB (@lem2438189 x y n) (@lem2438187 n x y)). Qed.
Lemma lem2438197 (n : int) (x : int) (y : int) : (term120 n y x) = (term213 n x y).
Proof. exact (TRANS (@lem2437856 n y x) (@lem2438190 n x y)). Qed.
Lemma lem2438211 (n : int) (x : int) (y : int) : (term210 n x y) = (term214 n x y).
Proof. exact (@lem19158 (term204 x y) (term191 n x y) (term206 x y)). Qed.
Lemma lem2438218 (n : int) (x : int) (y : int) : (term215 n x y) = (term216 n x y).
Proof. exact (@lem19367 (term173 n x y) ((term122 x y) = term95) (term206 x y)). Qed.
Lemma lem2438225 (n : int) (x : int) (y : int) : (term217 n x y) = (term218 n x y).
Proof. exact (@lem19367 (term173 n x y) ((term122 x y) = term95) (term204 x y)). Qed.
Lemma lem2438226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2438227 (n : int) (x : int) (y : int) : (term219 n x y) = (term220 n x y).
Proof. exact (MK_COMB (@lem2438226) (@lem2438225 n x y)). Qed.
Lemma lem2438228 (n : int) (x : int) (y : int) : (term214 n x y) = (term221 n x y).
Proof. exact (MK_COMB (@lem2438227 n x y) (@lem2438218 n x y)). Qed.
Lemma lem2438230 (n : int) (x : int) (y : int) : (term210 n x y) = (term221 n x y).
Proof. exact (TRANS (@lem2438211 n x y) (@lem2438228 n x y)). Qed.
Lemma lem2438233 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2438234 (n : int) (x : int) (y : int) : (term211 n x y) = (term222 n x y).
Proof. exact (MK_COMB (@lem2438233 n x y) (@lem2438230 n x y)). Qed.
Lemma lem2438235 (n : int) (x : int) (y : int) : (term222 n x y) = (term223 n x y).
Proof. exact (@lem19158 (term218 n x y) (term22 n x y) (term216 n x y)). Qed.
Lemma lem2438242 (n : int) (x : int) (y : int) : (term224 n x y) = (term225 n x y).
Proof. exact (@lem19158 (term226 n x y) (term22 n x y) (term227 x y)). Qed.
Lemma lem2438249 (n : int) (x : int) (y : int) : (term228 n x y) = (term229 n x y).
Proof. exact (@lem19158 (term230 n x y) (term22 n x y) (term231 x y)). Qed.
Lemma lem2438250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2438251 (n : int) (x : int) (y : int) : (term232 n x y) = (term233 n x y).
Proof. exact (MK_COMB (@lem2438250) (@lem2438249 n x y)). Qed.
Lemma lem2438252 (n : int) (x : int) (y : int) : (term223 n x y) = (term234 n x y).
Proof. exact (MK_COMB (@lem2438251 n x y) (@lem2438242 n x y)). Qed.
Lemma lem2438253 (n : int) (x : int) (y : int) : (term222 n x y) = (term234 n x y).
Proof. exact (TRANS (@lem2438235 n x y) (@lem2438252 n x y)). Qed.
Lemma lem2438254 (n : int) (x : int) (y : int) : (term211 n x y) = (term234 n x y).
Proof. exact (TRANS (@lem2438234 n x y) (@lem2438253 n x y)). Qed.
Lemma lem2438257 (x : int) (y : int) (n : int) : (term212 x y n) = (term212 x y n).
Proof. exact (eq_refl (term212 x y n)). Qed.
Lemma lem2438258 (n : int) (x : int) (y : int) : (term213 n x y) = (term235 n x y).
Proof. exact (MK_COMB (@lem2438257 x y n) (@lem2438254 n x y)). Qed.
Lemma lem2438259 (n : int) (x : int) (y : int) : (term235 n x y) = (term236 n x y).
Proof. exact (@lem19158 (term229 n x y) (term162 x y n) (term225 n x y)). Qed.
Lemma lem2438266 (n : int) (x : int) (y : int) : (term237 n x y) = (term238 n x y).
Proof. exact (@lem19158 (term239 n x y) (term162 x y n) (term240 n x y)). Qed.
Lemma lem2438273 (n : int) (x : int) (y : int) : (term241 n x y) = (term242 n x y).
Proof. exact (@lem19158 (term243 n x y) (term162 x y n) (term244 n x y)). Qed.
Lemma lem2438274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2438275 (n : int) (x : int) (y : int) : (term245 n x y) = (term246 n x y).
Proof. exact (MK_COMB (@lem2438274) (@lem2438273 n x y)). Qed.
Lemma lem2438276 (n : int) (x : int) (y : int) : (term236 n x y) = (term247 n x y).
Proof. exact (MK_COMB (@lem2438275 n x y) (@lem2438266 n x y)). Qed.
Lemma lem2438277 (n : int) (x : int) (y : int) : (term235 n x y) = (term247 n x y).
Proof. exact (TRANS (@lem2438259 n x y) (@lem2438276 n x y)). Qed.
Lemma lem2438278 (n : int) (x : int) (y : int) : (term213 n x y) = (term247 n x y).
Proof. exact (TRANS (@lem2438258 n x y) (@lem2438277 n x y)). Qed.
Lemma lem2438279 (n : int) (x : int) (y : int) : (term120 n y x) = (term247 n x y).
Proof. exact (TRANS (@lem2438197 n x y) (@lem2438278 n x y)). Qed.
Lemma lem2438281 (a : real) (x : real) (r : real) : (term248 x a r) = (term249 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2438282 (n : int) (x : int) (y : int) : (term162 x y n) = (term250 n x y).
Proof. exact (@lem2438281 (term251 n) (term122 x y) term95). Qed.
Lemma lem2438301 (x : int) (y : int) : (term252 x y) = (term122 x y).
Proof. exact (@lem1982733 (term122 x y)). Qed.
Lemma lem2438310 (n : int) : (term253 n) = (term253 n).
Proof. exact (eq_refl (term253 n)). Qed.
Lemma lem2438311 (n : int) (x : int) (y : int) : (term254 n x y) = (term255 n x y).
Proof. exact (MK_COMB (@lem2438310 n) (@lem2438301 x y)). Qed.
Lemma lem2438312 (n : int) (x : int) (y : int) : (term255 n x y) = (term256 n x y).
Proof. exact (@lem1982755 (real_of_int n) term132 (term122 x y)). Qed.
Lemma lem2438313 (x : int) (y : int) : (term257 x y) = (term258 x y).
Proof. exact (@lem1982757 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2438314 (y : int) : (term259 y) = (term198 y).
Proof. exact (@lem1982761 (term201 y) term132). Qed.
Lemma lem2438315 (x : int) : (term105 x) = (term105 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2438316 (x : int) (y : int) : (term258 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem2438315 x) (@lem2438314 y)). Qed.
Lemma lem2438317 (x : int) (y : int) : (term257 x y) = (term199 x y).
Proof. exact (TRANS (@lem2438313 x y) (@lem2438316 x y)). Qed.
Lemma lem2438318 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2438319 (n : int) (x : int) (y : int) : (term256 n x y) = (term260 n x y).
Proof. exact (MK_COMB (@lem2438318 n) (@lem2438317 x y)). Qed.
Lemma lem2438320 (n : int) (x : int) (y : int) : (term255 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2438312 n x y) (@lem2438319 n x y)). Qed.
Lemma lem2438321 (n : int) (x : int) (y : int) : (term254 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2438311 n x y) (@lem2438320 n x y)). Qed.
Lemma lem2438322 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438323 (n : int) (x : int) (y : int) : (term261 n x y) = (term262 n x y).
Proof. exact (MK_COMB (@lem2438322) (@lem2438321 n x y)). Qed.
Lemma lem2438324 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438325 (n : int) (x : int) (y : int) : (term263 n x y) = (term264 n x y).
Proof. exact (MK_COMB (@lem2438323 n x y) (@lem2438324)). Qed.
Lemma lem2438343 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2438344 (y : int) : (term267 y) = (term268 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2438346 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438347 : term132 = term137.
Proof. exact (@lem2438346 term81). Qed.
Lemma lem2438349 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438350 : term132 = term137.
Proof. exact (@lem2438349 term81). Qed.
Lemma lem2438351 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438352 : term138 = term139.
Proof. exact (MK_COMB (@lem2438351) (@lem2438350)). Qed.
Lemma lem2438353 : term269 = term270.
Proof. exact (MK_COMB (@lem2438352) (@lem2438347)). Qed.
Lemma lem2438354 : term270 = term271.
Proof. exact (@lem1981613 term132 term132 term80 term80). Qed.
Lemma lem2438356 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438357 : term145 = term146.
Proof. exact (@lem2438356 term81 term81). Qed.
Lemma lem2438358 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438359 : term148 = term81.
Proof. exact (EQ_MP (@lem2438358) (@lem940073)). Qed.
Lemma lem2438360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438361 : term146 = term80.
Proof. exact (MK_COMB (@lem2438360) (@lem2438359)). Qed.
Lemma lem2438362 : term145 = term80.
Proof. exact (TRANS (@lem2438357) (@lem2438361)). Qed.
Lemma lem2438364 (m : nat) (n : nat) : (term272 m n) = (term144 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2438365 : term269 = term146.
Proof. exact (@lem2438364 term81 term81). Qed.
Lemma lem2438366 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438367 : term148 = term81.
Proof. exact (EQ_MP (@lem2438366) (@lem940073)). Qed.
Lemma lem2438368 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438369 : term146 = term80.
Proof. exact (MK_COMB (@lem2438368) (@lem2438367)). Qed.
Lemma lem2438370 : term269 = term80.
Proof. exact (TRANS (@lem2438365) (@lem2438369)). Qed.
Lemma lem2438371 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438372 : term273 = term274.
Proof. exact (MK_COMB (@lem2438371) (@lem2438370)). Qed.
Lemma lem2438373 : term271 = term134.
Proof. exact (MK_COMB (@lem2438372) (@lem2438362)). Qed.
Lemma lem2438374 : term270 = term134.
Proof. exact (TRANS (@lem2438354) (@lem2438373)). Qed.
Lemma lem2438375 : term269 = term134.
Proof. exact (TRANS (@lem2438353) (@lem2438374)). Qed.
Lemma lem2438377 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438378 : term134 = term80.
Proof. exact (@lem2438377 term80). Qed.
Lemma lem2438379 : term269 = term80.
Proof. exact (TRANS (@lem2438375) (@lem2438378)). Qed.
Lemma lem2438380 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438381 : term275 = term276.
Proof. exact (MK_COMB (@lem2438380) (@lem2438379)). Qed.
Lemma lem2438382 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2438383 (y : int) : (term268 y) = (term277 y).
Proof. exact (MK_COMB (@lem2438381) (@lem2438382 y)). Qed.
Lemma lem2438384 (y : int) : (term267 y) = (term277 y).
Proof. exact (TRANS (@lem2438344 y) (@lem2438383 y)). Qed.
Lemma lem2438385 (y : int) : (term277 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2438386 (y : int) : (term267 y) = (real_of_int y).
Proof. exact (TRANS (@lem2438384 y) (@lem2438385 y)). Qed.
Lemma lem2438389 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2438390 (x : int) (y : int) : (term266 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem2438389 x) (@lem2438386 y)). Qed.
Lemma lem2438392 (x : int) (y : int) : (term265 x y) = (term278 x y).
Proof. exact (TRANS (@lem2438343 x y) (@lem2438390 x y)). Qed.
Lemma lem2438401 (n : int) : (term253 n) = (term253 n).
Proof. exact (eq_refl (term253 n)). Qed.
Lemma lem2438402 (n : int) (x : int) (y : int) : (term279 n x y) = (term280 n x y).
Proof. exact (MK_COMB (@lem2438401 n) (@lem2438392 x y)). Qed.
Lemma lem2438403 (n : int) (x : int) (y : int) : (term280 n x y) = (term281 n x y).
Proof. exact (@lem1982755 (real_of_int n) term132 (term278 x y)). Qed.
Lemma lem2438404 (x : int) (y : int) : (term282 x y) = (term283 x y).
Proof. exact (@lem1982757 (term201 x) term132 (real_of_int y)). Qed.
Lemma lem2438405 (y : int) : (term284 y) = (term251 y).
Proof. exact (@lem1982761 (real_of_int y) term132). Qed.
Lemma lem2438406 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2438407 (x : int) (y : int) : (term283 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem2438406 x) (@lem2438405 y)). Qed.
Lemma lem2438408 (x : int) (y : int) : (term282 x y) = (term200 x y).
Proof. exact (TRANS (@lem2438404 x y) (@lem2438407 x y)). Qed.
Lemma lem2438409 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2438410 (n : int) (x : int) (y : int) : (term281 n x y) = (term285 n x y).
Proof. exact (MK_COMB (@lem2438409 n) (@lem2438408 x y)). Qed.
Lemma lem2438411 (n : int) (x : int) (y : int) : (term280 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2438403 n x y) (@lem2438410 n x y)). Qed.
Lemma lem2438412 (n : int) (x : int) (y : int) : (term279 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2438402 n x y) (@lem2438411 n x y)). Qed.
Lemma lem2438413 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438414 (n : int) (x : int) (y : int) : (term286 n x y) = (term287 n x y).
Proof. exact (MK_COMB (@lem2438413) (@lem2438412 n x y)). Qed.
Lemma lem2438415 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438416 (n : int) (x : int) (y : int) : (term288 n x y) = (term289 n x y).
Proof. exact (MK_COMB (@lem2438414 n x y) (@lem2438415)). Qed.
Lemma lem2438417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438418 (n : int) (x : int) (y : int) : (term290 n x y) = (term291 n x y).
Proof. exact (MK_COMB (@lem2438417) (@lem2438416 n x y)). Qed.
Lemma lem2438419 (n : int) (x : int) (y : int) : (term250 n x y) = (term292 n x y).
Proof. exact (MK_COMB (@lem2438418 n x y) (@lem2438325 n x y)). Qed.
Lemma lem2438420 (n : int) (x : int) (y : int) : (term162 x y n) = (term292 n x y).
Proof. exact (TRANS (@lem2438282 n x y) (@lem2438419 n x y)). Qed.
Lemma lem2438421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438422 (n : int) (x : int) (y : int) : (term212 x y n) = (term293 n x y).
Proof. exact (MK_COMB (@lem2438421) (@lem2438420 n x y)). Qed.
Lemma lem2438424 (a : real) (x : real) (r : real) : (term248 x a r) = (term249 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2438425 (x : int) (y : int) (n : int) : (term173 n x y) = (term294 x y n).
Proof. exact (@lem2438424 (term123 x y) (real_of_int n) term95). Qed.
Lemma lem2438432 (n : int) : (term277 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2438449 (x : int) (y : int) : (term124 x y) = (term124 x y).
Proof. exact (eq_refl (term124 x y)). Qed.
Lemma lem2438452 (x : int) (y : int) (n : int) : (term295 x y n) = (term296 x y n).
Proof. exact (MK_COMB (@lem2438449 x y) (@lem2438432 n)). Qed.
Lemma lem2438453 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438454 (x : int) (y : int) (n : int) : (term297 x y n) = (term298 x y n).
Proof. exact (MK_COMB (@lem2438453) (@lem2438452 x y n)). Qed.
Lemma lem2438455 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438456 (x : int) (y : int) (n : int) : (term299 x y n) = (term300 x y n).
Proof. exact (MK_COMB (@lem2438454 x y n) (@lem2438455)). Qed.
Lemma lem2438489 (x : int) (y : int) (n : int) : (term301 x y n) = (term301 x y n).
Proof. exact (eq_refl (term301 x y n)). Qed.
Lemma lem2438490 (x : int) (y : int) (n : int) : (term294 x y n) = (term302 x y n).
Proof. exact (MK_COMB (@lem2438489 x y n) (@lem2438456 x y n)). Qed.
Lemma lem2438491 (x : int) (y : int) (n : int) : (term173 n x y) = (term302 x y n).
Proof. exact (TRANS (@lem2438425 x y n) (@lem2438490 x y n)). Qed.
Lemma lem2438492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438493 (x : int) (y : int) (n : int) : (term303 n x y) = (term304 x y n).
Proof. exact (MK_COMB (@lem2438492) (@lem2438491 x y n)). Qed.
Lemma lem2438494 (x : int) (y : int) : (term204 x y) = (term204 x y).
Proof. exact (eq_refl (term204 x y)). Qed.
Lemma lem2438495 (n : int) (x : int) (y : int) : (term230 n x y) = (term305 n x y).
Proof. exact (MK_COMB (@lem2438493 x y n) (@lem2438494 x y)). Qed.
Lemma lem2438496 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2438497 (n : int) (x : int) (y : int) : (term243 n x y) = (term306 n x y).
Proof. exact (MK_COMB (@lem2438496 n x y) (@lem2438495 n x y)). Qed.
Lemma lem2438498 (n : int) (x : int) (y : int) : (term307 n x y) = (term308 n x y).
Proof. exact (MK_COMB (@lem2438422 n x y) (@lem2438497 n x y)). Qed.
Lemma lem2438499 (n : int) (x : int) (y : int) : (term309 n x y) = (term308 n x y).
Proof. exact (eq_refl (term309 n x y)). Qed.
Lemma lem2438500 (n : int) (x : int) (y : int) : (term308 n x y) = (term309 n x y).
Proof. exact (SYM (@lem2438499 n x y)). Qed.
Lemma lem2438501 (n : int) (x : int) (y : int) : (term309 n x y) = (term310 n x y).
Proof. exact (@lem1482981 (term311 n x y) (term122 x y)). Qed.
Lemma lem2438502 (n : int) (x : int) (y : int) : (term308 n x y) = (term310 n x y).
Proof. exact (TRANS (@lem2438500 n x y) (@lem2438501 n x y)). Qed.
Lemma lem2438503 (n : int) (x : int) (y : int) : (term312 n x y) = (term313 n x y).
Proof. exact (eq_refl (term312 n x y)). Qed.
Lemma lem2438504 (x : int) (y : int) : (term314 x y) = (term314 x y).
Proof. exact (eq_refl (term314 x y)). Qed.
Lemma lem2438505 (n : int) (x : int) (y : int) : (term315 n x y) = (term316 n x y).
Proof. exact (MK_COMB (@lem2438504 x y) (@lem2438503 n x y)). Qed.
Lemma lem2438506 (n : int) (x : int) (y : int) : (term317 n x y) = (term318 n x y).
Proof. exact (eq_refl (term317 n x y)). Qed.
Lemma lem2438507 (x : int) (y : int) : (term319 x y) = (term319 x y).
Proof. exact (eq_refl (term319 x y)). Qed.
Lemma lem2438508 (n : int) (x : int) (y : int) : (term320 n x y) = (term321 n x y).
Proof. exact (MK_COMB (@lem2438507 x y) (@lem2438506 n x y)). Qed.
Lemma lem2438509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2438510 (n : int) (x : int) (y : int) : (term322 n x y) = (term323 n x y).
Proof. exact (MK_COMB (@lem2438509) (@lem2438508 n x y)). Qed.
Lemma lem2438511 (n : int) (x : int) (y : int) : (term310 n x y) = (term324 n x y).
Proof. exact (MK_COMB (@lem2438510 n x y) (@lem2438505 n x y)). Qed.
Lemma lem2438512 (n : int) (x : int) (y : int) : (term325 n x y) = (term325 n x y).
Proof. exact (eq_refl (term325 n x y)). Qed.
Lemma lem2438513 (n : int) (x : int) (y : int) : ((term308 n x y) = (term310 n x y)) = ((term308 n x y) = (term324 n x y)).
Proof. exact (MK_COMB (@lem2438512 n x y) (@lem2438511 n x y)). Qed.
Lemma lem2438514 (n : int) (x : int) (y : int) : (term308 n x y) = (term324 n x y).
Proof. exact (EQ_MP (@lem2438513 n x y) (@lem2438502 n x y)). Qed.
Lemma lem2438515 (x : int) (y : int) : (term326 x y) = (term327 x y).
Proof. exact (@lem1988291 (term122 x y) term95). Qed.
Lemma lem2438533 (x : int) (y : int) : (term177 x y) = (term178 x y).
Proof. exact (@lem1982792 (term122 x y) term95). Qed.
Lemma lem2438535 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2438536 : term95 = term179.
Proof. exact (@lem2438535 (NUMERAL 0)). Qed.
Lemma lem2438538 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438539 : term132 = term137.
Proof. exact (@lem2438538 term81). Qed.
Lemma lem2438540 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438541 : term138 = term139.
Proof. exact (MK_COMB (@lem2438540) (@lem2438539)). Qed.
Lemma lem2438542 : term180 = term181.
Proof. exact (MK_COMB (@lem2438541) (@lem2438536)). Qed.
Lemma lem2438543 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2438545 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438546 : term145 = term146.
Proof. exact (@lem2438545 term81 term81). Qed.
Lemma lem2438547 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438548 : term148 = term81.
Proof. exact (EQ_MP (@lem2438547) (@lem940073)). Qed.
Lemma lem2438549 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438550 : term146 = term80.
Proof. exact (MK_COMB (@lem2438549) (@lem2438548)). Qed.
Lemma lem2438551 : term145 = term80.
Proof. exact (TRANS (@lem2438546) (@lem2438550)). Qed.
Lemma lem2438553 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2438554 : term180 = term95.
Proof. exact (@lem2438553 term81). Qed.
Lemma lem2438555 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438556 : term184 = term185.
Proof. exact (MK_COMB (@lem2438555) (@lem2438554)). Qed.
Lemma lem2438557 : term182 = term179.
Proof. exact (MK_COMB (@lem2438556) (@lem2438551)). Qed.
Lemma lem2438558 : term181 = term179.
Proof. exact (TRANS (@lem2438543) (@lem2438557)). Qed.
Lemma lem2438559 : term180 = term179.
Proof. exact (TRANS (@lem2438542) (@lem2438558)). Qed.
Lemma lem2438561 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438562 : term179 = term95.
Proof. exact (@lem2438561 term95). Qed.
Lemma lem2438563 : term180 = term95.
Proof. exact (TRANS (@lem2438559) (@lem2438562)). Qed.
Lemma lem2438564 (x : int) (y : int) : (term186 x y) = (term186 x y).
Proof. exact (eq_refl (term186 x y)). Qed.
Lemma lem2438565 (x : int) (y : int) : (term178 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem2438564 x y) (@lem2438563)). Qed.
Lemma lem2438566 (x : int) (y : int) : (term187 x y) = (term122 x y).
Proof. exact (@lem1982723 (term122 x y)). Qed.
Lemma lem2438567 (x : int) (y : int) : (term178 x y) = (term122 x y).
Proof. exact (TRANS (@lem2438565 x y) (@lem2438566 x y)). Qed.
Lemma lem2438569 (x : int) (y : int) : (term177 x y) = (term122 x y).
Proof. exact (TRANS (@lem2438533 x y) (@lem2438567 x y)). Qed.
Lemma lem2438570 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438571 (x : int) (y : int) : (term328 x y) = (term329 x y).
Proof. exact (MK_COMB (@lem2438570) (@lem2438569 x y)). Qed.
Lemma lem2438572 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438573 (x : int) (y : int) : (term327 x y) = (term326 x y).
Proof. exact (MK_COMB (@lem2438571 x y) (@lem2438572)). Qed.
Lemma lem2438574 (x : int) (y : int) : (term326 x y) = (term326 x y).
Proof. exact (TRANS (@lem2438515 x y) (@lem2438573 x y)). Qed.
Lemma lem2438575 (n : int) (x : int) (y : int) : (term289 n x y) = (term330 n x y).
Proof. exact (@lem1988291 (term285 n x y) term95). Qed.
Lemma lem2438605 (n : int) (x : int) (y : int) : (term331 n x y) = (term332 n x y).
Proof. exact (@lem1982792 (term285 n x y) term95). Qed.
Lemma lem2438607 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2438608 : term95 = term179.
Proof. exact (@lem2438607 (NUMERAL 0)). Qed.
Lemma lem2438610 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438611 : term132 = term137.
Proof. exact (@lem2438610 term81). Qed.
Lemma lem2438612 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438613 : term138 = term139.
Proof. exact (MK_COMB (@lem2438612) (@lem2438611)). Qed.
Lemma lem2438614 : term180 = term181.
Proof. exact (MK_COMB (@lem2438613) (@lem2438608)). Qed.
Lemma lem2438615 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2438617 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438618 : term145 = term146.
Proof. exact (@lem2438617 term81 term81). Qed.
Lemma lem2438619 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438620 : term148 = term81.
Proof. exact (EQ_MP (@lem2438619) (@lem940073)). Qed.
Lemma lem2438621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438622 : term146 = term80.
Proof. exact (MK_COMB (@lem2438621) (@lem2438620)). Qed.
Lemma lem2438623 : term145 = term80.
Proof. exact (TRANS (@lem2438618) (@lem2438622)). Qed.
Lemma lem2438625 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2438626 : term180 = term95.
Proof. exact (@lem2438625 term81). Qed.
Lemma lem2438627 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438628 : term184 = term185.
Proof. exact (MK_COMB (@lem2438627) (@lem2438626)). Qed.
Lemma lem2438629 : term182 = term179.
Proof. exact (MK_COMB (@lem2438628) (@lem2438623)). Qed.
Lemma lem2438630 : term181 = term179.
Proof. exact (TRANS (@lem2438615) (@lem2438629)). Qed.
Lemma lem2438631 : term180 = term179.
Proof. exact (TRANS (@lem2438614) (@lem2438630)). Qed.
Lemma lem2438633 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438634 : term179 = term95.
Proof. exact (@lem2438633 term95). Qed.
Lemma lem2438635 : term180 = term95.
Proof. exact (TRANS (@lem2438631) (@lem2438634)). Qed.
Lemma lem2438636 (n : int) (x : int) (y : int) : (term333 n x y) = (term333 n x y).
Proof. exact (eq_refl (term333 n x y)). Qed.
Lemma lem2438637 (n : int) (x : int) (y : int) : (term332 n x y) = (term334 n x y).
Proof. exact (MK_COMB (@lem2438636 n x y) (@lem2438635)). Qed.
Lemma lem2438638 (n : int) (x : int) (y : int) : (term334 n x y) = (term285 n x y).
Proof. exact (@lem1982723 (term285 n x y)). Qed.
Lemma lem2438639 (n : int) (x : int) (y : int) : (term332 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2438637 n x y) (@lem2438638 n x y)). Qed.
Lemma lem2438641 (n : int) (x : int) (y : int) : (term331 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2438605 n x y) (@lem2438639 n x y)). Qed.
Lemma lem2438642 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438643 (n : int) (x : int) (y : int) : (term335 n x y) = (term287 n x y).
Proof. exact (MK_COMB (@lem2438642) (@lem2438641 n x y)). Qed.
Lemma lem2438644 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438645 (n : int) (x : int) (y : int) : (term330 n x y) = (term289 n x y).
Proof. exact (MK_COMB (@lem2438643 n x y) (@lem2438644)). Qed.
Lemma lem2438646 (n : int) (x : int) (y : int) : (term289 n x y) = (term289 n x y).
Proof. exact (TRANS (@lem2438575 n x y) (@lem2438645 n x y)). Qed.
Lemma lem2438647 (n : int) (x : int) (y : int) : (term264 n x y) = (term336 n x y).
Proof. exact (@lem1988291 (term260 n x y) term95). Qed.
Lemma lem2438677 (n : int) (x : int) (y : int) : (term337 n x y) = (term338 n x y).
Proof. exact (@lem1982792 (term260 n x y) term95). Qed.
Lemma lem2438679 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2438680 : term95 = term179.
Proof. exact (@lem2438679 (NUMERAL 0)). Qed.
Lemma lem2438682 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438683 : term132 = term137.
Proof. exact (@lem2438682 term81). Qed.
Lemma lem2438684 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438685 : term138 = term139.
Proof. exact (MK_COMB (@lem2438684) (@lem2438683)). Qed.
Lemma lem2438686 : term180 = term181.
Proof. exact (MK_COMB (@lem2438685) (@lem2438680)). Qed.
Lemma lem2438687 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2438689 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438690 : term145 = term146.
Proof. exact (@lem2438689 term81 term81). Qed.
Lemma lem2438691 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438692 : term148 = term81.
Proof. exact (EQ_MP (@lem2438691) (@lem940073)). Qed.
Lemma lem2438693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438694 : term146 = term80.
Proof. exact (MK_COMB (@lem2438693) (@lem2438692)). Qed.
Lemma lem2438695 : term145 = term80.
Proof. exact (TRANS (@lem2438690) (@lem2438694)). Qed.
Lemma lem2438697 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2438698 : term180 = term95.
Proof. exact (@lem2438697 term81). Qed.
Lemma lem2438699 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438700 : term184 = term185.
Proof. exact (MK_COMB (@lem2438699) (@lem2438698)). Qed.
Lemma lem2438701 : term182 = term179.
Proof. exact (MK_COMB (@lem2438700) (@lem2438695)). Qed.
Lemma lem2438702 : term181 = term179.
Proof. exact (TRANS (@lem2438687) (@lem2438701)). Qed.
Lemma lem2438703 : term180 = term179.
Proof. exact (TRANS (@lem2438686) (@lem2438702)). Qed.
Lemma lem2438705 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438706 : term179 = term95.
Proof. exact (@lem2438705 term95). Qed.
Lemma lem2438707 : term180 = term95.
Proof. exact (TRANS (@lem2438703) (@lem2438706)). Qed.
Lemma lem2438708 (n : int) (x : int) (y : int) : (term339 n x y) = (term339 n x y).
Proof. exact (eq_refl (term339 n x y)). Qed.
Lemma lem2438709 (n : int) (x : int) (y : int) : (term338 n x y) = (term340 n x y).
Proof. exact (MK_COMB (@lem2438708 n x y) (@lem2438707)). Qed.
Lemma lem2438710 (n : int) (x : int) (y : int) : (term340 n x y) = (term260 n x y).
Proof. exact (@lem1982723 (term260 n x y)). Qed.
Lemma lem2438711 (n : int) (x : int) (y : int) : (term338 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2438709 n x y) (@lem2438710 n x y)). Qed.
Lemma lem2438713 (n : int) (x : int) (y : int) : (term337 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2438677 n x y) (@lem2438711 n x y)). Qed.
Lemma lem2438714 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438715 (n : int) (x : int) (y : int) : (term341 n x y) = (term262 n x y).
Proof. exact (MK_COMB (@lem2438714) (@lem2438713 n x y)). Qed.
Lemma lem2438716 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438717 (n : int) (x : int) (y : int) : (term336 n x y) = (term264 n x y).
Proof. exact (MK_COMB (@lem2438715 n x y) (@lem2438716)). Qed.
Lemma lem2438718 (n : int) (x : int) (y : int) : (term264 n x y) = (term264 n x y).
Proof. exact (TRANS (@lem2438647 n x y) (@lem2438717 n x y)). Qed.
Lemma lem2438719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438720 (n : int) (x : int) (y : int) : (term291 n x y) = (term291 n x y).
Proof. exact (MK_COMB (@lem2438719) (@lem2438646 n x y)). Qed.
Lemma lem2438721 (n : int) (x : int) (y : int) : (term292 n x y) = (term292 n x y).
Proof. exact (MK_COMB (@lem2438720 n x y) (@lem2438718 n x y)). Qed.
Lemma lem2438723 (x : int) (y : int) (n : int) : (term342 x y n) = (term343 x y n).
Proof. exact (@lem1988291 (term344 x y n) term95). Qed.
Lemma lem2438724 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438749 (n : int) (x : int) (y : int) : (term344 x y n) = (term345 n x y).
Proof. exact (@lem1982761 (term201 n) (term122 x y)). Qed.
Lemma lem2438750 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2438751 (n : int) (x : int) (y : int) : (term346 x y n) = (term347 n x y).
Proof. exact (MK_COMB (@lem2438750) (@lem2438749 n x y)). Qed.
Lemma lem2438752 (n : int) (x : int) (y : int) : (term348 x y n) = (term349 n x y).
Proof. exact (MK_COMB (@lem2438751 n x y) (@lem2438724)). Qed.
Lemma lem2438753 (n : int) (x : int) (y : int) : (term349 n x y) = (term350 n x y).
Proof. exact (@lem1982792 (term345 n x y) term95). Qed.
Lemma lem2438755 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2438756 : term95 = term179.
Proof. exact (@lem2438755 (NUMERAL 0)). Qed.
Lemma lem2438758 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438759 : term132 = term137.
Proof. exact (@lem2438758 term81). Qed.
Lemma lem2438760 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438761 : term138 = term139.
Proof. exact (MK_COMB (@lem2438760) (@lem2438759)). Qed.
Lemma lem2438762 : term180 = term181.
Proof. exact (MK_COMB (@lem2438761) (@lem2438756)). Qed.
Lemma lem2438763 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2438765 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438766 : term145 = term146.
Proof. exact (@lem2438765 term81 term81). Qed.
Lemma lem2438767 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438768 : term148 = term81.
Proof. exact (EQ_MP (@lem2438767) (@lem940073)). Qed.
Lemma lem2438769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438770 : term146 = term80.
Proof. exact (MK_COMB (@lem2438769) (@lem2438768)). Qed.
Lemma lem2438771 : term145 = term80.
Proof. exact (TRANS (@lem2438766) (@lem2438770)). Qed.
Lemma lem2438773 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2438774 : term180 = term95.
Proof. exact (@lem2438773 term81). Qed.
Lemma lem2438775 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438776 : term184 = term185.
Proof. exact (MK_COMB (@lem2438775) (@lem2438774)). Qed.
Lemma lem2438777 : term182 = term179.
Proof. exact (MK_COMB (@lem2438776) (@lem2438771)). Qed.
Lemma lem2438778 : term181 = term179.
Proof. exact (TRANS (@lem2438763) (@lem2438777)). Qed.
Lemma lem2438779 : term180 = term179.
Proof. exact (TRANS (@lem2438762) (@lem2438778)). Qed.
Lemma lem2438781 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438782 : term179 = term95.
Proof. exact (@lem2438781 term95). Qed.
Lemma lem2438783 : term180 = term95.
Proof. exact (TRANS (@lem2438779) (@lem2438782)). Qed.
Lemma lem2438784 (n : int) (x : int) (y : int) : (term351 n x y) = (term351 n x y).
Proof. exact (eq_refl (term351 n x y)). Qed.
Lemma lem2438785 (n : int) (x : int) (y : int) : (term350 n x y) = (term352 n x y).
Proof. exact (MK_COMB (@lem2438784 n x y) (@lem2438783)). Qed.
Lemma lem2438786 (n : int) (x : int) (y : int) : (term352 n x y) = (term345 n x y).
Proof. exact (@lem1982723 (term345 n x y)). Qed.
Lemma lem2438787 (n : int) (x : int) (y : int) : (term350 n x y) = (term345 n x y).
Proof. exact (TRANS (@lem2438785 n x y) (@lem2438786 n x y)). Qed.
Lemma lem2438788 (n : int) (x : int) (y : int) : (term349 n x y) = (term345 n x y).
Proof. exact (TRANS (@lem2438753 n x y) (@lem2438787 n x y)). Qed.
Lemma lem2438789 (n : int) (x : int) (y : int) : (term348 x y n) = (term345 n x y).
Proof. exact (TRANS (@lem2438752 n x y) (@lem2438788 n x y)). Qed.
Lemma lem2438790 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438791 (n : int) (x : int) (y : int) : (term353 x y n) = (term354 n x y).
Proof. exact (MK_COMB (@lem2438790) (@lem2438789 n x y)). Qed.
Lemma lem2438792 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438793 (n : int) (x : int) (y : int) : (term343 x y n) = (term355 n x y).
Proof. exact (MK_COMB (@lem2438791 n x y) (@lem2438792)). Qed.
Lemma lem2438794 (n : int) (x : int) (y : int) : (term342 x y n) = (term355 n x y).
Proof. exact (TRANS (@lem2438723 x y n) (@lem2438793 n x y)). Qed.
Lemma lem2438795 (x : int) (y : int) (n : int) : (term356 x y n) = (term357 x y n).
Proof. exact (@lem1988291 (term358 x y n) term95). Qed.
Lemma lem2438796 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438815 (n : int) (x : int) (y : int) : (term358 x y n) = (term359 n x y).
Proof. exact (@lem1982761 (real_of_int n) (term122 x y)). Qed.
Lemma lem2438816 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2438817 (n : int) (x : int) (y : int) : (term360 x y n) = (term361 n x y).
Proof. exact (MK_COMB (@lem2438816) (@lem2438815 n x y)). Qed.
Lemma lem2438818 (n : int) (x : int) (y : int) : (term362 x y n) = (term363 n x y).
Proof. exact (MK_COMB (@lem2438817 n x y) (@lem2438796)). Qed.
Lemma lem2438819 (n : int) (x : int) (y : int) : (term363 n x y) = (term364 n x y).
Proof. exact (@lem1982792 (term359 n x y) term95). Qed.
Lemma lem2438821 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2438822 : term95 = term179.
Proof. exact (@lem2438821 (NUMERAL 0)). Qed.
Lemma lem2438824 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438825 : term132 = term137.
Proof. exact (@lem2438824 term81). Qed.
Lemma lem2438826 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438827 : term138 = term139.
Proof. exact (MK_COMB (@lem2438826) (@lem2438825)). Qed.
Lemma lem2438828 : term180 = term181.
Proof. exact (MK_COMB (@lem2438827) (@lem2438822)). Qed.
Lemma lem2438829 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2438831 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438832 : term145 = term146.
Proof. exact (@lem2438831 term81 term81). Qed.
Lemma lem2438833 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438834 : term148 = term81.
Proof. exact (EQ_MP (@lem2438833) (@lem940073)). Qed.
Lemma lem2438835 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438836 : term146 = term80.
Proof. exact (MK_COMB (@lem2438835) (@lem2438834)). Qed.
Lemma lem2438837 : term145 = term80.
Proof. exact (TRANS (@lem2438832) (@lem2438836)). Qed.
Lemma lem2438839 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2438840 : term180 = term95.
Proof. exact (@lem2438839 term81). Qed.
Lemma lem2438841 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438842 : term184 = term185.
Proof. exact (MK_COMB (@lem2438841) (@lem2438840)). Qed.
Lemma lem2438843 : term182 = term179.
Proof. exact (MK_COMB (@lem2438842) (@lem2438837)). Qed.
Lemma lem2438844 : term181 = term179.
Proof. exact (TRANS (@lem2438829) (@lem2438843)). Qed.
Lemma lem2438845 : term180 = term179.
Proof. exact (TRANS (@lem2438828) (@lem2438844)). Qed.
Lemma lem2438847 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438848 : term179 = term95.
Proof. exact (@lem2438847 term95). Qed.
Lemma lem2438849 : term180 = term95.
Proof. exact (TRANS (@lem2438845) (@lem2438848)). Qed.
Lemma lem2438850 (n : int) (x : int) (y : int) : (term365 n x y) = (term365 n x y).
Proof. exact (eq_refl (term365 n x y)). Qed.
Lemma lem2438851 (n : int) (x : int) (y : int) : (term364 n x y) = (term366 n x y).
Proof. exact (MK_COMB (@lem2438850 n x y) (@lem2438849)). Qed.
Lemma lem2438852 (n : int) (x : int) (y : int) : (term366 n x y) = (term359 n x y).
Proof. exact (@lem1982723 (term359 n x y)). Qed.
Lemma lem2438853 (n : int) (x : int) (y : int) : (term364 n x y) = (term359 n x y).
Proof. exact (TRANS (@lem2438851 n x y) (@lem2438852 n x y)). Qed.
Lemma lem2438854 (n : int) (x : int) (y : int) : (term363 n x y) = (term359 n x y).
Proof. exact (TRANS (@lem2438819 n x y) (@lem2438853 n x y)). Qed.
Lemma lem2438855 (n : int) (x : int) (y : int) : (term362 x y n) = (term359 n x y).
Proof. exact (TRANS (@lem2438818 n x y) (@lem2438854 n x y)). Qed.
Lemma lem2438856 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438857 (n : int) (x : int) (y : int) : (term367 x y n) = (term368 n x y).
Proof. exact (MK_COMB (@lem2438856) (@lem2438855 n x y)). Qed.
Lemma lem2438858 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438859 (n : int) (x : int) (y : int) : (term357 x y n) = (term369 n x y).
Proof. exact (MK_COMB (@lem2438857 n x y) (@lem2438858)). Qed.
Lemma lem2438860 (n : int) (x : int) (y : int) : (term356 x y n) = (term369 n x y).
Proof. exact (TRANS (@lem2438795 x y n) (@lem2438859 n x y)). Qed.
Lemma lem2438861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438862 (n : int) (x : int) (y : int) : (term370 x y n) = (term371 n x y).
Proof. exact (MK_COMB (@lem2438861) (@lem2438794 n x y)). Qed.
Lemma lem2438863 (n : int) (x : int) (y : int) : (term372 x y n) = (term373 n x y).
Proof. exact (MK_COMB (@lem2438862 n x y) (@lem2438860 n x y)). Qed.
Lemma lem2438864 (x : int) (y : int) : (term204 x y) = (term374 x y).
Proof. exact (@lem1988291 (term200 x y) term95). Qed.
Lemma lem2438888 (x : int) (y : int) : (term375 x y) = (term376 x y).
Proof. exact (@lem1982792 (term200 x y) term95). Qed.
Lemma lem2438890 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2438891 : term95 = term179.
Proof. exact (@lem2438890 (NUMERAL 0)). Qed.
Lemma lem2438893 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438894 : term132 = term137.
Proof. exact (@lem2438893 term81). Qed.
Lemma lem2438895 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438896 : term138 = term139.
Proof. exact (MK_COMB (@lem2438895) (@lem2438894)). Qed.
Lemma lem2438897 : term180 = term181.
Proof. exact (MK_COMB (@lem2438896) (@lem2438891)). Qed.
Lemma lem2438898 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2438900 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438901 : term145 = term146.
Proof. exact (@lem2438900 term81 term81). Qed.
Lemma lem2438902 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438903 : term148 = term81.
Proof. exact (EQ_MP (@lem2438902) (@lem940073)). Qed.
Lemma lem2438904 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438905 : term146 = term80.
Proof. exact (MK_COMB (@lem2438904) (@lem2438903)). Qed.
Lemma lem2438906 : term145 = term80.
Proof. exact (TRANS (@lem2438901) (@lem2438905)). Qed.
Lemma lem2438908 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2438909 : term180 = term95.
Proof. exact (@lem2438908 term81). Qed.
Lemma lem2438910 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438911 : term184 = term185.
Proof. exact (MK_COMB (@lem2438910) (@lem2438909)). Qed.
Lemma lem2438912 : term182 = term179.
Proof. exact (MK_COMB (@lem2438911) (@lem2438906)). Qed.
Lemma lem2438913 : term181 = term179.
Proof. exact (TRANS (@lem2438898) (@lem2438912)). Qed.
Lemma lem2438914 : term180 = term179.
Proof. exact (TRANS (@lem2438897) (@lem2438913)). Qed.
Lemma lem2438916 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438917 : term179 = term95.
Proof. exact (@lem2438916 term95). Qed.
Lemma lem2438918 : term180 = term95.
Proof. exact (TRANS (@lem2438914) (@lem2438917)). Qed.
Lemma lem2438919 (x : int) (y : int) : (term377 x y) = (term377 x y).
Proof. exact (eq_refl (term377 x y)). Qed.
Lemma lem2438920 (x : int) (y : int) : (term376 x y) = (term378 x y).
Proof. exact (MK_COMB (@lem2438919 x y) (@lem2438918)). Qed.
Lemma lem2438921 (x : int) (y : int) : (term378 x y) = (term200 x y).
Proof. exact (@lem1982723 (term200 x y)). Qed.
Lemma lem2438922 (x : int) (y : int) : (term376 x y) = (term200 x y).
Proof. exact (TRANS (@lem2438920 x y) (@lem2438921 x y)). Qed.
Lemma lem2438924 (x : int) (y : int) : (term375 x y) = (term200 x y).
Proof. exact (TRANS (@lem2438888 x y) (@lem2438922 x y)). Qed.
Lemma lem2438925 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2438926 (x : int) (y : int) : (term379 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem2438925) (@lem2438924 x y)). Qed.
Lemma lem2438927 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2438928 (x : int) (y : int) : (term374 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem2438926 x y) (@lem2438927)). Qed.
Lemma lem2438929 (x : int) (y : int) : (term204 x y) = (term204 x y).
Proof. exact (TRANS (@lem2438864 x y) (@lem2438928 x y)). Qed.
Lemma lem2438930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438931 (n : int) (x : int) (y : int) : (term380 x y n) = (term381 n x y).
Proof. exact (MK_COMB (@lem2438930) (@lem2438863 n x y)). Qed.
Lemma lem2438932 (n : int) (x : int) (y : int) : (term382 n x y) = (term383 n x y).
Proof. exact (MK_COMB (@lem2438931 n x y) (@lem2438929 x y)). Qed.
Lemma lem2438934 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2438935 (n : int) (x : int) (y : int) : (term384 n x y) = (term385 n x y).
Proof. exact (MK_COMB (@lem2438934 n x y) (@lem2438932 n x y)). Qed.
Lemma lem2438936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438937 (n : int) (x : int) (y : int) : (term293 n x y) = (term293 n x y).
Proof. exact (MK_COMB (@lem2438936) (@lem2438721 n x y)). Qed.
Lemma lem2438938 (n : int) (x : int) (y : int) : (term318 n x y) = (term386 n x y).
Proof. exact (MK_COMB (@lem2438937 n x y) (@lem2438935 n x y)). Qed.
Lemma lem2438939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2438940 (x : int) (y : int) : (term319 x y) = (term319 x y).
Proof. exact (MK_COMB (@lem2438939) (@lem2438574 x y)). Qed.
Lemma lem2438941 (n : int) (x : int) (y : int) : (term321 n x y) = (term387 n x y).
Proof. exact (MK_COMB (@lem2438940 x y) (@lem2438938 n x y)). Qed.
Lemma lem2438942 (x : int) (y : int) : (term388 x y) = (term389 x y).
Proof. exact (@lem1988289 term95 (term122 x y)). Qed.
Lemma lem2438960 (x : int) (y : int) : (term390 x y) = (term391 x y).
Proof. exact (@lem1982792 term95 (term122 x y)). Qed.
Lemma lem2438961 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2438962 (y : int) : (term267 y) = (term268 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2438964 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438965 : term132 = term137.
Proof. exact (@lem2438964 term81). Qed.
Lemma lem2438967 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2438968 : term132 = term137.
Proof. exact (@lem2438967 term81). Qed.
Lemma lem2438969 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438970 : term138 = term139.
Proof. exact (MK_COMB (@lem2438969) (@lem2438968)). Qed.
Lemma lem2438971 : term269 = term270.
Proof. exact (MK_COMB (@lem2438970) (@lem2438965)). Qed.
Lemma lem2438972 : term270 = term271.
Proof. exact (@lem1981613 term132 term132 term80 term80). Qed.
Lemma lem2438974 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2438975 : term145 = term146.
Proof. exact (@lem2438974 term81 term81). Qed.
Lemma lem2438976 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438977 : term148 = term81.
Proof. exact (EQ_MP (@lem2438976) (@lem940073)). Qed.
Lemma lem2438978 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438979 : term146 = term80.
Proof. exact (MK_COMB (@lem2438978) (@lem2438977)). Qed.
Lemma lem2438980 : term145 = term80.
Proof. exact (TRANS (@lem2438975) (@lem2438979)). Qed.
Lemma lem2438982 (m : nat) (n : nat) : (term272 m n) = (term144 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2438983 : term269 = term146.
Proof. exact (@lem2438982 term81 term81). Qed.
Lemma lem2438984 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2438985 : term148 = term81.
Proof. exact (EQ_MP (@lem2438984) (@lem940073)). Qed.
Lemma lem2438986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2438987 : term146 = term80.
Proof. exact (MK_COMB (@lem2438986) (@lem2438985)). Qed.
Lemma lem2438988 : term269 = term80.
Proof. exact (TRANS (@lem2438983) (@lem2438987)). Qed.
Lemma lem2438989 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2438990 : term273 = term274.
Proof. exact (MK_COMB (@lem2438989) (@lem2438988)). Qed.
Lemma lem2438991 : term271 = term134.
Proof. exact (MK_COMB (@lem2438990) (@lem2438980)). Qed.
Lemma lem2438992 : term270 = term134.
Proof. exact (TRANS (@lem2438972) (@lem2438991)). Qed.
Lemma lem2438993 : term269 = term134.
Proof. exact (TRANS (@lem2438971) (@lem2438992)). Qed.
Lemma lem2438995 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2438996 : term134 = term80.
Proof. exact (@lem2438995 term80). Qed.
Lemma lem2438997 : term269 = term80.
Proof. exact (TRANS (@lem2438993) (@lem2438996)). Qed.
Lemma lem2438998 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2438999 : term275 = term276.
Proof. exact (MK_COMB (@lem2438998) (@lem2438997)). Qed.
Lemma lem2439000 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2439001 (y : int) : (term268 y) = (term277 y).
Proof. exact (MK_COMB (@lem2438999) (@lem2439000 y)). Qed.
Lemma lem2439002 (y : int) : (term267 y) = (term277 y).
Proof. exact (TRANS (@lem2438962 y) (@lem2439001 y)). Qed.
Lemma lem2439003 (y : int) : (term277 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2439004 (y : int) : (term267 y) = (real_of_int y).
Proof. exact (TRANS (@lem2439002 y) (@lem2439003 y)). Qed.
Lemma lem2439007 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439008 (x : int) (y : int) : (term266 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem2439007 x) (@lem2439004 y)). Qed.
Lemma lem2439009 (x : int) (y : int) : (term265 x y) = (term278 x y).
Proof. exact (TRANS (@lem2438961 x y) (@lem2439008 x y)). Qed.
Lemma lem2439010 : term392 = term392.
Proof. exact (eq_refl term392). Qed.
Lemma lem2439011 (x : int) (y : int) : (term391 x y) = (term393 x y).
Proof. exact (MK_COMB (@lem2439010) (@lem2439009 x y)). Qed.
Lemma lem2439012 (x : int) (y : int) : (term393 x y) = (term278 x y).
Proof. exact (@lem1982721 (term278 x y)). Qed.
Lemma lem2439013 (x : int) (y : int) : (term391 x y) = (term278 x y).
Proof. exact (TRANS (@lem2439011 x y) (@lem2439012 x y)). Qed.
Lemma lem2439015 (x : int) (y : int) : (term390 x y) = (term278 x y).
Proof. exact (TRANS (@lem2438960 x y) (@lem2439013 x y)). Qed.
Lemma lem2439016 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2439017 (x : int) (y : int) : (term394 x y) = (term395 x y).
Proof. exact (MK_COMB (@lem2439016) (@lem2439015 x y)). Qed.
Lemma lem2439018 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439019 (x : int) (y : int) : (term389 x y) = (term396 x y).
Proof. exact (MK_COMB (@lem2439017 x y) (@lem2439018)). Qed.
Lemma lem2439020 (x : int) (y : int) : (term388 x y) = (term396 x y).
Proof. exact (TRANS (@lem2438942 x y) (@lem2439019 x y)). Qed.
Lemma lem2439021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439022 (n : int) (x : int) (y : int) : (term291 n x y) = (term291 n x y).
Proof. exact (MK_COMB (@lem2439021) (@lem2438646 n x y)). Qed.
Lemma lem2439023 (n : int) (x : int) (y : int) : (term292 n x y) = (term292 n x y).
Proof. exact (MK_COMB (@lem2439022 n x y) (@lem2438718 n x y)). Qed.
Lemma lem2439025 (x : int) (y : int) (n : int) : (term397 x y n) = (term398 x y n).
Proof. exact (@lem1988291 (term399 x y n) term95). Qed.
Lemma lem2439026 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439033 (n : int) : (term201 n) = (term201 n).
Proof. exact (eq_refl (term201 n)). Qed.
Lemma lem2439049 (x : int) (y : int) : (term400 x y) = (term265 x y).
Proof. exact (@lem1982785 (term122 x y)). Qed.
Lemma lem2439050 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2439051 (y : int) : (term267 y) = (term268 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2439053 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439054 : term132 = term137.
Proof. exact (@lem2439053 term81). Qed.
Lemma lem2439056 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439057 : term132 = term137.
Proof. exact (@lem2439056 term81). Qed.
Lemma lem2439058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439059 : term138 = term139.
Proof. exact (MK_COMB (@lem2439058) (@lem2439057)). Qed.
Lemma lem2439060 : term269 = term270.
Proof. exact (MK_COMB (@lem2439059) (@lem2439054)). Qed.
Lemma lem2439061 : term270 = term271.
Proof. exact (@lem1981613 term132 term132 term80 term80). Qed.
Lemma lem2439063 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2439064 : term145 = term146.
Proof. exact (@lem2439063 term81 term81). Qed.
Lemma lem2439065 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439066 : term148 = term81.
Proof. exact (EQ_MP (@lem2439065) (@lem940073)). Qed.
Lemma lem2439067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439068 : term146 = term80.
Proof. exact (MK_COMB (@lem2439067) (@lem2439066)). Qed.
Lemma lem2439069 : term145 = term80.
Proof. exact (TRANS (@lem2439064) (@lem2439068)). Qed.
Lemma lem2439071 (m : nat) (n : nat) : (term272 m n) = (term144 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2439072 : term269 = term146.
Proof. exact (@lem2439071 term81 term81). Qed.
Lemma lem2439073 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439074 : term148 = term81.
Proof. exact (EQ_MP (@lem2439073) (@lem940073)). Qed.
Lemma lem2439075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439076 : term146 = term80.
Proof. exact (MK_COMB (@lem2439075) (@lem2439074)). Qed.
Lemma lem2439077 : term269 = term80.
Proof. exact (TRANS (@lem2439072) (@lem2439076)). Qed.
Lemma lem2439078 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2439079 : term273 = term274.
Proof. exact (MK_COMB (@lem2439078) (@lem2439077)). Qed.
Lemma lem2439080 : term271 = term134.
Proof. exact (MK_COMB (@lem2439079) (@lem2439069)). Qed.
Lemma lem2439081 : term270 = term134.
Proof. exact (TRANS (@lem2439061) (@lem2439080)). Qed.
Lemma lem2439082 : term269 = term134.
Proof. exact (TRANS (@lem2439060) (@lem2439081)). Qed.
Lemma lem2439084 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2439085 : term134 = term80.
Proof. exact (@lem2439084 term80). Qed.
Lemma lem2439086 : term269 = term80.
Proof. exact (TRANS (@lem2439082) (@lem2439085)). Qed.
Lemma lem2439087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439088 : term275 = term276.
Proof. exact (MK_COMB (@lem2439087) (@lem2439086)). Qed.
Lemma lem2439089 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2439090 (y : int) : (term268 y) = (term277 y).
Proof. exact (MK_COMB (@lem2439088) (@lem2439089 y)). Qed.
Lemma lem2439091 (y : int) : (term267 y) = (term277 y).
Proof. exact (TRANS (@lem2439051 y) (@lem2439090 y)). Qed.
Lemma lem2439092 (y : int) : (term277 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2439093 (y : int) : (term267 y) = (real_of_int y).
Proof. exact (TRANS (@lem2439091 y) (@lem2439092 y)). Qed.
Lemma lem2439096 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439097 (x : int) (y : int) : (term266 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem2439096 x) (@lem2439093 y)). Qed.
Lemma lem2439098 (x : int) (y : int) : (term265 x y) = (term278 x y).
Proof. exact (TRANS (@lem2439050 x y) (@lem2439097 x y)). Qed.
Lemma lem2439100 (x : int) (y : int) : (term400 x y) = (term278 x y).
Proof. exact (TRANS (@lem2439049 x y) (@lem2439098 x y)). Qed.
Lemma lem2439101 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2439102 (x : int) (y : int) : (term401 x y) = (term402 x y).
Proof. exact (MK_COMB (@lem2439101) (@lem2439100 x y)). Qed.
Lemma lem2439103 (x : int) (y : int) (n : int) : (term399 x y n) = (term403 x y n).
Proof. exact (MK_COMB (@lem2439102 x y) (@lem2439033 n)). Qed.
Lemma lem2439104 (n : int) (x : int) (y : int) : (term403 x y n) = (term404 n x y).
Proof. exact (@lem1982761 (term201 n) (term278 x y)). Qed.
Lemma lem2439105 (n : int) (x : int) (y : int) : (term399 x y n) = (term404 n x y).
Proof. exact (TRANS (@lem2439103 x y n) (@lem2439104 n x y)). Qed.
Lemma lem2439106 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2439107 (n : int) (x : int) (y : int) : (term405 x y n) = (term406 n x y).
Proof. exact (MK_COMB (@lem2439106) (@lem2439105 n x y)). Qed.
Lemma lem2439108 (n : int) (x : int) (y : int) : (term407 x y n) = (term408 n x y).
Proof. exact (MK_COMB (@lem2439107 n x y) (@lem2439026)). Qed.
Lemma lem2439109 (n : int) (x : int) (y : int) : (term408 n x y) = (term409 n x y).
Proof. exact (@lem1982792 (term404 n x y) term95). Qed.
Lemma lem2439111 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2439112 : term95 = term179.
Proof. exact (@lem2439111 (NUMERAL 0)). Qed.
Lemma lem2439114 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439115 : term132 = term137.
Proof. exact (@lem2439114 term81). Qed.
Lemma lem2439116 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439117 : term138 = term139.
Proof. exact (MK_COMB (@lem2439116) (@lem2439115)). Qed.
Lemma lem2439118 : term180 = term181.
Proof. exact (MK_COMB (@lem2439117) (@lem2439112)). Qed.
Lemma lem2439119 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2439121 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2439122 : term145 = term146.
Proof. exact (@lem2439121 term81 term81). Qed.
Lemma lem2439123 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439124 : term148 = term81.
Proof. exact (EQ_MP (@lem2439123) (@lem940073)). Qed.
Lemma lem2439125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439126 : term146 = term80.
Proof. exact (MK_COMB (@lem2439125) (@lem2439124)). Qed.
Lemma lem2439127 : term145 = term80.
Proof. exact (TRANS (@lem2439122) (@lem2439126)). Qed.
Lemma lem2439129 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2439130 : term180 = term95.
Proof. exact (@lem2439129 term81). Qed.
Lemma lem2439131 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2439132 : term184 = term185.
Proof. exact (MK_COMB (@lem2439131) (@lem2439130)). Qed.
Lemma lem2439133 : term182 = term179.
Proof. exact (MK_COMB (@lem2439132) (@lem2439127)). Qed.
Lemma lem2439134 : term181 = term179.
Proof. exact (TRANS (@lem2439119) (@lem2439133)). Qed.
Lemma lem2439135 : term180 = term179.
Proof. exact (TRANS (@lem2439118) (@lem2439134)). Qed.
Lemma lem2439137 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2439138 : term179 = term95.
Proof. exact (@lem2439137 term95). Qed.
Lemma lem2439139 : term180 = term95.
Proof. exact (TRANS (@lem2439135) (@lem2439138)). Qed.
Lemma lem2439140 (n : int) (x : int) (y : int) : (term410 n x y) = (term410 n x y).
Proof. exact (eq_refl (term410 n x y)). Qed.
Lemma lem2439141 (n : int) (x : int) (y : int) : (term409 n x y) = (term411 n x y).
Proof. exact (MK_COMB (@lem2439140 n x y) (@lem2439139)). Qed.
Lemma lem2439142 (n : int) (x : int) (y : int) : (term411 n x y) = (term404 n x y).
Proof. exact (@lem1982723 (term404 n x y)). Qed.
Lemma lem2439143 (n : int) (x : int) (y : int) : (term409 n x y) = (term404 n x y).
Proof. exact (TRANS (@lem2439141 n x y) (@lem2439142 n x y)). Qed.
Lemma lem2439144 (n : int) (x : int) (y : int) : (term408 n x y) = (term404 n x y).
Proof. exact (TRANS (@lem2439109 n x y) (@lem2439143 n x y)). Qed.
Lemma lem2439145 (n : int) (x : int) (y : int) : (term407 x y n) = (term404 n x y).
Proof. exact (TRANS (@lem2439108 n x y) (@lem2439144 n x y)). Qed.
Lemma lem2439146 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439147 (n : int) (x : int) (y : int) : (term412 x y n) = (term413 n x y).
Proof. exact (MK_COMB (@lem2439146) (@lem2439145 n x y)). Qed.
Lemma lem2439148 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439149 (n : int) (x : int) (y : int) : (term398 x y n) = (term414 n x y).
Proof. exact (MK_COMB (@lem2439147 n x y) (@lem2439148)). Qed.
Lemma lem2439150 (n : int) (x : int) (y : int) : (term397 x y n) = (term414 n x y).
Proof. exact (TRANS (@lem2439025 x y n) (@lem2439149 n x y)). Qed.
Lemma lem2439151 (x : int) (y : int) (n : int) : (term415 x y n) = (term416 x y n).
Proof. exact (@lem1988291 (term417 x y n) term95). Qed.
Lemma lem2439152 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439153 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2439169 (x : int) (y : int) : (term400 x y) = (term265 x y).
Proof. exact (@lem1982785 (term122 x y)). Qed.
Lemma lem2439170 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2439171 (y : int) : (term267 y) = (term268 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2439173 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439174 : term132 = term137.
Proof. exact (@lem2439173 term81). Qed.
Lemma lem2439176 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439177 : term132 = term137.
Proof. exact (@lem2439176 term81). Qed.
Lemma lem2439178 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439179 : term138 = term139.
Proof. exact (MK_COMB (@lem2439178) (@lem2439177)). Qed.
Lemma lem2439180 : term269 = term270.
Proof. exact (MK_COMB (@lem2439179) (@lem2439174)). Qed.
Lemma lem2439181 : term270 = term271.
Proof. exact (@lem1981613 term132 term132 term80 term80). Qed.
Lemma lem2439183 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2439184 : term145 = term146.
Proof. exact (@lem2439183 term81 term81). Qed.
Lemma lem2439185 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439186 : term148 = term81.
Proof. exact (EQ_MP (@lem2439185) (@lem940073)). Qed.
Lemma lem2439187 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439188 : term146 = term80.
Proof. exact (MK_COMB (@lem2439187) (@lem2439186)). Qed.
Lemma lem2439189 : term145 = term80.
Proof. exact (TRANS (@lem2439184) (@lem2439188)). Qed.
Lemma lem2439191 (m : nat) (n : nat) : (term272 m n) = (term144 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2439192 : term269 = term146.
Proof. exact (@lem2439191 term81 term81). Qed.
Lemma lem2439193 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439194 : term148 = term81.
Proof. exact (EQ_MP (@lem2439193) (@lem940073)). Qed.
Lemma lem2439195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439196 : term146 = term80.
Proof. exact (MK_COMB (@lem2439195) (@lem2439194)). Qed.
Lemma lem2439197 : term269 = term80.
Proof. exact (TRANS (@lem2439192) (@lem2439196)). Qed.
Lemma lem2439198 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2439199 : term273 = term274.
Proof. exact (MK_COMB (@lem2439198) (@lem2439197)). Qed.
Lemma lem2439200 : term271 = term134.
Proof. exact (MK_COMB (@lem2439199) (@lem2439189)). Qed.
Lemma lem2439201 : term270 = term134.
Proof. exact (TRANS (@lem2439181) (@lem2439200)). Qed.
Lemma lem2439202 : term269 = term134.
Proof. exact (TRANS (@lem2439180) (@lem2439201)). Qed.
Lemma lem2439204 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2439205 : term134 = term80.
Proof. exact (@lem2439204 term80). Qed.
Lemma lem2439206 : term269 = term80.
Proof. exact (TRANS (@lem2439202) (@lem2439205)). Qed.
Lemma lem2439207 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439208 : term275 = term276.
Proof. exact (MK_COMB (@lem2439207) (@lem2439206)). Qed.
Lemma lem2439209 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2439210 (y : int) : (term268 y) = (term277 y).
Proof. exact (MK_COMB (@lem2439208) (@lem2439209 y)). Qed.
Lemma lem2439211 (y : int) : (term267 y) = (term277 y).
Proof. exact (TRANS (@lem2439171 y) (@lem2439210 y)). Qed.
Lemma lem2439212 (y : int) : (term277 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2439213 (y : int) : (term267 y) = (real_of_int y).
Proof. exact (TRANS (@lem2439211 y) (@lem2439212 y)). Qed.
Lemma lem2439216 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439217 (x : int) (y : int) : (term266 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem2439216 x) (@lem2439213 y)). Qed.
Lemma lem2439218 (x : int) (y : int) : (term265 x y) = (term278 x y).
Proof. exact (TRANS (@lem2439170 x y) (@lem2439217 x y)). Qed.
Lemma lem2439220 (x : int) (y : int) : (term400 x y) = (term278 x y).
Proof. exact (TRANS (@lem2439169 x y) (@lem2439218 x y)). Qed.
Lemma lem2439221 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2439222 (x : int) (y : int) : (term401 x y) = (term402 x y).
Proof. exact (MK_COMB (@lem2439221) (@lem2439220 x y)). Qed.
Lemma lem2439223 (x : int) (y : int) (n : int) : (term417 x y n) = (term418 x y n).
Proof. exact (MK_COMB (@lem2439222 x y) (@lem2439153 n)). Qed.
Lemma lem2439224 (n : int) (x : int) (y : int) : (term418 x y n) = (term419 n x y).
Proof. exact (@lem1982761 (real_of_int n) (term278 x y)). Qed.
Lemma lem2439225 (n : int) (x : int) (y : int) : (term417 x y n) = (term419 n x y).
Proof. exact (TRANS (@lem2439223 x y n) (@lem2439224 n x y)). Qed.
Lemma lem2439226 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2439227 (n : int) (x : int) (y : int) : (term420 x y n) = (term421 n x y).
Proof. exact (MK_COMB (@lem2439226) (@lem2439225 n x y)). Qed.
Lemma lem2439228 (n : int) (x : int) (y : int) : (term422 x y n) = (term423 n x y).
Proof. exact (MK_COMB (@lem2439227 n x y) (@lem2439152)). Qed.
Lemma lem2439229 (n : int) (x : int) (y : int) : (term423 n x y) = (term424 n x y).
Proof. exact (@lem1982792 (term419 n x y) term95). Qed.
Lemma lem2439231 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2439232 : term95 = term179.
Proof. exact (@lem2439231 (NUMERAL 0)). Qed.
Lemma lem2439234 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439235 : term132 = term137.
Proof. exact (@lem2439234 term81). Qed.
Lemma lem2439236 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439237 : term138 = term139.
Proof. exact (MK_COMB (@lem2439236) (@lem2439235)). Qed.
Lemma lem2439238 : term180 = term181.
Proof. exact (MK_COMB (@lem2439237) (@lem2439232)). Qed.
Lemma lem2439239 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2439241 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2439242 : term145 = term146.
Proof. exact (@lem2439241 term81 term81). Qed.
Lemma lem2439243 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439244 : term148 = term81.
Proof. exact (EQ_MP (@lem2439243) (@lem940073)). Qed.
Lemma lem2439245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439246 : term146 = term80.
Proof. exact (MK_COMB (@lem2439245) (@lem2439244)). Qed.
Lemma lem2439247 : term145 = term80.
Proof. exact (TRANS (@lem2439242) (@lem2439246)). Qed.
Lemma lem2439249 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2439250 : term180 = term95.
Proof. exact (@lem2439249 term81). Qed.
Lemma lem2439251 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2439252 : term184 = term185.
Proof. exact (MK_COMB (@lem2439251) (@lem2439250)). Qed.
Lemma lem2439253 : term182 = term179.
Proof. exact (MK_COMB (@lem2439252) (@lem2439247)). Qed.
Lemma lem2439254 : term181 = term179.
Proof. exact (TRANS (@lem2439239) (@lem2439253)). Qed.
Lemma lem2439255 : term180 = term179.
Proof. exact (TRANS (@lem2439238) (@lem2439254)). Qed.
Lemma lem2439257 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2439258 : term179 = term95.
Proof. exact (@lem2439257 term95). Qed.
Lemma lem2439259 : term180 = term95.
Proof. exact (TRANS (@lem2439255) (@lem2439258)). Qed.
Lemma lem2439260 (n : int) (x : int) (y : int) : (term425 n x y) = (term425 n x y).
Proof. exact (eq_refl (term425 n x y)). Qed.
Lemma lem2439261 (n : int) (x : int) (y : int) : (term424 n x y) = (term426 n x y).
Proof. exact (MK_COMB (@lem2439260 n x y) (@lem2439259)). Qed.
Lemma lem2439262 (n : int) (x : int) (y : int) : (term426 n x y) = (term419 n x y).
Proof. exact (@lem1982723 (term419 n x y)). Qed.
Lemma lem2439263 (n : int) (x : int) (y : int) : (term424 n x y) = (term419 n x y).
Proof. exact (TRANS (@lem2439261 n x y) (@lem2439262 n x y)). Qed.
Lemma lem2439264 (n : int) (x : int) (y : int) : (term423 n x y) = (term419 n x y).
Proof. exact (TRANS (@lem2439229 n x y) (@lem2439263 n x y)). Qed.
Lemma lem2439265 (n : int) (x : int) (y : int) : (term422 x y n) = (term419 n x y).
Proof. exact (TRANS (@lem2439228 n x y) (@lem2439264 n x y)). Qed.
Lemma lem2439266 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439267 (n : int) (x : int) (y : int) : (term427 x y n) = (term428 n x y).
Proof. exact (MK_COMB (@lem2439266) (@lem2439265 n x y)). Qed.
Lemma lem2439268 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439269 (n : int) (x : int) (y : int) : (term416 x y n) = (term429 n x y).
Proof. exact (MK_COMB (@lem2439267 n x y) (@lem2439268)). Qed.
Lemma lem2439270 (n : int) (x : int) (y : int) : (term415 x y n) = (term429 n x y).
Proof. exact (TRANS (@lem2439151 x y n) (@lem2439269 n x y)). Qed.
Lemma lem2439271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439272 (n : int) (x : int) (y : int) : (term430 x y n) = (term431 n x y).
Proof. exact (MK_COMB (@lem2439271) (@lem2439150 n x y)). Qed.
Lemma lem2439273 (n : int) (x : int) (y : int) : (term432 x y n) = (term433 n x y).
Proof. exact (MK_COMB (@lem2439272 n x y) (@lem2439270 n x y)). Qed.
Lemma lem2439274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439275 (n : int) (x : int) (y : int) : (term434 x y n) = (term435 n x y).
Proof. exact (MK_COMB (@lem2439274) (@lem2439273 n x y)). Qed.
Lemma lem2439276 (n : int) (x : int) (y : int) : (term436 n x y) = (term437 n x y).
Proof. exact (MK_COMB (@lem2439275 n x y) (@lem2438929 x y)). Qed.
Lemma lem2439278 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2439279 (n : int) (x : int) (y : int) : (term438 n x y) = (term439 n x y).
Proof. exact (MK_COMB (@lem2439278 n x y) (@lem2439276 n x y)). Qed.
Lemma lem2439280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439281 (n : int) (x : int) (y : int) : (term293 n x y) = (term293 n x y).
Proof. exact (MK_COMB (@lem2439280) (@lem2439023 n x y)). Qed.
Lemma lem2439282 (n : int) (x : int) (y : int) : (term313 n x y) = (term440 n x y).
Proof. exact (MK_COMB (@lem2439281 n x y) (@lem2439279 n x y)). Qed.
Lemma lem2439283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439284 (x : int) (y : int) : (term314 x y) = (term441 x y).
Proof. exact (MK_COMB (@lem2439283) (@lem2439020 x y)). Qed.
Lemma lem2439285 (n : int) (x : int) (y : int) : (term316 n x y) = (term442 n x y).
Proof. exact (MK_COMB (@lem2439284 x y) (@lem2439282 n x y)). Qed.
Lemma lem2439286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2439287 (n : int) (x : int) (y : int) : (term323 n x y) = (term443 n x y).
Proof. exact (MK_COMB (@lem2439286) (@lem2438941 n x y)). Qed.
Lemma lem2439288 (n : int) (x : int) (y : int) : (term324 n x y) = (term444 n x y).
Proof. exact (MK_COMB (@lem2439287 n x y) (@lem2439285 n x y)). Qed.
Lemma lem2439299 (n : int) (x : int) (y : int) : (term308 n x y) = (term444 n x y).
Proof. exact (TRANS (@lem2438514 n x y) (@lem2439288 n x y)). Qed.
Lemma lem2439300 (n : int) (x : int) (y : int) : (term307 n x y) = (term444 n x y).
Proof. exact (TRANS (@lem2438498 n x y) (@lem2439299 n x y)). Qed.
Lemma lem2439302 (a : real) (x : real) (r : real) : (term248 x a r) = (term249 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2439303 (n : int) (x : int) (y : int) : (term162 x y n) = (term250 n x y).
Proof. exact (@lem2439302 (term251 n) (term122 x y) term95). Qed.
Lemma lem2439322 (x : int) (y : int) : (term252 x y) = (term122 x y).
Proof. exact (@lem1982733 (term122 x y)). Qed.
Lemma lem2439331 (n : int) : (term253 n) = (term253 n).
Proof. exact (eq_refl (term253 n)). Qed.
Lemma lem2439332 (n : int) (x : int) (y : int) : (term254 n x y) = (term255 n x y).
Proof. exact (MK_COMB (@lem2439331 n) (@lem2439322 x y)). Qed.
Lemma lem2439333 (n : int) (x : int) (y : int) : (term255 n x y) = (term256 n x y).
Proof. exact (@lem1982755 (real_of_int n) term132 (term122 x y)). Qed.
Lemma lem2439334 (x : int) (y : int) : (term257 x y) = (term258 x y).
Proof. exact (@lem1982757 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2439335 (y : int) : (term259 y) = (term198 y).
Proof. exact (@lem1982761 (term201 y) term132). Qed.
Lemma lem2439336 (x : int) : (term105 x) = (term105 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2439337 (x : int) (y : int) : (term258 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem2439336 x) (@lem2439335 y)). Qed.
Lemma lem2439338 (x : int) (y : int) : (term257 x y) = (term199 x y).
Proof. exact (TRANS (@lem2439334 x y) (@lem2439337 x y)). Qed.
Lemma lem2439339 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2439340 (n : int) (x : int) (y : int) : (term256 n x y) = (term260 n x y).
Proof. exact (MK_COMB (@lem2439339 n) (@lem2439338 x y)). Qed.
Lemma lem2439341 (n : int) (x : int) (y : int) : (term255 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2439333 n x y) (@lem2439340 n x y)). Qed.
Lemma lem2439342 (n : int) (x : int) (y : int) : (term254 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2439332 n x y) (@lem2439341 n x y)). Qed.
Lemma lem2439343 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439344 (n : int) (x : int) (y : int) : (term261 n x y) = (term262 n x y).
Proof. exact (MK_COMB (@lem2439343) (@lem2439342 n x y)). Qed.
Lemma lem2439345 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439346 (n : int) (x : int) (y : int) : (term263 n x y) = (term264 n x y).
Proof. exact (MK_COMB (@lem2439344 n x y) (@lem2439345)). Qed.
Lemma lem2439364 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2439365 (y : int) : (term267 y) = (term268 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2439367 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439368 : term132 = term137.
Proof. exact (@lem2439367 term81). Qed.
Lemma lem2439370 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439371 : term132 = term137.
Proof. exact (@lem2439370 term81). Qed.
Lemma lem2439372 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439373 : term138 = term139.
Proof. exact (MK_COMB (@lem2439372) (@lem2439371)). Qed.
Lemma lem2439374 : term269 = term270.
Proof. exact (MK_COMB (@lem2439373) (@lem2439368)). Qed.
Lemma lem2439375 : term270 = term271.
Proof. exact (@lem1981613 term132 term132 term80 term80). Qed.
Lemma lem2439377 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2439378 : term145 = term146.
Proof. exact (@lem2439377 term81 term81). Qed.
Lemma lem2439379 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439380 : term148 = term81.
Proof. exact (EQ_MP (@lem2439379) (@lem940073)). Qed.
Lemma lem2439381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439382 : term146 = term80.
Proof. exact (MK_COMB (@lem2439381) (@lem2439380)). Qed.
Lemma lem2439383 : term145 = term80.
Proof. exact (TRANS (@lem2439378) (@lem2439382)). Qed.
Lemma lem2439385 (m : nat) (n : nat) : (term272 m n) = (term144 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2439386 : term269 = term146.
Proof. exact (@lem2439385 term81 term81). Qed.
Lemma lem2439387 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439388 : term148 = term81.
Proof. exact (EQ_MP (@lem2439387) (@lem940073)). Qed.
Lemma lem2439389 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439390 : term146 = term80.
Proof. exact (MK_COMB (@lem2439389) (@lem2439388)). Qed.
Lemma lem2439391 : term269 = term80.
Proof. exact (TRANS (@lem2439386) (@lem2439390)). Qed.
Lemma lem2439392 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2439393 : term273 = term274.
Proof. exact (MK_COMB (@lem2439392) (@lem2439391)). Qed.
Lemma lem2439394 : term271 = term134.
Proof. exact (MK_COMB (@lem2439393) (@lem2439383)). Qed.
Lemma lem2439395 : term270 = term134.
Proof. exact (TRANS (@lem2439375) (@lem2439394)). Qed.
Lemma lem2439396 : term269 = term134.
Proof. exact (TRANS (@lem2439374) (@lem2439395)). Qed.
Lemma lem2439398 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2439399 : term134 = term80.
Proof. exact (@lem2439398 term80). Qed.
Lemma lem2439400 : term269 = term80.
Proof. exact (TRANS (@lem2439396) (@lem2439399)). Qed.
Lemma lem2439401 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439402 : term275 = term276.
Proof. exact (MK_COMB (@lem2439401) (@lem2439400)). Qed.
Lemma lem2439403 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2439404 (y : int) : (term268 y) = (term277 y).
Proof. exact (MK_COMB (@lem2439402) (@lem2439403 y)). Qed.
Lemma lem2439405 (y : int) : (term267 y) = (term277 y).
Proof. exact (TRANS (@lem2439365 y) (@lem2439404 y)). Qed.
Lemma lem2439406 (y : int) : (term277 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2439407 (y : int) : (term267 y) = (real_of_int y).
Proof. exact (TRANS (@lem2439405 y) (@lem2439406 y)). Qed.
Lemma lem2439410 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439411 (x : int) (y : int) : (term266 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem2439410 x) (@lem2439407 y)). Qed.
Lemma lem2439413 (x : int) (y : int) : (term265 x y) = (term278 x y).
Proof. exact (TRANS (@lem2439364 x y) (@lem2439411 x y)). Qed.
Lemma lem2439422 (n : int) : (term253 n) = (term253 n).
Proof. exact (eq_refl (term253 n)). Qed.
Lemma lem2439423 (n : int) (x : int) (y : int) : (term279 n x y) = (term280 n x y).
Proof. exact (MK_COMB (@lem2439422 n) (@lem2439413 x y)). Qed.
Lemma lem2439424 (n : int) (x : int) (y : int) : (term280 n x y) = (term281 n x y).
Proof. exact (@lem1982755 (real_of_int n) term132 (term278 x y)). Qed.
Lemma lem2439425 (x : int) (y : int) : (term282 x y) = (term283 x y).
Proof. exact (@lem1982757 (term201 x) term132 (real_of_int y)). Qed.
Lemma lem2439426 (y : int) : (term284 y) = (term251 y).
Proof. exact (@lem1982761 (real_of_int y) term132). Qed.
Lemma lem2439427 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439428 (x : int) (y : int) : (term283 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem2439427 x) (@lem2439426 y)). Qed.
Lemma lem2439429 (x : int) (y : int) : (term282 x y) = (term200 x y).
Proof. exact (TRANS (@lem2439425 x y) (@lem2439428 x y)). Qed.
Lemma lem2439430 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2439431 (n : int) (x : int) (y : int) : (term281 n x y) = (term285 n x y).
Proof. exact (MK_COMB (@lem2439430 n) (@lem2439429 x y)). Qed.
Lemma lem2439432 (n : int) (x : int) (y : int) : (term280 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2439424 n x y) (@lem2439431 n x y)). Qed.
Lemma lem2439433 (n : int) (x : int) (y : int) : (term279 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2439423 n x y) (@lem2439432 n x y)). Qed.
Lemma lem2439434 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439435 (n : int) (x : int) (y : int) : (term286 n x y) = (term287 n x y).
Proof. exact (MK_COMB (@lem2439434) (@lem2439433 n x y)). Qed.
Lemma lem2439436 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439437 (n : int) (x : int) (y : int) : (term288 n x y) = (term289 n x y).
Proof. exact (MK_COMB (@lem2439435 n x y) (@lem2439436)). Qed.
Lemma lem2439438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439439 (n : int) (x : int) (y : int) : (term290 n x y) = (term291 n x y).
Proof. exact (MK_COMB (@lem2439438) (@lem2439437 n x y)). Qed.
Lemma lem2439440 (n : int) (x : int) (y : int) : (term250 n x y) = (term292 n x y).
Proof. exact (MK_COMB (@lem2439439 n x y) (@lem2439346 n x y)). Qed.
Lemma lem2439441 (n : int) (x : int) (y : int) : (term162 x y n) = (term292 n x y).
Proof. exact (TRANS (@lem2439303 n x y) (@lem2439440 n x y)). Qed.
Lemma lem2439442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439443 (n : int) (x : int) (y : int) : (term212 x y n) = (term293 n x y).
Proof. exact (MK_COMB (@lem2439442) (@lem2439441 n x y)). Qed.
Lemma lem2439444 (n : int) (x : int) (y : int) : (term244 n x y) = (term244 n x y).
Proof. exact (eq_refl (term244 n x y)). Qed.
Lemma lem2439447 (n : int) (x : int) (y : int) : (term445 n x y) = (term446 n x y).
Proof. exact (MK_COMB (@lem2439443 n x y) (@lem2439444 n x y)). Qed.
Lemma lem2439448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2439449 (n : int) (x : int) (y : int) : (term447 n x y) = (term448 n x y).
Proof. exact (MK_COMB (@lem2439448) (@lem2439300 n x y)). Qed.
Lemma lem2439450 (n : int) (x : int) (y : int) : (term242 n x y) = (term449 n x y).
Proof. exact (MK_COMB (@lem2439449 n x y) (@lem2439447 n x y)). Qed.
Lemma lem2439452 (a : real) (x : real) (r : real) : (term248 x a r) = (term249 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2439453 (n : int) (x : int) (y : int) : (term162 x y n) = (term250 n x y).
Proof. exact (@lem2439452 (term251 n) (term122 x y) term95). Qed.
Lemma lem2439472 (x : int) (y : int) : (term252 x y) = (term122 x y).
Proof. exact (@lem1982733 (term122 x y)). Qed.
Lemma lem2439481 (n : int) : (term253 n) = (term253 n).
Proof. exact (eq_refl (term253 n)). Qed.
Lemma lem2439482 (n : int) (x : int) (y : int) : (term254 n x y) = (term255 n x y).
Proof. exact (MK_COMB (@lem2439481 n) (@lem2439472 x y)). Qed.
Lemma lem2439483 (n : int) (x : int) (y : int) : (term255 n x y) = (term256 n x y).
Proof. exact (@lem1982755 (real_of_int n) term132 (term122 x y)). Qed.
Lemma lem2439484 (x : int) (y : int) : (term257 x y) = (term258 x y).
Proof. exact (@lem1982757 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2439485 (y : int) : (term259 y) = (term198 y).
Proof. exact (@lem1982761 (term201 y) term132). Qed.
Lemma lem2439486 (x : int) : (term105 x) = (term105 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2439487 (x : int) (y : int) : (term258 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem2439486 x) (@lem2439485 y)). Qed.
Lemma lem2439488 (x : int) (y : int) : (term257 x y) = (term199 x y).
Proof. exact (TRANS (@lem2439484 x y) (@lem2439487 x y)). Qed.
Lemma lem2439489 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2439490 (n : int) (x : int) (y : int) : (term256 n x y) = (term260 n x y).
Proof. exact (MK_COMB (@lem2439489 n) (@lem2439488 x y)). Qed.
Lemma lem2439491 (n : int) (x : int) (y : int) : (term255 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2439483 n x y) (@lem2439490 n x y)). Qed.
Lemma lem2439492 (n : int) (x : int) (y : int) : (term254 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2439482 n x y) (@lem2439491 n x y)). Qed.
Lemma lem2439493 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439494 (n : int) (x : int) (y : int) : (term261 n x y) = (term262 n x y).
Proof. exact (MK_COMB (@lem2439493) (@lem2439492 n x y)). Qed.
Lemma lem2439495 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439496 (n : int) (x : int) (y : int) : (term263 n x y) = (term264 n x y).
Proof. exact (MK_COMB (@lem2439494 n x y) (@lem2439495)). Qed.
Lemma lem2439514 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2439515 (y : int) : (term267 y) = (term268 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2439517 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439518 : term132 = term137.
Proof. exact (@lem2439517 term81). Qed.
Lemma lem2439520 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439521 : term132 = term137.
Proof. exact (@lem2439520 term81). Qed.
Lemma lem2439522 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439523 : term138 = term139.
Proof. exact (MK_COMB (@lem2439522) (@lem2439521)). Qed.
Lemma lem2439524 : term269 = term270.
Proof. exact (MK_COMB (@lem2439523) (@lem2439518)). Qed.
Lemma lem2439525 : term270 = term271.
Proof. exact (@lem1981613 term132 term132 term80 term80). Qed.
Lemma lem2439527 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2439528 : term145 = term146.
Proof. exact (@lem2439527 term81 term81). Qed.
Lemma lem2439529 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439530 : term148 = term81.
Proof. exact (EQ_MP (@lem2439529) (@lem940073)). Qed.
Lemma lem2439531 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439532 : term146 = term80.
Proof. exact (MK_COMB (@lem2439531) (@lem2439530)). Qed.
Lemma lem2439533 : term145 = term80.
Proof. exact (TRANS (@lem2439528) (@lem2439532)). Qed.
Lemma lem2439535 (m : nat) (n : nat) : (term272 m n) = (term144 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2439536 : term269 = term146.
Proof. exact (@lem2439535 term81 term81). Qed.
Lemma lem2439537 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439538 : term148 = term81.
Proof. exact (EQ_MP (@lem2439537) (@lem940073)). Qed.
Lemma lem2439539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439540 : term146 = term80.
Proof. exact (MK_COMB (@lem2439539) (@lem2439538)). Qed.
Lemma lem2439541 : term269 = term80.
Proof. exact (TRANS (@lem2439536) (@lem2439540)). Qed.
Lemma lem2439542 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2439543 : term273 = term274.
Proof. exact (MK_COMB (@lem2439542) (@lem2439541)). Qed.
Lemma lem2439544 : term271 = term134.
Proof. exact (MK_COMB (@lem2439543) (@lem2439533)). Qed.
Lemma lem2439545 : term270 = term134.
Proof. exact (TRANS (@lem2439525) (@lem2439544)). Qed.
Lemma lem2439546 : term269 = term134.
Proof. exact (TRANS (@lem2439524) (@lem2439545)). Qed.
Lemma lem2439548 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2439549 : term134 = term80.
Proof. exact (@lem2439548 term80). Qed.
Lemma lem2439550 : term269 = term80.
Proof. exact (TRANS (@lem2439546) (@lem2439549)). Qed.
Lemma lem2439551 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439552 : term275 = term276.
Proof. exact (MK_COMB (@lem2439551) (@lem2439550)). Qed.
Lemma lem2439553 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2439554 (y : int) : (term268 y) = (term277 y).
Proof. exact (MK_COMB (@lem2439552) (@lem2439553 y)). Qed.
Lemma lem2439555 (y : int) : (term267 y) = (term277 y).
Proof. exact (TRANS (@lem2439515 y) (@lem2439554 y)). Qed.
Lemma lem2439556 (y : int) : (term277 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2439557 (y : int) : (term267 y) = (real_of_int y).
Proof. exact (TRANS (@lem2439555 y) (@lem2439556 y)). Qed.
Lemma lem2439560 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439561 (x : int) (y : int) : (term266 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem2439560 x) (@lem2439557 y)). Qed.
Lemma lem2439563 (x : int) (y : int) : (term265 x y) = (term278 x y).
Proof. exact (TRANS (@lem2439514 x y) (@lem2439561 x y)). Qed.
Lemma lem2439572 (n : int) : (term253 n) = (term253 n).
Proof. exact (eq_refl (term253 n)). Qed.
Lemma lem2439573 (n : int) (x : int) (y : int) : (term279 n x y) = (term280 n x y).
Proof. exact (MK_COMB (@lem2439572 n) (@lem2439563 x y)). Qed.
Lemma lem2439574 (n : int) (x : int) (y : int) : (term280 n x y) = (term281 n x y).
Proof. exact (@lem1982755 (real_of_int n) term132 (term278 x y)). Qed.
Lemma lem2439575 (x : int) (y : int) : (term282 x y) = (term283 x y).
Proof. exact (@lem1982757 (term201 x) term132 (real_of_int y)). Qed.
Lemma lem2439576 (y : int) : (term284 y) = (term251 y).
Proof. exact (@lem1982761 (real_of_int y) term132). Qed.
Lemma lem2439577 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439578 (x : int) (y : int) : (term283 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem2439577 x) (@lem2439576 y)). Qed.
Lemma lem2439579 (x : int) (y : int) : (term282 x y) = (term200 x y).
Proof. exact (TRANS (@lem2439575 x y) (@lem2439578 x y)). Qed.
Lemma lem2439580 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2439581 (n : int) (x : int) (y : int) : (term281 n x y) = (term285 n x y).
Proof. exact (MK_COMB (@lem2439580 n) (@lem2439579 x y)). Qed.
Lemma lem2439582 (n : int) (x : int) (y : int) : (term280 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2439574 n x y) (@lem2439581 n x y)). Qed.
Lemma lem2439583 (n : int) (x : int) (y : int) : (term279 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2439573 n x y) (@lem2439582 n x y)). Qed.
Lemma lem2439584 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439585 (n : int) (x : int) (y : int) : (term286 n x y) = (term287 n x y).
Proof. exact (MK_COMB (@lem2439584) (@lem2439583 n x y)). Qed.
Lemma lem2439586 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439587 (n : int) (x : int) (y : int) : (term288 n x y) = (term289 n x y).
Proof. exact (MK_COMB (@lem2439585 n x y) (@lem2439586)). Qed.
Lemma lem2439588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439589 (n : int) (x : int) (y : int) : (term290 n x y) = (term291 n x y).
Proof. exact (MK_COMB (@lem2439588) (@lem2439587 n x y)). Qed.
Lemma lem2439590 (n : int) (x : int) (y : int) : (term250 n x y) = (term292 n x y).
Proof. exact (MK_COMB (@lem2439589 n x y) (@lem2439496 n x y)). Qed.
Lemma lem2439591 (n : int) (x : int) (y : int) : (term162 x y n) = (term292 n x y).
Proof. exact (TRANS (@lem2439453 n x y) (@lem2439590 n x y)). Qed.
Lemma lem2439592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439593 (n : int) (x : int) (y : int) : (term212 x y n) = (term293 n x y).
Proof. exact (MK_COMB (@lem2439592) (@lem2439591 n x y)). Qed.
Lemma lem2439595 (a : real) (x : real) (r : real) : (term248 x a r) = (term249 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2439596 (x : int) (y : int) (n : int) : (term173 n x y) = (term294 x y n).
Proof. exact (@lem2439595 (term123 x y) (real_of_int n) term95). Qed.
Lemma lem2439603 (n : int) : (term277 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2439620 (x : int) (y : int) : (term124 x y) = (term124 x y).
Proof. exact (eq_refl (term124 x y)). Qed.
Lemma lem2439623 (x : int) (y : int) (n : int) : (term295 x y n) = (term296 x y n).
Proof. exact (MK_COMB (@lem2439620 x y) (@lem2439603 n)). Qed.
Lemma lem2439624 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439625 (x : int) (y : int) (n : int) : (term297 x y n) = (term298 x y n).
Proof. exact (MK_COMB (@lem2439624) (@lem2439623 x y n)). Qed.
Lemma lem2439626 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439627 (x : int) (y : int) (n : int) : (term299 x y n) = (term300 x y n).
Proof. exact (MK_COMB (@lem2439625 x y n) (@lem2439626)). Qed.
Lemma lem2439660 (x : int) (y : int) (n : int) : (term301 x y n) = (term301 x y n).
Proof. exact (eq_refl (term301 x y n)). Qed.
Lemma lem2439661 (x : int) (y : int) (n : int) : (term294 x y n) = (term302 x y n).
Proof. exact (MK_COMB (@lem2439660 x y n) (@lem2439627 x y n)). Qed.
Lemma lem2439662 (x : int) (y : int) (n : int) : (term173 n x y) = (term302 x y n).
Proof. exact (TRANS (@lem2439596 x y n) (@lem2439661 x y n)). Qed.
Lemma lem2439663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439664 (x : int) (y : int) (n : int) : (term303 n x y) = (term304 x y n).
Proof. exact (MK_COMB (@lem2439663) (@lem2439662 x y n)). Qed.
Lemma lem2439665 (x : int) (y : int) : (term206 x y) = (term206 x y).
Proof. exact (eq_refl (term206 x y)). Qed.
Lemma lem2439666 (n : int) (x : int) (y : int) : (term226 n x y) = (term450 n x y).
Proof. exact (MK_COMB (@lem2439664 x y n) (@lem2439665 x y)). Qed.
Lemma lem2439667 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2439668 (n : int) (x : int) (y : int) : (term239 n x y) = (term451 n x y).
Proof. exact (MK_COMB (@lem2439667 n x y) (@lem2439666 n x y)). Qed.
Lemma lem2439669 (n : int) (x : int) (y : int) : (term452 n x y) = (term453 n x y).
Proof. exact (MK_COMB (@lem2439593 n x y) (@lem2439668 n x y)). Qed.
Lemma lem2439670 (n : int) (x : int) (y : int) : (term454 n x y) = (term453 n x y).
Proof. exact (eq_refl (term454 n x y)). Qed.
Lemma lem2439671 (n : int) (x : int) (y : int) : (term453 n x y) = (term454 n x y).
Proof. exact (SYM (@lem2439670 n x y)). Qed.
Lemma lem2439672 (n : int) (x : int) (y : int) : (term454 n x y) = (term455 n x y).
Proof. exact (@lem1482981 (term456 n x y) (term122 x y)). Qed.
Lemma lem2439673 (n : int) (x : int) (y : int) : (term453 n x y) = (term455 n x y).
Proof. exact (TRANS (@lem2439671 n x y) (@lem2439672 n x y)). Qed.
Lemma lem2439674 (n : int) (x : int) (y : int) : (term457 n x y) = (term458 n x y).
Proof. exact (eq_refl (term457 n x y)). Qed.
Lemma lem2439675 (x : int) (y : int) : (term314 x y) = (term314 x y).
Proof. exact (eq_refl (term314 x y)). Qed.
Lemma lem2439676 (n : int) (x : int) (y : int) : (term459 n x y) = (term460 n x y).
Proof. exact (MK_COMB (@lem2439675 x y) (@lem2439674 n x y)). Qed.
Lemma lem2439677 (n : int) (x : int) (y : int) : (term461 n x y) = (term462 n x y).
Proof. exact (eq_refl (term461 n x y)). Qed.
Lemma lem2439678 (x : int) (y : int) : (term319 x y) = (term319 x y).
Proof. exact (eq_refl (term319 x y)). Qed.
Lemma lem2439679 (n : int) (x : int) (y : int) : (term463 n x y) = (term464 n x y).
Proof. exact (MK_COMB (@lem2439678 x y) (@lem2439677 n x y)). Qed.
Lemma lem2439680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2439681 (n : int) (x : int) (y : int) : (term465 n x y) = (term466 n x y).
Proof. exact (MK_COMB (@lem2439680) (@lem2439679 n x y)). Qed.
Lemma lem2439682 (n : int) (x : int) (y : int) : (term455 n x y) = (term467 n x y).
Proof. exact (MK_COMB (@lem2439681 n x y) (@lem2439676 n x y)). Qed.
Lemma lem2439683 (n : int) (x : int) (y : int) : (term468 n x y) = (term468 n x y).
Proof. exact (eq_refl (term468 n x y)). Qed.
Lemma lem2439684 (n : int) (x : int) (y : int) : ((term453 n x y) = (term455 n x y)) = ((term453 n x y) = (term467 n x y)).
Proof. exact (MK_COMB (@lem2439683 n x y) (@lem2439682 n x y)). Qed.
Lemma lem2439685 (n : int) (x : int) (y : int) : (term453 n x y) = (term467 n x y).
Proof. exact (EQ_MP (@lem2439684 n x y) (@lem2439673 n x y)). Qed.
Lemma lem2439686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439687 (n : int) (x : int) (y : int) : (term291 n x y) = (term291 n x y).
Proof. exact (MK_COMB (@lem2439686) (@lem2438646 n x y)). Qed.
Lemma lem2439688 (n : int) (x : int) (y : int) : (term292 n x y) = (term292 n x y).
Proof. exact (MK_COMB (@lem2439687 n x y) (@lem2438718 n x y)). Qed.
Lemma lem2439690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439691 (n : int) (x : int) (y : int) : (term370 x y n) = (term371 n x y).
Proof. exact (MK_COMB (@lem2439690) (@lem2438794 n x y)). Qed.
Lemma lem2439692 (n : int) (x : int) (y : int) : (term372 x y n) = (term373 n x y).
Proof. exact (MK_COMB (@lem2439691 n x y) (@lem2438860 n x y)). Qed.
Lemma lem2439693 (x : int) (y : int) : (term206 x y) = (term469 x y).
Proof. exact (@lem1988291 (term199 x y) term95). Qed.
Lemma lem2439717 (x : int) (y : int) : (term470 x y) = (term471 x y).
Proof. exact (@lem1982792 (term199 x y) term95). Qed.
Lemma lem2439719 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2439720 : term95 = term179.
Proof. exact (@lem2439719 (NUMERAL 0)). Qed.
Lemma lem2439722 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439723 : term132 = term137.
Proof. exact (@lem2439722 term81). Qed.
Lemma lem2439724 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439725 : term138 = term139.
Proof. exact (MK_COMB (@lem2439724) (@lem2439723)). Qed.
Lemma lem2439726 : term180 = term181.
Proof. exact (MK_COMB (@lem2439725) (@lem2439720)). Qed.
Lemma lem2439727 : term181 = term182.
Proof. exact (@lem1981613 term132 term95 term80 term80). Qed.
Lemma lem2439729 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2439730 : term145 = term146.
Proof. exact (@lem2439729 term81 term81). Qed.
Lemma lem2439731 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439732 : term148 = term81.
Proof. exact (EQ_MP (@lem2439731) (@lem940073)). Qed.
Lemma lem2439733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439734 : term146 = term80.
Proof. exact (MK_COMB (@lem2439733) (@lem2439732)). Qed.
Lemma lem2439735 : term145 = term80.
Proof. exact (TRANS (@lem2439730) (@lem2439734)). Qed.
Lemma lem2439737 (x : nat) : (term183 x) = term95.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2439738 : term180 = term95.
Proof. exact (@lem2439737 term81). Qed.
Lemma lem2439739 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2439740 : term184 = term185.
Proof. exact (MK_COMB (@lem2439739) (@lem2439738)). Qed.
Lemma lem2439741 : term182 = term179.
Proof. exact (MK_COMB (@lem2439740) (@lem2439735)). Qed.
Lemma lem2439742 : term181 = term179.
Proof. exact (TRANS (@lem2439727) (@lem2439741)). Qed.
Lemma lem2439743 : term180 = term179.
Proof. exact (TRANS (@lem2439726) (@lem2439742)). Qed.
Lemma lem2439745 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2439746 : term179 = term95.
Proof. exact (@lem2439745 term95). Qed.
Lemma lem2439747 : term180 = term95.
Proof. exact (TRANS (@lem2439743) (@lem2439746)). Qed.
Lemma lem2439748 (x : int) (y : int) : (term472 x y) = (term472 x y).
Proof. exact (eq_refl (term472 x y)). Qed.
Lemma lem2439749 (x : int) (y : int) : (term471 x y) = (term473 x y).
Proof. exact (MK_COMB (@lem2439748 x y) (@lem2439747)). Qed.
Lemma lem2439750 (x : int) (y : int) : (term473 x y) = (term199 x y).
Proof. exact (@lem1982723 (term199 x y)). Qed.
Lemma lem2439751 (x : int) (y : int) : (term471 x y) = (term199 x y).
Proof. exact (TRANS (@lem2439749 x y) (@lem2439750 x y)). Qed.
Lemma lem2439753 (x : int) (y : int) : (term470 x y) = (term199 x y).
Proof. exact (TRANS (@lem2439717 x y) (@lem2439751 x y)). Qed.
Lemma lem2439754 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439755 (x : int) (y : int) : (term474 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem2439754) (@lem2439753 x y)). Qed.
Lemma lem2439756 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439757 (x : int) (y : int) : (term469 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem2439755 x y) (@lem2439756)). Qed.
Lemma lem2439758 (x : int) (y : int) : (term206 x y) = (term206 x y).
Proof. exact (TRANS (@lem2439693 x y) (@lem2439757 x y)). Qed.
Lemma lem2439759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439760 (n : int) (x : int) (y : int) : (term380 x y n) = (term381 n x y).
Proof. exact (MK_COMB (@lem2439759) (@lem2439692 n x y)). Qed.
Lemma lem2439761 (n : int) (x : int) (y : int) : (term475 n x y) = (term476 n x y).
Proof. exact (MK_COMB (@lem2439760 n x y) (@lem2439758 x y)). Qed.
Lemma lem2439763 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2439764 (n : int) (x : int) (y : int) : (term477 n x y) = (term478 n x y).
Proof. exact (MK_COMB (@lem2439763 n x y) (@lem2439761 n x y)). Qed.
Lemma lem2439765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439766 (n : int) (x : int) (y : int) : (term293 n x y) = (term293 n x y).
Proof. exact (MK_COMB (@lem2439765) (@lem2439688 n x y)). Qed.
Lemma lem2439767 (n : int) (x : int) (y : int) : (term462 n x y) = (term479 n x y).
Proof. exact (MK_COMB (@lem2439766 n x y) (@lem2439764 n x y)). Qed.
Lemma lem2439768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439769 (x : int) (y : int) : (term319 x y) = (term319 x y).
Proof. exact (MK_COMB (@lem2439768) (@lem2438574 x y)). Qed.
Lemma lem2439770 (n : int) (x : int) (y : int) : (term464 n x y) = (term480 n x y).
Proof. exact (MK_COMB (@lem2439769 x y) (@lem2439767 n x y)). Qed.
Lemma lem2439771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439772 (n : int) (x : int) (y : int) : (term291 n x y) = (term291 n x y).
Proof. exact (MK_COMB (@lem2439771) (@lem2438646 n x y)). Qed.
Lemma lem2439773 (n : int) (x : int) (y : int) : (term292 n x y) = (term292 n x y).
Proof. exact (MK_COMB (@lem2439772 n x y) (@lem2438718 n x y)). Qed.
Lemma lem2439775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439776 (n : int) (x : int) (y : int) : (term430 x y n) = (term431 n x y).
Proof. exact (MK_COMB (@lem2439775) (@lem2439150 n x y)). Qed.
Lemma lem2439777 (n : int) (x : int) (y : int) : (term432 x y n) = (term433 n x y).
Proof. exact (MK_COMB (@lem2439776 n x y) (@lem2439270 n x y)). Qed.
Lemma lem2439778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439779 (n : int) (x : int) (y : int) : (term434 x y n) = (term435 n x y).
Proof. exact (MK_COMB (@lem2439778) (@lem2439777 n x y)). Qed.
Lemma lem2439780 (n : int) (x : int) (y : int) : (term481 n x y) = (term482 n x y).
Proof. exact (MK_COMB (@lem2439779 n x y) (@lem2439758 x y)). Qed.
Lemma lem2439782 (n : int) (x : int) (y : int) : (term49 n x y) = (term49 n x y).
Proof. exact (eq_refl (term49 n x y)). Qed.
Lemma lem2439783 (n : int) (x : int) (y : int) : (term483 n x y) = (term484 n x y).
Proof. exact (MK_COMB (@lem2439782 n x y) (@lem2439780 n x y)). Qed.
Lemma lem2439784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439785 (n : int) (x : int) (y : int) : (term293 n x y) = (term293 n x y).
Proof. exact (MK_COMB (@lem2439784) (@lem2439773 n x y)). Qed.
Lemma lem2439786 (n : int) (x : int) (y : int) : (term458 n x y) = (term485 n x y).
Proof. exact (MK_COMB (@lem2439785 n x y) (@lem2439783 n x y)). Qed.
Lemma lem2439787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439788 (x : int) (y : int) : (term314 x y) = (term441 x y).
Proof. exact (MK_COMB (@lem2439787) (@lem2439020 x y)). Qed.
Lemma lem2439789 (n : int) (x : int) (y : int) : (term460 n x y) = (term486 n x y).
Proof. exact (MK_COMB (@lem2439788 x y) (@lem2439786 n x y)). Qed.
Lemma lem2439790 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2439791 (n : int) (x : int) (y : int) : (term466 n x y) = (term487 n x y).
Proof. exact (MK_COMB (@lem2439790) (@lem2439770 n x y)). Qed.
Lemma lem2439792 (n : int) (x : int) (y : int) : (term467 n x y) = (term488 n x y).
Proof. exact (MK_COMB (@lem2439791 n x y) (@lem2439789 n x y)). Qed.
Lemma lem2439803 (n : int) (x : int) (y : int) : (term453 n x y) = (term488 n x y).
Proof. exact (TRANS (@lem2439685 n x y) (@lem2439792 n x y)). Qed.
Lemma lem2439804 (n : int) (x : int) (y : int) : (term452 n x y) = (term488 n x y).
Proof. exact (TRANS (@lem2439669 n x y) (@lem2439803 n x y)). Qed.
Lemma lem2439806 (a : real) (x : real) (r : real) : (term248 x a r) = (term249 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2439807 (n : int) (x : int) (y : int) : (term162 x y n) = (term250 n x y).
Proof. exact (@lem2439806 (term251 n) (term122 x y) term95). Qed.
Lemma lem2439826 (x : int) (y : int) : (term252 x y) = (term122 x y).
Proof. exact (@lem1982733 (term122 x y)). Qed.
Lemma lem2439835 (n : int) : (term253 n) = (term253 n).
Proof. exact (eq_refl (term253 n)). Qed.
Lemma lem2439836 (n : int) (x : int) (y : int) : (term254 n x y) = (term255 n x y).
Proof. exact (MK_COMB (@lem2439835 n) (@lem2439826 x y)). Qed.
Lemma lem2439837 (n : int) (x : int) (y : int) : (term255 n x y) = (term256 n x y).
Proof. exact (@lem1982755 (real_of_int n) term132 (term122 x y)). Qed.
Lemma lem2439838 (x : int) (y : int) : (term257 x y) = (term258 x y).
Proof. exact (@lem1982757 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2439839 (y : int) : (term259 y) = (term198 y).
Proof. exact (@lem1982761 (term201 y) term132). Qed.
Lemma lem2439840 (x : int) : (term105 x) = (term105 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2439841 (x : int) (y : int) : (term258 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem2439840 x) (@lem2439839 y)). Qed.
Lemma lem2439842 (x : int) (y : int) : (term257 x y) = (term199 x y).
Proof. exact (TRANS (@lem2439838 x y) (@lem2439841 x y)). Qed.
Lemma lem2439843 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2439844 (n : int) (x : int) (y : int) : (term256 n x y) = (term260 n x y).
Proof. exact (MK_COMB (@lem2439843 n) (@lem2439842 x y)). Qed.
Lemma lem2439845 (n : int) (x : int) (y : int) : (term255 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2439837 n x y) (@lem2439844 n x y)). Qed.
Lemma lem2439846 (n : int) (x : int) (y : int) : (term254 n x y) = (term260 n x y).
Proof. exact (TRANS (@lem2439836 n x y) (@lem2439845 n x y)). Qed.
Lemma lem2439847 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439848 (n : int) (x : int) (y : int) : (term261 n x y) = (term262 n x y).
Proof. exact (MK_COMB (@lem2439847) (@lem2439846 n x y)). Qed.
Lemma lem2439849 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439850 (n : int) (x : int) (y : int) : (term263 n x y) = (term264 n x y).
Proof. exact (MK_COMB (@lem2439848 n x y) (@lem2439849)). Qed.
Lemma lem2439868 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2439869 (y : int) : (term267 y) = (term268 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2439871 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439872 : term132 = term137.
Proof. exact (@lem2439871 term81). Qed.
Lemma lem2439874 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2439875 : term132 = term137.
Proof. exact (@lem2439874 term81). Qed.
Lemma lem2439876 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439877 : term138 = term139.
Proof. exact (MK_COMB (@lem2439876) (@lem2439875)). Qed.
Lemma lem2439878 : term269 = term270.
Proof. exact (MK_COMB (@lem2439877) (@lem2439872)). Qed.
Lemma lem2439879 : term270 = term271.
Proof. exact (@lem1981613 term132 term132 term80 term80). Qed.
Lemma lem2439881 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2439882 : term145 = term146.
Proof. exact (@lem2439881 term81 term81). Qed.
Lemma lem2439883 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439884 : term148 = term81.
Proof. exact (EQ_MP (@lem2439883) (@lem940073)). Qed.
Lemma lem2439885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439886 : term146 = term80.
Proof. exact (MK_COMB (@lem2439885) (@lem2439884)). Qed.
Lemma lem2439887 : term145 = term80.
Proof. exact (TRANS (@lem2439882) (@lem2439886)). Qed.
Lemma lem2439889 (m : nat) (n : nat) : (term272 m n) = (term144 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2439890 : term269 = term146.
Proof. exact (@lem2439889 term81 term81). Qed.
Lemma lem2439891 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2439892 : term148 = term81.
Proof. exact (EQ_MP (@lem2439891) (@lem940073)). Qed.
Lemma lem2439893 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2439894 : term146 = term80.
Proof. exact (MK_COMB (@lem2439893) (@lem2439892)). Qed.
Lemma lem2439895 : term269 = term80.
Proof. exact (TRANS (@lem2439890) (@lem2439894)). Qed.
Lemma lem2439896 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2439897 : term273 = term274.
Proof. exact (MK_COMB (@lem2439896) (@lem2439895)). Qed.
Lemma lem2439898 : term271 = term134.
Proof. exact (MK_COMB (@lem2439897) (@lem2439887)). Qed.
Lemma lem2439899 : term270 = term134.
Proof. exact (TRANS (@lem2439879) (@lem2439898)). Qed.
Lemma lem2439900 : term269 = term134.
Proof. exact (TRANS (@lem2439878) (@lem2439899)). Qed.
Lemma lem2439902 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2439903 : term134 = term80.
Proof. exact (@lem2439902 term80). Qed.
Lemma lem2439904 : term269 = term80.
Proof. exact (TRANS (@lem2439900) (@lem2439903)). Qed.
Lemma lem2439905 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2439906 : term275 = term276.
Proof. exact (MK_COMB (@lem2439905) (@lem2439904)). Qed.
Lemma lem2439907 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2439908 (y : int) : (term268 y) = (term277 y).
Proof. exact (MK_COMB (@lem2439906) (@lem2439907 y)). Qed.
Lemma lem2439909 (y : int) : (term267 y) = (term277 y).
Proof. exact (TRANS (@lem2439869 y) (@lem2439908 y)). Qed.
Lemma lem2439910 (y : int) : (term277 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2439911 (y : int) : (term267 y) = (real_of_int y).
Proof. exact (TRANS (@lem2439909 y) (@lem2439910 y)). Qed.
Lemma lem2439914 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439915 (x : int) (y : int) : (term266 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem2439914 x) (@lem2439911 y)). Qed.
Lemma lem2439917 (x : int) (y : int) : (term265 x y) = (term278 x y).
Proof. exact (TRANS (@lem2439868 x y) (@lem2439915 x y)). Qed.
Lemma lem2439926 (n : int) : (term253 n) = (term253 n).
Proof. exact (eq_refl (term253 n)). Qed.
Lemma lem2439927 (n : int) (x : int) (y : int) : (term279 n x y) = (term280 n x y).
Proof. exact (MK_COMB (@lem2439926 n) (@lem2439917 x y)). Qed.
Lemma lem2439928 (n : int) (x : int) (y : int) : (term280 n x y) = (term281 n x y).
Proof. exact (@lem1982755 (real_of_int n) term132 (term278 x y)). Qed.
Lemma lem2439929 (x : int) (y : int) : (term282 x y) = (term283 x y).
Proof. exact (@lem1982757 (term201 x) term132 (real_of_int y)). Qed.
Lemma lem2439930 (y : int) : (term284 y) = (term251 y).
Proof. exact (@lem1982761 (real_of_int y) term132). Qed.
Lemma lem2439931 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2439932 (x : int) (y : int) : (term283 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem2439931 x) (@lem2439930 y)). Qed.
Lemma lem2439933 (x : int) (y : int) : (term282 x y) = (term200 x y).
Proof. exact (TRANS (@lem2439929 x y) (@lem2439932 x y)). Qed.
Lemma lem2439934 (n : int) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem2439935 (n : int) (x : int) (y : int) : (term281 n x y) = (term285 n x y).
Proof. exact (MK_COMB (@lem2439934 n) (@lem2439933 x y)). Qed.
Lemma lem2439936 (n : int) (x : int) (y : int) : (term280 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2439928 n x y) (@lem2439935 n x y)). Qed.
Lemma lem2439937 (n : int) (x : int) (y : int) : (term279 n x y) = (term285 n x y).
Proof. exact (TRANS (@lem2439927 n x y) (@lem2439936 n x y)). Qed.
Lemma lem2439938 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2439939 (n : int) (x : int) (y : int) : (term286 n x y) = (term287 n x y).
Proof. exact (MK_COMB (@lem2439938) (@lem2439937 n x y)). Qed.
Lemma lem2439940 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2439941 (n : int) (x : int) (y : int) : (term288 n x y) = (term289 n x y).
Proof. exact (MK_COMB (@lem2439939 n x y) (@lem2439940)). Qed.
Lemma lem2439942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439943 (n : int) (x : int) (y : int) : (term290 n x y) = (term291 n x y).
Proof. exact (MK_COMB (@lem2439942) (@lem2439941 n x y)). Qed.
Lemma lem2439944 (n : int) (x : int) (y : int) : (term250 n x y) = (term292 n x y).
Proof. exact (MK_COMB (@lem2439943 n x y) (@lem2439850 n x y)). Qed.
Lemma lem2439945 (n : int) (x : int) (y : int) : (term162 x y n) = (term292 n x y).
Proof. exact (TRANS (@lem2439807 n x y) (@lem2439944 n x y)). Qed.
Lemma lem2439946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2439947 (n : int) (x : int) (y : int) : (term212 x y n) = (term293 n x y).
Proof. exact (MK_COMB (@lem2439946) (@lem2439945 n x y)). Qed.
Lemma lem2439948 (n : int) (x : int) (y : int) : (term240 n x y) = (term240 n x y).
Proof. exact (eq_refl (term240 n x y)). Qed.
Lemma lem2439951 (n : int) (x : int) (y : int) : (term489 n x y) = (term490 n x y).
Proof. exact (MK_COMB (@lem2439947 n x y) (@lem2439948 n x y)). Qed.
Lemma lem2439952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2439953 (n : int) (x : int) (y : int) : (term491 n x y) = (term492 n x y).
Proof. exact (MK_COMB (@lem2439952) (@lem2439804 n x y)). Qed.
Lemma lem2439954 (n : int) (x : int) (y : int) : (term238 n x y) = (term493 n x y).
Proof. exact (MK_COMB (@lem2439953 n x y) (@lem2439951 n x y)). Qed.
Lemma lem2439955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2439956 (n : int) (x : int) (y : int) : (term246 n x y) = (term494 n x y).
Proof. exact (MK_COMB (@lem2439955) (@lem2439450 n x y)). Qed.
Lemma lem2439957 (n : int) (x : int) (y : int) : (term247 n x y) = (term495 n x y).
Proof. exact (MK_COMB (@lem2439956 n x y) (@lem2439954 n x y)). Qed.
Lemma lem2439958 (n : int) (x : int) (y : int) (h1 : term495 n x y) : term495 n x y.
Proof. exact (h1). Qed.
Lemma lem2439959 (n : int) (x : int) (y : int) (h1 : term449 n x y) : term449 n x y.
Proof. exact (h1). Qed.
Lemma lem2439960 (n : int) (x : int) (y : int) (h1 : term444 n x y) : term444 n x y.
Proof. exact (h1). Qed.
Lemma lem2439961 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term387 n x y.
Proof. exact (h1). Qed.
Lemma lem2439962 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term386 n x y.
Proof. exact (proj2 (@lem2439961 n x y h1)). Qed.
Lemma lem2439964 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term385 n x y.
Proof. exact (proj2 (@lem2439962 n x y h1)). Qed.
Lemma lem2439965 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term292 n x y.
Proof. exact (proj1 (@lem2439962 n x y h1)). Qed.
Lemma lem2439967 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term289 n x y.
Proof. exact (proj1 (@lem2439965 n x y h1)). Qed.
Lemma lem2439968 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term383 n x y.
Proof. exact (proj2 (@lem2439964 n x y h1)). Qed.
Lemma lem2439971 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term373 n x y.
Proof. exact (proj1 (@lem2439968 n x y h1)). Qed.
Lemma lem2439973 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term355 n x y.
Proof. exact (proj1 (@lem2439971 n x y h1)). Qed.
Lemma lem2439975 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2439976 : term496 = term497.
Proof. exact (@lem2439975 term95 term80). Qed.
Lemma lem2439978 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2439979 : term80 = term134.
Proof. exact (@lem2439978 term81). Qed.
Lemma lem2439981 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2439982 : term95 = term179.
Proof. exact (@lem2439981 (NUMERAL 0)). Qed.
Lemma lem2439983 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2439984 : term498 = term499.
Proof. exact (MK_COMB (@lem2439983) (@lem2439982)). Qed.
Lemma lem2439985 : term497 = term500.
Proof. exact (MK_COMB (@lem2439984) (@lem2439979)). Qed.
Lemma lem2439986 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2439988 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2439989 : term497 = term503.
Proof. exact (@lem2439988 (NUMERAL 0) term81). Qed.
Lemma lem2439990 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2439991 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2439992 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2439991 h1) (fun h1 : term503 = True => @lem2439990)). Qed.
Lemma lem2439993 : term503 = True.
Proof. exact (EQ_MP (@lem2439992) (@lem2439990)). Qed.
Lemma lem2439994 : term497 = True.
Proof. exact (TRANS (@lem2439989) (@lem2439993)). Qed.
Lemma lem2439995 : True = term497.
Proof. exact (SYM (@lem2439994)). Qed.
Lemma lem2439996 : term497.
Proof. exact (EQ_MP (@lem2439995) (@lem0)). Qed.
Lemma lem2439997 : term505.
Proof. exact (@lem2439986 (@lem2439996)). Qed.
Lemma lem2439999 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440000 : term497 = term503.
Proof. exact (@lem2439999 (NUMERAL 0) term81). Qed.
Lemma lem2440001 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440002 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440003 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440002 h1) (fun h1 : term503 = True => @lem2440001)). Qed.
Lemma lem2440004 : term503 = True.
Proof. exact (EQ_MP (@lem2440003) (@lem2440001)). Qed.
Lemma lem2440005 : term497 = True.
Proof. exact (TRANS (@lem2440000) (@lem2440004)). Qed.
Lemma lem2440006 : True = term497.
Proof. exact (SYM (@lem2440005)). Qed.
Lemma lem2440007 : term497.
Proof. exact (EQ_MP (@lem2440006) (@lem0)). Qed.
Lemma lem2440008 : term500 = term506.
Proof. exact (@lem2439997 (@lem2440007)). Qed.
Lemma lem2440010 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440011 : term145 = term146.
Proof. exact (@lem2440010 term81 term81). Qed.
Lemma lem2440012 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440013 : term148 = term81.
Proof. exact (EQ_MP (@lem2440012) (@lem940073)). Qed.
Lemma lem2440014 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440015 : term146 = term80.
Proof. exact (MK_COMB (@lem2440014) (@lem2440013)). Qed.
Lemma lem2440016 : term145 = term80.
Proof. exact (TRANS (@lem2440011) (@lem2440015)). Qed.
Lemma lem2440018 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440019 : term508 = term95.
Proof. exact (@lem2440018 term81). Qed.
Lemma lem2440020 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2440021 : term509 = term498.
Proof. exact (MK_COMB (@lem2440020) (@lem2440019)). Qed.
Lemma lem2440022 : term506 = term497.
Proof. exact (MK_COMB (@lem2440021) (@lem2440016)). Qed.
Lemma lem2440024 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440025 : term497 = term503.
Proof. exact (@lem2440024 (NUMERAL 0) term81). Qed.
Lemma lem2440026 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440027 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440028 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440027 h1) (fun h1 : term503 = True => @lem2440026)). Qed.
Lemma lem2440029 : term503 = True.
Proof. exact (EQ_MP (@lem2440028) (@lem2440026)). Qed.
Lemma lem2440030 : term497 = True.
Proof. exact (TRANS (@lem2440025) (@lem2440029)). Qed.
Lemma lem2440031 : term506 = True.
Proof. exact (TRANS (@lem2440022) (@lem2440030)). Qed.
Lemma lem2440032 : term500 = True.
Proof. exact (TRANS (@lem2440008) (@lem2440031)). Qed.
Lemma lem2440033 : term497 = True.
Proof. exact (TRANS (@lem2439985) (@lem2440032)). Qed.
Lemma lem2440034 : term496 = True.
Proof. exact (TRANS (@lem2439976) (@lem2440033)). Qed.
Lemma lem2440035 : True = term496.
Proof. exact (SYM (@lem2440034)). Qed.
Lemma lem2440036 : term496.
Proof. exact (EQ_MP (@lem2440035) (@lem0)). Qed.
Lemma lem2440037 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term510 n x y.
Proof. exact (conj (@lem2440036) (@lem2439967 n x y h1)). Qed.
Lemma lem2440039 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2440040 (n : int) (x : int) (y : int) : term512 n x y.
Proof. exact (@lem2440039 term80 (term285 n x y)). Qed.
Lemma lem2440041 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term513 n x y.
Proof. exact (@lem2440040 n x y (@lem2440037 n x y h1)). Qed.
Lemma lem2440042 (n : int) (x : int) (y : int) : (term514 n x y) = (term285 n x y).
Proof. exact (@lem1982733 (term285 n x y)). Qed.
Lemma lem2440043 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2440044 (n : int) (x : int) (y : int) : (term515 n x y) = (term287 n x y).
Proof. exact (MK_COMB (@lem2440043) (@lem2440042 n x y)). Qed.
Lemma lem2440045 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2440046 (n : int) (x : int) (y : int) : (term513 n x y) = (term289 n x y).
Proof. exact (MK_COMB (@lem2440044 n x y) (@lem2440045)). Qed.
Lemma lem2440047 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term289 n x y.
Proof. exact (EQ_MP (@lem2440046 n x y) (@lem2440041 n x y h1)). Qed.
Lemma lem2440049 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2440050 : term496 = term497.
Proof. exact (@lem2440049 term95 term80). Qed.
Lemma lem2440052 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440053 : term80 = term134.
Proof. exact (@lem2440052 term81). Qed.
Lemma lem2440055 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440056 : term95 = term179.
Proof. exact (@lem2440055 (NUMERAL 0)). Qed.
Lemma lem2440057 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2440058 : term498 = term499.
Proof. exact (MK_COMB (@lem2440057) (@lem2440056)). Qed.
Lemma lem2440059 : term497 = term500.
Proof. exact (MK_COMB (@lem2440058) (@lem2440053)). Qed.
Lemma lem2440060 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2440062 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440063 : term497 = term503.
Proof. exact (@lem2440062 (NUMERAL 0) term81). Qed.
Lemma lem2440064 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440065 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440066 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440065 h1) (fun h1 : term503 = True => @lem2440064)). Qed.
Lemma lem2440067 : term503 = True.
Proof. exact (EQ_MP (@lem2440066) (@lem2440064)). Qed.
Lemma lem2440068 : term497 = True.
Proof. exact (TRANS (@lem2440063) (@lem2440067)). Qed.
Lemma lem2440069 : True = term497.
Proof. exact (SYM (@lem2440068)). Qed.
Lemma lem2440070 : term497.
Proof. exact (EQ_MP (@lem2440069) (@lem0)). Qed.
Lemma lem2440071 : term505.
Proof. exact (@lem2440060 (@lem2440070)). Qed.
Lemma lem2440073 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440074 : term497 = term503.
Proof. exact (@lem2440073 (NUMERAL 0) term81). Qed.
Lemma lem2440075 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440076 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440077 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440076 h1) (fun h1 : term503 = True => @lem2440075)). Qed.
Lemma lem2440078 : term503 = True.
Proof. exact (EQ_MP (@lem2440077) (@lem2440075)). Qed.
Lemma lem2440079 : term497 = True.
Proof. exact (TRANS (@lem2440074) (@lem2440078)). Qed.
Lemma lem2440080 : True = term497.
Proof. exact (SYM (@lem2440079)). Qed.
Lemma lem2440081 : term497.
Proof. exact (EQ_MP (@lem2440080) (@lem0)). Qed.
Lemma lem2440082 : term500 = term506.
Proof. exact (@lem2440071 (@lem2440081)). Qed.
Lemma lem2440084 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440085 : term145 = term146.
Proof. exact (@lem2440084 term81 term81). Qed.
Lemma lem2440086 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440087 : term148 = term81.
Proof. exact (EQ_MP (@lem2440086) (@lem940073)). Qed.
Lemma lem2440088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440089 : term146 = term80.
Proof. exact (MK_COMB (@lem2440088) (@lem2440087)). Qed.
Lemma lem2440090 : term145 = term80.
Proof. exact (TRANS (@lem2440085) (@lem2440089)). Qed.
Lemma lem2440092 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440093 : term508 = term95.
Proof. exact (@lem2440092 term81). Qed.
Lemma lem2440094 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2440095 : term509 = term498.
Proof. exact (MK_COMB (@lem2440094) (@lem2440093)). Qed.
Lemma lem2440096 : term506 = term497.
Proof. exact (MK_COMB (@lem2440095) (@lem2440090)). Qed.
Lemma lem2440098 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440099 : term497 = term503.
Proof. exact (@lem2440098 (NUMERAL 0) term81). Qed.
Lemma lem2440100 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440101 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440102 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440101 h1) (fun h1 : term503 = True => @lem2440100)). Qed.
Lemma lem2440103 : term503 = True.
Proof. exact (EQ_MP (@lem2440102) (@lem2440100)). Qed.
Lemma lem2440104 : term497 = True.
Proof. exact (TRANS (@lem2440099) (@lem2440103)). Qed.
Lemma lem2440105 : term506 = True.
Proof. exact (TRANS (@lem2440096) (@lem2440104)). Qed.
Lemma lem2440106 : term500 = True.
Proof. exact (TRANS (@lem2440082) (@lem2440105)). Qed.
Lemma lem2440107 : term497 = True.
Proof. exact (TRANS (@lem2440059) (@lem2440106)). Qed.
Lemma lem2440108 : term496 = True.
Proof. exact (TRANS (@lem2440050) (@lem2440107)). Qed.
Lemma lem2440109 : True = term496.
Proof. exact (SYM (@lem2440108)). Qed.
Lemma lem2440110 : term496.
Proof. exact (EQ_MP (@lem2440109) (@lem0)). Qed.
Lemma lem2440111 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term516 n x y.
Proof. exact (conj (@lem2440110) (@lem2439973 n x y h1)). Qed.
Lemma lem2440113 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2440114 (n : int) (x : int) (y : int) : term517 n x y.
Proof. exact (@lem2440113 term80 (term345 n x y)). Qed.
Lemma lem2440115 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term518 n x y.
Proof. exact (@lem2440114 n x y (@lem2440111 n x y h1)). Qed.
Lemma lem2440116 (n : int) (x : int) (y : int) : (term519 n x y) = (term345 n x y).
Proof. exact (@lem1982733 (term345 n x y)). Qed.
Lemma lem2440117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2440118 (n : int) (x : int) (y : int) : (term520 n x y) = (term354 n x y).
Proof. exact (MK_COMB (@lem2440117) (@lem2440116 n x y)). Qed.
Lemma lem2440119 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2440120 (n : int) (x : int) (y : int) : (term518 n x y) = (term355 n x y).
Proof. exact (MK_COMB (@lem2440118 n x y) (@lem2440119)). Qed.
Lemma lem2440121 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term355 n x y.
Proof. exact (EQ_MP (@lem2440120 n x y) (@lem2440115 n x y h1)). Qed.
Lemma lem2440122 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term521 n x y.
Proof. exact (conj (@lem2440121 n x y h1) (@lem2440047 n x y h1)). Qed.
Lemma lem2440124 (x : real) (y : real) : term522 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2440125 (n : int) (x : int) (y : int) : term523 n x y.
Proof. exact (@lem2440124 (term345 n x y) (term285 n x y)). Qed.
Lemma lem2440126 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term524 n x y.
Proof. exact (@lem2440125 n x y (@lem2440122 n x y h1)). Qed.
Lemma lem2440127 (n : int) (x : int) (y : int) : (term525 n x y) = (term526 n x y).
Proof. exact (@lem1982753 (term201 n) (real_of_int n) (term122 x y) (term200 x y)). Qed.
Lemma lem2440128 (n : int) : (term527 n) = (term528 n).
Proof. exact (@lem1982713 term132 (real_of_int n)). Qed.
Lemma lem2440130 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440131 : term80 = term134.
Proof. exact (@lem2440130 term81). Qed.
Lemma lem2440133 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2440134 : term132 = term137.
Proof. exact (@lem2440133 term81). Qed.
Lemma lem2440135 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440136 : term529 = term530.
Proof. exact (MK_COMB (@lem2440135) (@lem2440134)). Qed.
Lemma lem2440137 : term531 = term532.
Proof. exact (MK_COMB (@lem2440136) (@lem2440131)). Qed.
Lemma lem2440138 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2440140 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440141 : term497 = term503.
Proof. exact (@lem2440140 (NUMERAL 0) term81). Qed.
Lemma lem2440142 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440143 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440144 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440143 h1) (fun h1 : term503 = True => @lem2440142)). Qed.
Lemma lem2440145 : term503 = True.
Proof. exact (EQ_MP (@lem2440144) (@lem2440142)). Qed.
Lemma lem2440146 : term497 = True.
Proof. exact (TRANS (@lem2440141) (@lem2440145)). Qed.
Lemma lem2440147 : True = term497.
Proof. exact (SYM (@lem2440146)). Qed.
Lemma lem2440148 : term497.
Proof. exact (EQ_MP (@lem2440147) (@lem0)). Qed.
Lemma lem2440149 : term534.
Proof. exact (@lem2440138 (@lem2440148)). Qed.
Lemma lem2440151 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440152 : term497 = term503.
Proof. exact (@lem2440151 (NUMERAL 0) term81). Qed.
Lemma lem2440153 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440154 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440155 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440154 h1) (fun h1 : term503 = True => @lem2440153)). Qed.
Lemma lem2440156 : term503 = True.
Proof. exact (EQ_MP (@lem2440155) (@lem2440153)). Qed.
Lemma lem2440157 : term497 = True.
Proof. exact (TRANS (@lem2440152) (@lem2440156)). Qed.
Lemma lem2440158 : True = term497.
Proof. exact (SYM (@lem2440157)). Qed.
Lemma lem2440159 : term497.
Proof. exact (EQ_MP (@lem2440158) (@lem0)). Qed.
Lemma lem2440160 : term535.
Proof. exact (@lem2440149 (@lem2440159)). Qed.
Lemma lem2440162 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440163 : term497 = term503.
Proof. exact (@lem2440162 (NUMERAL 0) term81). Qed.
Lemma lem2440164 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440165 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440166 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440165 h1) (fun h1 : term503 = True => @lem2440164)). Qed.
Lemma lem2440167 : term503 = True.
Proof. exact (EQ_MP (@lem2440166) (@lem2440164)). Qed.
Lemma lem2440168 : term497 = True.
Proof. exact (TRANS (@lem2440163) (@lem2440167)). Qed.
Lemma lem2440169 : True = term497.
Proof. exact (SYM (@lem2440168)). Qed.
Lemma lem2440170 : term497.
Proof. exact (EQ_MP (@lem2440169) (@lem0)). Qed.
Lemma lem2440171 : term536.
Proof. exact (@lem2440160 (@lem2440170)). Qed.
Lemma lem2440173 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440174 : term145 = term146.
Proof. exact (@lem2440173 term81 term81). Qed.
Lemma lem2440175 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440176 : term148 = term81.
Proof. exact (EQ_MP (@lem2440175) (@lem940073)). Qed.
Lemma lem2440177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440178 : term146 = term80.
Proof. exact (MK_COMB (@lem2440177) (@lem2440176)). Qed.
Lemma lem2440179 : term145 = term80.
Proof. exact (TRANS (@lem2440174) (@lem2440178)). Qed.
Lemma lem2440181 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2440182 : term140 = term151.
Proof. exact (@lem2440181 term81 term81). Qed.
Lemma lem2440183 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440184 : term148 = term81.
Proof. exact (EQ_MP (@lem2440183) (@lem940073)). Qed.
Lemma lem2440185 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440186 : term146 = term80.
Proof. exact (MK_COMB (@lem2440185) (@lem2440184)). Qed.
Lemma lem2440187 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2440188 : term151 = term132.
Proof. exact (MK_COMB (@lem2440187) (@lem2440186)). Qed.
Lemma lem2440189 : term140 = term132.
Proof. exact (TRANS (@lem2440182) (@lem2440188)). Qed.
Lemma lem2440190 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440191 : term537 = term529.
Proof. exact (MK_COMB (@lem2440190) (@lem2440189)). Qed.
Lemma lem2440192 : term538 = term531.
Proof. exact (MK_COMB (@lem2440191) (@lem2440179)). Qed.
Lemma lem2440194 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2440195 : term531 = term95.
Proof. exact (@lem2440194 term81). Qed.
Lemma lem2440196 : term538 = term95.
Proof. exact (TRANS (@lem2440192) (@lem2440195)). Qed.
Lemma lem2440197 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440198 : term540 = term541.
Proof. exact (MK_COMB (@lem2440197) (@lem2440196)). Qed.
Lemma lem2440199 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2440200 : term542 = term508.
Proof. exact (MK_COMB (@lem2440198) (@lem2440199)). Qed.
Lemma lem2440202 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440203 : term508 = term95.
Proof. exact (@lem2440202 term81). Qed.
Lemma lem2440204 : term542 = term95.
Proof. exact (TRANS (@lem2440200) (@lem2440203)). Qed.
Lemma lem2440206 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440207 : term145 = term146.
Proof. exact (@lem2440206 term81 term81). Qed.
Lemma lem2440208 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440209 : term148 = term81.
Proof. exact (EQ_MP (@lem2440208) (@lem940073)). Qed.
Lemma lem2440210 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440211 : term146 = term80.
Proof. exact (MK_COMB (@lem2440210) (@lem2440209)). Qed.
Lemma lem2440212 : term145 = term80.
Proof. exact (TRANS (@lem2440207) (@lem2440211)). Qed.
Lemma lem2440213 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2440214 : term543 = term508.
Proof. exact (MK_COMB (@lem2440213) (@lem2440212)). Qed.
Lemma lem2440216 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440217 : term508 = term95.
Proof. exact (@lem2440216 term81). Qed.
Lemma lem2440218 : term543 = term95.
Proof. exact (TRANS (@lem2440214) (@lem2440217)). Qed.
Lemma lem2440219 : term95 = term543.
Proof. exact (SYM (@lem2440218)). Qed.
Lemma lem2440220 : term542 = term543.
Proof. exact (TRANS (@lem2440204) (@lem2440219)). Qed.
Lemma lem2440221 : term532 = term179.
Proof. exact (@lem2440171 (@lem2440220)). Qed.
Lemma lem2440222 : term531 = term179.
Proof. exact (TRANS (@lem2440137) (@lem2440221)). Qed.
Lemma lem2440224 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2440225 : term179 = term95.
Proof. exact (@lem2440224 term95). Qed.
Lemma lem2440226 : term531 = term95.
Proof. exact (TRANS (@lem2440222) (@lem2440225)). Qed.
Lemma lem2440227 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440228 : term544 = term541.
Proof. exact (MK_COMB (@lem2440227) (@lem2440226)). Qed.
Lemma lem2440229 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2440230 (n : int) : (term528 n) = (term545 n).
Proof. exact (MK_COMB (@lem2440228) (@lem2440229 n)). Qed.
Lemma lem2440231 (n : int) : (term527 n) = (term545 n).
Proof. exact (TRANS (@lem2440128 n) (@lem2440230 n)). Qed.
Lemma lem2440232 (n : int) : (term545 n) = term95.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2440233 (n : int) : (term527 n) = term95.
Proof. exact (TRANS (@lem2440231 n) (@lem2440232 n)). Qed.
Lemma lem2440234 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440235 (n : int) : (term546 n) = term392.
Proof. exact (MK_COMB (@lem2440234) (@lem2440233 n)). Qed.
Lemma lem2440236 (x : int) (y : int) : (term547 x y) = (term548 x y).
Proof. exact (@lem1982753 (real_of_int x) (term201 x) (term201 y) (term251 y)). Qed.
Lemma lem2440237 (x : int) : (term549 x) = (term528 x).
Proof. exact (@lem1982715 term132 (real_of_int x)). Qed.
Lemma lem2440239 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440240 : term80 = term134.
Proof. exact (@lem2440239 term81). Qed.
Lemma lem2440242 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2440243 : term132 = term137.
Proof. exact (@lem2440242 term81). Qed.
Lemma lem2440244 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440245 : term529 = term530.
Proof. exact (MK_COMB (@lem2440244) (@lem2440243)). Qed.
Lemma lem2440246 : term531 = term532.
Proof. exact (MK_COMB (@lem2440245) (@lem2440240)). Qed.
Lemma lem2440247 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2440249 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440250 : term497 = term503.
Proof. exact (@lem2440249 (NUMERAL 0) term81). Qed.
Lemma lem2440251 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440252 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440253 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440252 h1) (fun h1 : term503 = True => @lem2440251)). Qed.
Lemma lem2440254 : term503 = True.
Proof. exact (EQ_MP (@lem2440253) (@lem2440251)). Qed.
Lemma lem2440255 : term497 = True.
Proof. exact (TRANS (@lem2440250) (@lem2440254)). Qed.
Lemma lem2440256 : True = term497.
Proof. exact (SYM (@lem2440255)). Qed.
Lemma lem2440257 : term497.
Proof. exact (EQ_MP (@lem2440256) (@lem0)). Qed.
Lemma lem2440258 : term534.
Proof. exact (@lem2440247 (@lem2440257)). Qed.
Lemma lem2440260 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440261 : term497 = term503.
Proof. exact (@lem2440260 (NUMERAL 0) term81). Qed.
Lemma lem2440262 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440263 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440264 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440263 h1) (fun h1 : term503 = True => @lem2440262)). Qed.
Lemma lem2440265 : term503 = True.
Proof. exact (EQ_MP (@lem2440264) (@lem2440262)). Qed.
Lemma lem2440266 : term497 = True.
Proof. exact (TRANS (@lem2440261) (@lem2440265)). Qed.
Lemma lem2440267 : True = term497.
Proof. exact (SYM (@lem2440266)). Qed.
Lemma lem2440268 : term497.
Proof. exact (EQ_MP (@lem2440267) (@lem0)). Qed.
Lemma lem2440269 : term535.
Proof. exact (@lem2440258 (@lem2440268)). Qed.
Lemma lem2440271 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440272 : term497 = term503.
Proof. exact (@lem2440271 (NUMERAL 0) term81). Qed.
Lemma lem2440273 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440274 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440275 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440274 h1) (fun h1 : term503 = True => @lem2440273)). Qed.
Lemma lem2440276 : term503 = True.
Proof. exact (EQ_MP (@lem2440275) (@lem2440273)). Qed.
Lemma lem2440277 : term497 = True.
Proof. exact (TRANS (@lem2440272) (@lem2440276)). Qed.
Lemma lem2440278 : True = term497.
Proof. exact (SYM (@lem2440277)). Qed.
Lemma lem2440279 : term497.
Proof. exact (EQ_MP (@lem2440278) (@lem0)). Qed.
Lemma lem2440280 : term536.
Proof. exact (@lem2440269 (@lem2440279)). Qed.
Lemma lem2440282 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440283 : term145 = term146.
Proof. exact (@lem2440282 term81 term81). Qed.
Lemma lem2440284 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440285 : term148 = term81.
Proof. exact (EQ_MP (@lem2440284) (@lem940073)). Qed.
Lemma lem2440286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440287 : term146 = term80.
Proof. exact (MK_COMB (@lem2440286) (@lem2440285)). Qed.
Lemma lem2440288 : term145 = term80.
Proof. exact (TRANS (@lem2440283) (@lem2440287)). Qed.
Lemma lem2440290 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2440291 : term140 = term151.
Proof. exact (@lem2440290 term81 term81). Qed.
Lemma lem2440292 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440293 : term148 = term81.
Proof. exact (EQ_MP (@lem2440292) (@lem940073)). Qed.
Lemma lem2440294 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440295 : term146 = term80.
Proof. exact (MK_COMB (@lem2440294) (@lem2440293)). Qed.
Lemma lem2440296 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2440297 : term151 = term132.
Proof. exact (MK_COMB (@lem2440296) (@lem2440295)). Qed.
Lemma lem2440298 : term140 = term132.
Proof. exact (TRANS (@lem2440291) (@lem2440297)). Qed.
Lemma lem2440299 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440300 : term537 = term529.
Proof. exact (MK_COMB (@lem2440299) (@lem2440298)). Qed.
Lemma lem2440301 : term538 = term531.
Proof. exact (MK_COMB (@lem2440300) (@lem2440288)). Qed.
Lemma lem2440303 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2440304 : term531 = term95.
Proof. exact (@lem2440303 term81). Qed.
Lemma lem2440305 : term538 = term95.
Proof. exact (TRANS (@lem2440301) (@lem2440304)). Qed.
Lemma lem2440306 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440307 : term540 = term541.
Proof. exact (MK_COMB (@lem2440306) (@lem2440305)). Qed.
Lemma lem2440308 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2440309 : term542 = term508.
Proof. exact (MK_COMB (@lem2440307) (@lem2440308)). Qed.
Lemma lem2440311 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440312 : term508 = term95.
Proof. exact (@lem2440311 term81). Qed.
Lemma lem2440313 : term542 = term95.
Proof. exact (TRANS (@lem2440309) (@lem2440312)). Qed.
Lemma lem2440315 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440316 : term145 = term146.
Proof. exact (@lem2440315 term81 term81). Qed.
Lemma lem2440317 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440318 : term148 = term81.
Proof. exact (EQ_MP (@lem2440317) (@lem940073)). Qed.
Lemma lem2440319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440320 : term146 = term80.
Proof. exact (MK_COMB (@lem2440319) (@lem2440318)). Qed.
Lemma lem2440321 : term145 = term80.
Proof. exact (TRANS (@lem2440316) (@lem2440320)). Qed.
Lemma lem2440322 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2440323 : term543 = term508.
Proof. exact (MK_COMB (@lem2440322) (@lem2440321)). Qed.
Lemma lem2440325 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440326 : term508 = term95.
Proof. exact (@lem2440325 term81). Qed.
Lemma lem2440327 : term543 = term95.
Proof. exact (TRANS (@lem2440323) (@lem2440326)). Qed.
Lemma lem2440328 : term95 = term543.
Proof. exact (SYM (@lem2440327)). Qed.
Lemma lem2440329 : term542 = term543.
Proof. exact (TRANS (@lem2440313) (@lem2440328)). Qed.
Lemma lem2440330 : term532 = term179.
Proof. exact (@lem2440280 (@lem2440329)). Qed.
Lemma lem2440331 : term531 = term179.
Proof. exact (TRANS (@lem2440246) (@lem2440330)). Qed.
Lemma lem2440333 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2440334 : term179 = term95.
Proof. exact (@lem2440333 term95). Qed.
Lemma lem2440335 : term531 = term95.
Proof. exact (TRANS (@lem2440331) (@lem2440334)). Qed.
Lemma lem2440336 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440337 : term544 = term541.
Proof. exact (MK_COMB (@lem2440336) (@lem2440335)). Qed.
Lemma lem2440338 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2440339 (x : int) : (term528 x) = (term545 x).
Proof. exact (MK_COMB (@lem2440337) (@lem2440338 x)). Qed.
Lemma lem2440340 (x : int) : (term549 x) = (term545 x).
Proof. exact (TRANS (@lem2440237 x) (@lem2440339 x)). Qed.
Lemma lem2440341 (x : int) : (term545 x) = term95.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2440342 (x : int) : (term549 x) = term95.
Proof. exact (TRANS (@lem2440340 x) (@lem2440341 x)). Qed.
Lemma lem2440343 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440344 (x : int) : (term550 x) = term392.
Proof. exact (MK_COMB (@lem2440343) (@lem2440342 x)). Qed.
Lemma lem2440345 (y : int) : (term551 y) = (term552 y).
Proof. exact (@lem1982763 (term201 y) (real_of_int y) term132). Qed.
Lemma lem2440346 (y : int) : (term527 y) = (term528 y).
Proof. exact (@lem1982713 term132 (real_of_int y)). Qed.
Lemma lem2440348 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440349 : term80 = term134.
Proof. exact (@lem2440348 term81). Qed.
Lemma lem2440351 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2440352 : term132 = term137.
Proof. exact (@lem2440351 term81). Qed.
Lemma lem2440353 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440354 : term529 = term530.
Proof. exact (MK_COMB (@lem2440353) (@lem2440352)). Qed.
Lemma lem2440355 : term531 = term532.
Proof. exact (MK_COMB (@lem2440354) (@lem2440349)). Qed.
Lemma lem2440356 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2440358 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440359 : term497 = term503.
Proof. exact (@lem2440358 (NUMERAL 0) term81). Qed.
Lemma lem2440360 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440361 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440362 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440361 h1) (fun h1 : term503 = True => @lem2440360)). Qed.
Lemma lem2440363 : term503 = True.
Proof. exact (EQ_MP (@lem2440362) (@lem2440360)). Qed.
Lemma lem2440364 : term497 = True.
Proof. exact (TRANS (@lem2440359) (@lem2440363)). Qed.
Lemma lem2440365 : True = term497.
Proof. exact (SYM (@lem2440364)). Qed.
Lemma lem2440366 : term497.
Proof. exact (EQ_MP (@lem2440365) (@lem0)). Qed.
Lemma lem2440367 : term534.
Proof. exact (@lem2440356 (@lem2440366)). Qed.
Lemma lem2440369 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440370 : term497 = term503.
Proof. exact (@lem2440369 (NUMERAL 0) term81). Qed.
Lemma lem2440371 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440372 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440373 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440372 h1) (fun h1 : term503 = True => @lem2440371)). Qed.
Lemma lem2440374 : term503 = True.
Proof. exact (EQ_MP (@lem2440373) (@lem2440371)). Qed.
Lemma lem2440375 : term497 = True.
Proof. exact (TRANS (@lem2440370) (@lem2440374)). Qed.
Lemma lem2440376 : True = term497.
Proof. exact (SYM (@lem2440375)). Qed.
Lemma lem2440377 : term497.
Proof. exact (EQ_MP (@lem2440376) (@lem0)). Qed.
Lemma lem2440378 : term535.
Proof. exact (@lem2440367 (@lem2440377)). Qed.
Lemma lem2440380 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440381 : term497 = term503.
Proof. exact (@lem2440380 (NUMERAL 0) term81). Qed.
Lemma lem2440382 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440383 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440384 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440383 h1) (fun h1 : term503 = True => @lem2440382)). Qed.
Lemma lem2440385 : term503 = True.
Proof. exact (EQ_MP (@lem2440384) (@lem2440382)). Qed.
Lemma lem2440386 : term497 = True.
Proof. exact (TRANS (@lem2440381) (@lem2440385)). Qed.
Lemma lem2440387 : True = term497.
Proof. exact (SYM (@lem2440386)). Qed.
Lemma lem2440388 : term497.
Proof. exact (EQ_MP (@lem2440387) (@lem0)). Qed.
Lemma lem2440389 : term536.
Proof. exact (@lem2440378 (@lem2440388)). Qed.
Lemma lem2440391 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440392 : term145 = term146.
Proof. exact (@lem2440391 term81 term81). Qed.
Lemma lem2440393 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440394 : term148 = term81.
Proof. exact (EQ_MP (@lem2440393) (@lem940073)). Qed.
Lemma lem2440395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440396 : term146 = term80.
Proof. exact (MK_COMB (@lem2440395) (@lem2440394)). Qed.
Lemma lem2440397 : term145 = term80.
Proof. exact (TRANS (@lem2440392) (@lem2440396)). Qed.
Lemma lem2440399 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2440400 : term140 = term151.
Proof. exact (@lem2440399 term81 term81). Qed.
Lemma lem2440401 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440402 : term148 = term81.
Proof. exact (EQ_MP (@lem2440401) (@lem940073)). Qed.
Lemma lem2440403 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440404 : term146 = term80.
Proof. exact (MK_COMB (@lem2440403) (@lem2440402)). Qed.
Lemma lem2440405 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2440406 : term151 = term132.
Proof. exact (MK_COMB (@lem2440405) (@lem2440404)). Qed.
Lemma lem2440407 : term140 = term132.
Proof. exact (TRANS (@lem2440400) (@lem2440406)). Qed.
Lemma lem2440408 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440409 : term537 = term529.
Proof. exact (MK_COMB (@lem2440408) (@lem2440407)). Qed.
Lemma lem2440410 : term538 = term531.
Proof. exact (MK_COMB (@lem2440409) (@lem2440397)). Qed.
Lemma lem2440412 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2440413 : term531 = term95.
Proof. exact (@lem2440412 term81). Qed.
Lemma lem2440414 : term538 = term95.
Proof. exact (TRANS (@lem2440410) (@lem2440413)). Qed.
Lemma lem2440415 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440416 : term540 = term541.
Proof. exact (MK_COMB (@lem2440415) (@lem2440414)). Qed.
Lemma lem2440417 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2440418 : term542 = term508.
Proof. exact (MK_COMB (@lem2440416) (@lem2440417)). Qed.
Lemma lem2440420 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440421 : term508 = term95.
Proof. exact (@lem2440420 term81). Qed.
Lemma lem2440422 : term542 = term95.
Proof. exact (TRANS (@lem2440418) (@lem2440421)). Qed.
Lemma lem2440424 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440425 : term145 = term146.
Proof. exact (@lem2440424 term81 term81). Qed.
Lemma lem2440426 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440427 : term148 = term81.
Proof. exact (EQ_MP (@lem2440426) (@lem940073)). Qed.
Lemma lem2440428 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440429 : term146 = term80.
Proof. exact (MK_COMB (@lem2440428) (@lem2440427)). Qed.
Lemma lem2440430 : term145 = term80.
Proof. exact (TRANS (@lem2440425) (@lem2440429)). Qed.
Lemma lem2440431 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2440432 : term543 = term508.
Proof. exact (MK_COMB (@lem2440431) (@lem2440430)). Qed.
Lemma lem2440434 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440435 : term508 = term95.
Proof. exact (@lem2440434 term81). Qed.
Lemma lem2440436 : term543 = term95.
Proof. exact (TRANS (@lem2440432) (@lem2440435)). Qed.
Lemma lem2440437 : term95 = term543.
Proof. exact (SYM (@lem2440436)). Qed.
Lemma lem2440438 : term542 = term543.
Proof. exact (TRANS (@lem2440422) (@lem2440437)). Qed.
Lemma lem2440439 : term532 = term179.
Proof. exact (@lem2440389 (@lem2440438)). Qed.
Lemma lem2440440 : term531 = term179.
Proof. exact (TRANS (@lem2440355) (@lem2440439)). Qed.
Lemma lem2440442 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2440443 : term179 = term95.
Proof. exact (@lem2440442 term95). Qed.
Lemma lem2440444 : term531 = term95.
Proof. exact (TRANS (@lem2440440) (@lem2440443)). Qed.
Lemma lem2440445 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440446 : term544 = term541.
Proof. exact (MK_COMB (@lem2440445) (@lem2440444)). Qed.
Lemma lem2440447 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2440448 (y : int) : (term528 y) = (term545 y).
Proof. exact (MK_COMB (@lem2440446) (@lem2440447 y)). Qed.
Lemma lem2440449 (y : int) : (term527 y) = (term545 y).
Proof. exact (TRANS (@lem2440346 y) (@lem2440448 y)). Qed.
Lemma lem2440450 (y : int) : (term545 y) = term95.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2440451 (y : int) : (term527 y) = term95.
Proof. exact (TRANS (@lem2440449 y) (@lem2440450 y)). Qed.
Lemma lem2440452 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440453 (y : int) : (term546 y) = term392.
Proof. exact (MK_COMB (@lem2440452) (@lem2440451 y)). Qed.
Lemma lem2440454 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem2440455 (y : int) : (term552 y) = term553.
Proof. exact (MK_COMB (@lem2440453 y) (@lem2440454)). Qed.
Lemma lem2440456 (y : int) : (term551 y) = term553.
Proof. exact (TRANS (@lem2440345 y) (@lem2440455 y)). Qed.
Lemma lem2440457 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2440458 (y : int) : (term551 y) = term132.
Proof. exact (TRANS (@lem2440456 y) (@lem2440457)). Qed.
Lemma lem2440459 (x : int) (y : int) : (term548 x y) = term553.
Proof. exact (MK_COMB (@lem2440344 x) (@lem2440458 y)). Qed.
Lemma lem2440460 (x : int) (y : int) : (term547 x y) = term553.
Proof. exact (TRANS (@lem2440236 x y) (@lem2440459 x y)). Qed.
Lemma lem2440461 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2440462 (x : int) (y : int) : (term547 x y) = term132.
Proof. exact (TRANS (@lem2440460 x y) (@lem2440461)). Qed.
Lemma lem2440463 (n : int) (x : int) (y : int) : (term526 n x y) = term553.
Proof. exact (MK_COMB (@lem2440235 n) (@lem2440462 x y)). Qed.
Lemma lem2440464 (n : int) (x : int) (y : int) : (term525 n x y) = term553.
Proof. exact (TRANS (@lem2440127 n x y) (@lem2440463 n x y)). Qed.
Lemma lem2440465 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2440466 (n : int) (x : int) (y : int) : (term525 n x y) = term132.
Proof. exact (TRANS (@lem2440464 n x y) (@lem2440465)). Qed.
Lemma lem2440467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2440468 (n : int) (x : int) (y : int) : (term554 n x y) = term555.
Proof. exact (MK_COMB (@lem2440467) (@lem2440466 n x y)). Qed.
Lemma lem2440469 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2440470 (n : int) (x : int) (y : int) : (term524 n x y) = term556.
Proof. exact (MK_COMB (@lem2440468 n x y) (@lem2440469)). Qed.
Lemma lem2440471 (n : int) (x : int) (y : int) (h1 : term387 n x y) : term556.
Proof. exact (EQ_MP (@lem2440470 n x y) (@lem2440126 n x y h1)). Qed.
Lemma lem2440473 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2440474 : term556 = term557.
Proof. exact (@lem2440473 term95 term132). Qed.
Lemma lem2440476 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2440477 : term132 = term137.
Proof. exact (@lem2440476 term81). Qed.
Lemma lem2440479 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440480 : term95 = term179.
Proof. exact (@lem2440479 (NUMERAL 0)). Qed.
Lemma lem2440481 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2440482 : term558 = term559.
Proof. exact (MK_COMB (@lem2440481) (@lem2440480)). Qed.
Lemma lem2440483 : term557 = term560.
Proof. exact (MK_COMB (@lem2440482) (@lem2440477)). Qed.
Lemma lem2440484 : term561.
Proof. exact (@lem1980026 term95 term80 term132 term80). Qed.
Lemma lem2440486 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440487 : term497 = term503.
Proof. exact (@lem2440486 (NUMERAL 0) term81). Qed.
Lemma lem2440488 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440489 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440490 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440489 h1) (fun h1 : term503 = True => @lem2440488)). Qed.
Lemma lem2440491 : term503 = True.
Proof. exact (EQ_MP (@lem2440490) (@lem2440488)). Qed.
Lemma lem2440492 : term497 = True.
Proof. exact (TRANS (@lem2440487) (@lem2440491)). Qed.
Lemma lem2440493 : True = term497.
Proof. exact (SYM (@lem2440492)). Qed.
Lemma lem2440494 : term497.
Proof. exact (EQ_MP (@lem2440493) (@lem0)). Qed.
Lemma lem2440495 : term562.
Proof. exact (@lem2440484 (@lem2440494)). Qed.
Lemma lem2440497 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440498 : term497 = term503.
Proof. exact (@lem2440497 (NUMERAL 0) term81). Qed.
Lemma lem2440499 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440500 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440501 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440500 h1) (fun h1 : term503 = True => @lem2440499)). Qed.
Lemma lem2440502 : term503 = True.
Proof. exact (EQ_MP (@lem2440501) (@lem2440499)). Qed.
Lemma lem2440503 : term497 = True.
Proof. exact (TRANS (@lem2440498) (@lem2440502)). Qed.
Lemma lem2440504 : True = term497.
Proof. exact (SYM (@lem2440503)). Qed.
Lemma lem2440505 : term497.
Proof. exact (EQ_MP (@lem2440504) (@lem0)). Qed.
Lemma lem2440506 : term560 = term563.
Proof. exact (@lem2440495 (@lem2440505)). Qed.
Lemma lem2440508 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2440509 : term140 = term151.
Proof. exact (@lem2440508 term81 term81). Qed.
Lemma lem2440510 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440511 : term148 = term81.
Proof. exact (EQ_MP (@lem2440510) (@lem940073)). Qed.
Lemma lem2440512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440513 : term146 = term80.
Proof. exact (MK_COMB (@lem2440512) (@lem2440511)). Qed.
Lemma lem2440514 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2440515 : term151 = term132.
Proof. exact (MK_COMB (@lem2440514) (@lem2440513)). Qed.
Lemma lem2440516 : term140 = term132.
Proof. exact (TRANS (@lem2440509) (@lem2440515)). Qed.
Lemma lem2440518 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440519 : term508 = term95.
Proof. exact (@lem2440518 term81). Qed.
Lemma lem2440520 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2440521 : term564 = term558.
Proof. exact (MK_COMB (@lem2440520) (@lem2440519)). Qed.
Lemma lem2440522 : term563 = term557.
Proof. exact (MK_COMB (@lem2440521) (@lem2440516)). Qed.
Lemma lem2440524 (m : nat) (n : nat) : (term565 m n) = (term566 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2440525 : term557 = term567.
Proof. exact (@lem2440524 (NUMERAL 0) term81). Qed.
Lemma lem2440526 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440527 (h1 : term504 = (BIT1 0)) : (term81 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2440528 : (term504 = (BIT1 0)) = ((term81 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440527 h1) (fun h1 : (term81 = (NUMERAL 0)) = False => @lem2440526)). Qed.
Lemma lem2440529 : (term81 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2440528) (@lem2440526)). Qed.
Lemma lem2440530 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2440531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2440532 : term568 = (and True).
Proof. exact (MK_COMB (@lem2440531) (@lem2440530)). Qed.
Lemma lem2440533 : term567 = (True /\ False).
Proof. exact (MK_COMB (@lem2440532) (@lem2440529)). Qed.
Lemma lem2440535 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2440536 : term567 = False.
Proof. exact (TRANS (@lem2440533) (@lem2440535)). Qed.
Lemma lem2440537 : term557 = False.
Proof. exact (TRANS (@lem2440525) (@lem2440536)). Qed.
Lemma lem2440538 : term563 = False.
Proof. exact (TRANS (@lem2440522) (@lem2440537)). Qed.
Lemma lem2440539 : term560 = False.
Proof. exact (TRANS (@lem2440506) (@lem2440538)). Qed.
Lemma lem2440540 : term557 = False.
Proof. exact (TRANS (@lem2440483) (@lem2440539)). Qed.
Lemma lem2440541 : term556 = False.
Proof. exact (TRANS (@lem2440474) (@lem2440540)). Qed.
Lemma lem2440542 (n : int) (x : int) (y : int) (h1 : term387 n x y) : False.
Proof. exact (EQ_MP (@lem2440541) (@lem2440471 n x y h1)). Qed.
Lemma lem2440543 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term442 n x y.
Proof. exact (h1). Qed.
Lemma lem2440544 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term440 n x y.
Proof. exact (proj2 (@lem2440543 n x y h1)). Qed.
Lemma lem2440546 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term439 n x y.
Proof. exact (proj2 (@lem2440544 n x y h1)). Qed.
Lemma lem2440547 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term292 n x y.
Proof. exact (proj1 (@lem2440544 n x y h1)). Qed.
Lemma lem2440548 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term264 n x y.
Proof. exact (proj2 (@lem2440547 n x y h1)). Qed.
Lemma lem2440550 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term437 n x y.
Proof. exact (proj2 (@lem2440546 n x y h1)). Qed.
Lemma lem2440553 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term433 n x y.
Proof. exact (proj1 (@lem2440550 n x y h1)). Qed.
Lemma lem2440555 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term414 n x y.
Proof. exact (proj1 (@lem2440553 n x y h1)). Qed.
Lemma lem2440557 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2440558 : term496 = term497.
Proof. exact (@lem2440557 term95 term80). Qed.
Lemma lem2440560 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440561 : term80 = term134.
Proof. exact (@lem2440560 term81). Qed.
Lemma lem2440563 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440564 : term95 = term179.
Proof. exact (@lem2440563 (NUMERAL 0)). Qed.
Lemma lem2440565 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2440566 : term498 = term499.
Proof. exact (MK_COMB (@lem2440565) (@lem2440564)). Qed.
Lemma lem2440567 : term497 = term500.
Proof. exact (MK_COMB (@lem2440566) (@lem2440561)). Qed.
Lemma lem2440568 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2440570 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440571 : term497 = term503.
Proof. exact (@lem2440570 (NUMERAL 0) term81). Qed.
Lemma lem2440572 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440573 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440574 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440573 h1) (fun h1 : term503 = True => @lem2440572)). Qed.
Lemma lem2440575 : term503 = True.
Proof. exact (EQ_MP (@lem2440574) (@lem2440572)). Qed.
Lemma lem2440576 : term497 = True.
Proof. exact (TRANS (@lem2440571) (@lem2440575)). Qed.
Lemma lem2440577 : True = term497.
Proof. exact (SYM (@lem2440576)). Qed.
Lemma lem2440578 : term497.
Proof. exact (EQ_MP (@lem2440577) (@lem0)). Qed.
Lemma lem2440579 : term505.
Proof. exact (@lem2440568 (@lem2440578)). Qed.
Lemma lem2440581 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440582 : term497 = term503.
Proof. exact (@lem2440581 (NUMERAL 0) term81). Qed.
Lemma lem2440583 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440584 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440585 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440584 h1) (fun h1 : term503 = True => @lem2440583)). Qed.
Lemma lem2440586 : term503 = True.
Proof. exact (EQ_MP (@lem2440585) (@lem2440583)). Qed.
Lemma lem2440587 : term497 = True.
Proof. exact (TRANS (@lem2440582) (@lem2440586)). Qed.
Lemma lem2440588 : True = term497.
Proof. exact (SYM (@lem2440587)). Qed.
Lemma lem2440589 : term497.
Proof. exact (EQ_MP (@lem2440588) (@lem0)). Qed.
Lemma lem2440590 : term500 = term506.
Proof. exact (@lem2440579 (@lem2440589)). Qed.
Lemma lem2440592 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440593 : term145 = term146.
Proof. exact (@lem2440592 term81 term81). Qed.
Lemma lem2440594 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440595 : term148 = term81.
Proof. exact (EQ_MP (@lem2440594) (@lem940073)). Qed.
Lemma lem2440596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440597 : term146 = term80.
Proof. exact (MK_COMB (@lem2440596) (@lem2440595)). Qed.
Lemma lem2440598 : term145 = term80.
Proof. exact (TRANS (@lem2440593) (@lem2440597)). Qed.
Lemma lem2440600 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440601 : term508 = term95.
Proof. exact (@lem2440600 term81). Qed.
Lemma lem2440602 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2440603 : term509 = term498.
Proof. exact (MK_COMB (@lem2440602) (@lem2440601)). Qed.
Lemma lem2440604 : term506 = term497.
Proof. exact (MK_COMB (@lem2440603) (@lem2440598)). Qed.
Lemma lem2440606 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440607 : term497 = term503.
Proof. exact (@lem2440606 (NUMERAL 0) term81). Qed.
Lemma lem2440608 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440609 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440610 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440609 h1) (fun h1 : term503 = True => @lem2440608)). Qed.
Lemma lem2440611 : term503 = True.
Proof. exact (EQ_MP (@lem2440610) (@lem2440608)). Qed.
Lemma lem2440612 : term497 = True.
Proof. exact (TRANS (@lem2440607) (@lem2440611)). Qed.
Lemma lem2440613 : term506 = True.
Proof. exact (TRANS (@lem2440604) (@lem2440612)). Qed.
Lemma lem2440614 : term500 = True.
Proof. exact (TRANS (@lem2440590) (@lem2440613)). Qed.
Lemma lem2440615 : term497 = True.
Proof. exact (TRANS (@lem2440567) (@lem2440614)). Qed.
Lemma lem2440616 : term496 = True.
Proof. exact (TRANS (@lem2440558) (@lem2440615)). Qed.
Lemma lem2440617 : True = term496.
Proof. exact (SYM (@lem2440616)). Qed.
Lemma lem2440618 : term496.
Proof. exact (EQ_MP (@lem2440617) (@lem0)). Qed.
Lemma lem2440619 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term569 n x y.
Proof. exact (conj (@lem2440618) (@lem2440548 n x y h1)). Qed.
Lemma lem2440621 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2440622 (n : int) (x : int) (y : int) : term570 n x y.
Proof. exact (@lem2440621 term80 (term260 n x y)). Qed.
Lemma lem2440623 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term571 n x y.
Proof. exact (@lem2440622 n x y (@lem2440619 n x y h1)). Qed.
Lemma lem2440624 (n : int) (x : int) (y : int) : (term572 n x y) = (term260 n x y).
Proof. exact (@lem1982733 (term260 n x y)). Qed.
Lemma lem2440625 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2440626 (n : int) (x : int) (y : int) : (term573 n x y) = (term262 n x y).
Proof. exact (MK_COMB (@lem2440625) (@lem2440624 n x y)). Qed.
Lemma lem2440627 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2440628 (n : int) (x : int) (y : int) : (term571 n x y) = (term264 n x y).
Proof. exact (MK_COMB (@lem2440626 n x y) (@lem2440627)). Qed.
Lemma lem2440629 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term264 n x y.
Proof. exact (EQ_MP (@lem2440628 n x y) (@lem2440623 n x y h1)). Qed.
Lemma lem2440631 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2440632 : term496 = term497.
Proof. exact (@lem2440631 term95 term80). Qed.
Lemma lem2440634 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440635 : term80 = term134.
Proof. exact (@lem2440634 term81). Qed.
Lemma lem2440637 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440638 : term95 = term179.
Proof. exact (@lem2440637 (NUMERAL 0)). Qed.
Lemma lem2440639 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2440640 : term498 = term499.
Proof. exact (MK_COMB (@lem2440639) (@lem2440638)). Qed.
Lemma lem2440641 : term497 = term500.
Proof. exact (MK_COMB (@lem2440640) (@lem2440635)). Qed.
Lemma lem2440642 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2440644 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440645 : term497 = term503.
Proof. exact (@lem2440644 (NUMERAL 0) term81). Qed.
Lemma lem2440646 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440647 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440648 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440647 h1) (fun h1 : term503 = True => @lem2440646)). Qed.
Lemma lem2440649 : term503 = True.
Proof. exact (EQ_MP (@lem2440648) (@lem2440646)). Qed.
Lemma lem2440650 : term497 = True.
Proof. exact (TRANS (@lem2440645) (@lem2440649)). Qed.
Lemma lem2440651 : True = term497.
Proof. exact (SYM (@lem2440650)). Qed.
Lemma lem2440652 : term497.
Proof. exact (EQ_MP (@lem2440651) (@lem0)). Qed.
Lemma lem2440653 : term505.
Proof. exact (@lem2440642 (@lem2440652)). Qed.
Lemma lem2440655 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440656 : term497 = term503.
Proof. exact (@lem2440655 (NUMERAL 0) term81). Qed.
Lemma lem2440657 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440658 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440659 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440658 h1) (fun h1 : term503 = True => @lem2440657)). Qed.
Lemma lem2440660 : term503 = True.
Proof. exact (EQ_MP (@lem2440659) (@lem2440657)). Qed.
Lemma lem2440661 : term497 = True.
Proof. exact (TRANS (@lem2440656) (@lem2440660)). Qed.
Lemma lem2440662 : True = term497.
Proof. exact (SYM (@lem2440661)). Qed.
Lemma lem2440663 : term497.
Proof. exact (EQ_MP (@lem2440662) (@lem0)). Qed.
Lemma lem2440664 : term500 = term506.
Proof. exact (@lem2440653 (@lem2440663)). Qed.
Lemma lem2440666 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440667 : term145 = term146.
Proof. exact (@lem2440666 term81 term81). Qed.
Lemma lem2440668 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440669 : term148 = term81.
Proof. exact (EQ_MP (@lem2440668) (@lem940073)). Qed.
Lemma lem2440670 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440671 : term146 = term80.
Proof. exact (MK_COMB (@lem2440670) (@lem2440669)). Qed.
Lemma lem2440672 : term145 = term80.
Proof. exact (TRANS (@lem2440667) (@lem2440671)). Qed.
Lemma lem2440674 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440675 : term508 = term95.
Proof. exact (@lem2440674 term81). Qed.
Lemma lem2440676 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2440677 : term509 = term498.
Proof. exact (MK_COMB (@lem2440676) (@lem2440675)). Qed.
Lemma lem2440678 : term506 = term497.
Proof. exact (MK_COMB (@lem2440677) (@lem2440672)). Qed.
Lemma lem2440680 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440681 : term497 = term503.
Proof. exact (@lem2440680 (NUMERAL 0) term81). Qed.
Lemma lem2440682 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440683 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440684 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440683 h1) (fun h1 : term503 = True => @lem2440682)). Qed.
Lemma lem2440685 : term503 = True.
Proof. exact (EQ_MP (@lem2440684) (@lem2440682)). Qed.
Lemma lem2440686 : term497 = True.
Proof. exact (TRANS (@lem2440681) (@lem2440685)). Qed.
Lemma lem2440687 : term506 = True.
Proof. exact (TRANS (@lem2440678) (@lem2440686)). Qed.
Lemma lem2440688 : term500 = True.
Proof. exact (TRANS (@lem2440664) (@lem2440687)). Qed.
Lemma lem2440689 : term497 = True.
Proof. exact (TRANS (@lem2440641) (@lem2440688)). Qed.
Lemma lem2440690 : term496 = True.
Proof. exact (TRANS (@lem2440632) (@lem2440689)). Qed.
Lemma lem2440691 : True = term496.
Proof. exact (SYM (@lem2440690)). Qed.
Lemma lem2440692 : term496.
Proof. exact (EQ_MP (@lem2440691) (@lem0)). Qed.
Lemma lem2440693 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term574 n x y.
Proof. exact (conj (@lem2440692) (@lem2440555 n x y h1)). Qed.
Lemma lem2440695 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2440696 (n : int) (x : int) (y : int) : term575 n x y.
Proof. exact (@lem2440695 term80 (term404 n x y)). Qed.
Lemma lem2440697 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term576 n x y.
Proof. exact (@lem2440696 n x y (@lem2440693 n x y h1)). Qed.
Lemma lem2440698 (n : int) (x : int) (y : int) : (term577 n x y) = (term404 n x y).
Proof. exact (@lem1982733 (term404 n x y)). Qed.
Lemma lem2440699 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2440700 (n : int) (x : int) (y : int) : (term578 n x y) = (term413 n x y).
Proof. exact (MK_COMB (@lem2440699) (@lem2440698 n x y)). Qed.
Lemma lem2440701 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2440702 (n : int) (x : int) (y : int) : (term576 n x y) = (term414 n x y).
Proof. exact (MK_COMB (@lem2440700 n x y) (@lem2440701)). Qed.
Lemma lem2440703 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term414 n x y.
Proof. exact (EQ_MP (@lem2440702 n x y) (@lem2440697 n x y h1)). Qed.
Lemma lem2440704 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term579 n x y.
Proof. exact (conj (@lem2440703 n x y h1) (@lem2440629 n x y h1)). Qed.
Lemma lem2440706 (x : real) (y : real) : term522 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2440707 (n : int) (x : int) (y : int) : term580 n x y.
Proof. exact (@lem2440706 (term404 n x y) (term260 n x y)). Qed.
Lemma lem2440708 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term581 n x y.
Proof. exact (@lem2440707 n x y (@lem2440704 n x y h1)). Qed.
Lemma lem2440709 (n : int) (x : int) (y : int) : (term582 n x y) = (term583 n x y).
Proof. exact (@lem1982753 (term201 n) (real_of_int n) (term278 x y) (term199 x y)). Qed.
Lemma lem2440710 (n : int) : (term527 n) = (term528 n).
Proof. exact (@lem1982713 term132 (real_of_int n)). Qed.
Lemma lem2440712 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440713 : term80 = term134.
Proof. exact (@lem2440712 term81). Qed.
Lemma lem2440715 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2440716 : term132 = term137.
Proof. exact (@lem2440715 term81). Qed.
Lemma lem2440717 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440718 : term529 = term530.
Proof. exact (MK_COMB (@lem2440717) (@lem2440716)). Qed.
Lemma lem2440719 : term531 = term532.
Proof. exact (MK_COMB (@lem2440718) (@lem2440713)). Qed.
Lemma lem2440720 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2440722 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440723 : term497 = term503.
Proof. exact (@lem2440722 (NUMERAL 0) term81). Qed.
Lemma lem2440724 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440725 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440726 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440725 h1) (fun h1 : term503 = True => @lem2440724)). Qed.
Lemma lem2440727 : term503 = True.
Proof. exact (EQ_MP (@lem2440726) (@lem2440724)). Qed.
Lemma lem2440728 : term497 = True.
Proof. exact (TRANS (@lem2440723) (@lem2440727)). Qed.
Lemma lem2440729 : True = term497.
Proof. exact (SYM (@lem2440728)). Qed.
Lemma lem2440730 : term497.
Proof. exact (EQ_MP (@lem2440729) (@lem0)). Qed.
Lemma lem2440731 : term534.
Proof. exact (@lem2440720 (@lem2440730)). Qed.
Lemma lem2440733 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440734 : term497 = term503.
Proof. exact (@lem2440733 (NUMERAL 0) term81). Qed.
Lemma lem2440735 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440736 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440737 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440736 h1) (fun h1 : term503 = True => @lem2440735)). Qed.
Lemma lem2440738 : term503 = True.
Proof. exact (EQ_MP (@lem2440737) (@lem2440735)). Qed.
Lemma lem2440739 : term497 = True.
Proof. exact (TRANS (@lem2440734) (@lem2440738)). Qed.
Lemma lem2440740 : True = term497.
Proof. exact (SYM (@lem2440739)). Qed.
Lemma lem2440741 : term497.
Proof. exact (EQ_MP (@lem2440740) (@lem0)). Qed.
Lemma lem2440742 : term535.
Proof. exact (@lem2440731 (@lem2440741)). Qed.
Lemma lem2440744 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440745 : term497 = term503.
Proof. exact (@lem2440744 (NUMERAL 0) term81). Qed.
Lemma lem2440746 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440747 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440748 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440747 h1) (fun h1 : term503 = True => @lem2440746)). Qed.
Lemma lem2440749 : term503 = True.
Proof. exact (EQ_MP (@lem2440748) (@lem2440746)). Qed.
Lemma lem2440750 : term497 = True.
Proof. exact (TRANS (@lem2440745) (@lem2440749)). Qed.
Lemma lem2440751 : True = term497.
Proof. exact (SYM (@lem2440750)). Qed.
Lemma lem2440752 : term497.
Proof. exact (EQ_MP (@lem2440751) (@lem0)). Qed.
Lemma lem2440753 : term536.
Proof. exact (@lem2440742 (@lem2440752)). Qed.
Lemma lem2440755 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440756 : term145 = term146.
Proof. exact (@lem2440755 term81 term81). Qed.
Lemma lem2440757 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440758 : term148 = term81.
Proof. exact (EQ_MP (@lem2440757) (@lem940073)). Qed.
Lemma lem2440759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440760 : term146 = term80.
Proof. exact (MK_COMB (@lem2440759) (@lem2440758)). Qed.
Lemma lem2440761 : term145 = term80.
Proof. exact (TRANS (@lem2440756) (@lem2440760)). Qed.
Lemma lem2440763 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2440764 : term140 = term151.
Proof. exact (@lem2440763 term81 term81). Qed.
Lemma lem2440765 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440766 : term148 = term81.
Proof. exact (EQ_MP (@lem2440765) (@lem940073)). Qed.
Lemma lem2440767 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440768 : term146 = term80.
Proof. exact (MK_COMB (@lem2440767) (@lem2440766)). Qed.
Lemma lem2440769 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2440770 : term151 = term132.
Proof. exact (MK_COMB (@lem2440769) (@lem2440768)). Qed.
Lemma lem2440771 : term140 = term132.
Proof. exact (TRANS (@lem2440764) (@lem2440770)). Qed.
Lemma lem2440772 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440773 : term537 = term529.
Proof. exact (MK_COMB (@lem2440772) (@lem2440771)). Qed.
Lemma lem2440774 : term538 = term531.
Proof. exact (MK_COMB (@lem2440773) (@lem2440761)). Qed.
Lemma lem2440776 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2440777 : term531 = term95.
Proof. exact (@lem2440776 term81). Qed.
Lemma lem2440778 : term538 = term95.
Proof. exact (TRANS (@lem2440774) (@lem2440777)). Qed.
Lemma lem2440779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440780 : term540 = term541.
Proof. exact (MK_COMB (@lem2440779) (@lem2440778)). Qed.
Lemma lem2440781 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2440782 : term542 = term508.
Proof. exact (MK_COMB (@lem2440780) (@lem2440781)). Qed.
Lemma lem2440784 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440785 : term508 = term95.
Proof. exact (@lem2440784 term81). Qed.
Lemma lem2440786 : term542 = term95.
Proof. exact (TRANS (@lem2440782) (@lem2440785)). Qed.
Lemma lem2440788 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440789 : term145 = term146.
Proof. exact (@lem2440788 term81 term81). Qed.
Lemma lem2440790 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440791 : term148 = term81.
Proof. exact (EQ_MP (@lem2440790) (@lem940073)). Qed.
Lemma lem2440792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440793 : term146 = term80.
Proof. exact (MK_COMB (@lem2440792) (@lem2440791)). Qed.
Lemma lem2440794 : term145 = term80.
Proof. exact (TRANS (@lem2440789) (@lem2440793)). Qed.
Lemma lem2440795 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2440796 : term543 = term508.
Proof. exact (MK_COMB (@lem2440795) (@lem2440794)). Qed.
Lemma lem2440798 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440799 : term508 = term95.
Proof. exact (@lem2440798 term81). Qed.
Lemma lem2440800 : term543 = term95.
Proof. exact (TRANS (@lem2440796) (@lem2440799)). Qed.
Lemma lem2440801 : term95 = term543.
Proof. exact (SYM (@lem2440800)). Qed.
Lemma lem2440802 : term542 = term543.
Proof. exact (TRANS (@lem2440786) (@lem2440801)). Qed.
Lemma lem2440803 : term532 = term179.
Proof. exact (@lem2440753 (@lem2440802)). Qed.
Lemma lem2440804 : term531 = term179.
Proof. exact (TRANS (@lem2440719) (@lem2440803)). Qed.
Lemma lem2440806 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2440807 : term179 = term95.
Proof. exact (@lem2440806 term95). Qed.
Lemma lem2440808 : term531 = term95.
Proof. exact (TRANS (@lem2440804) (@lem2440807)). Qed.
Lemma lem2440809 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440810 : term544 = term541.
Proof. exact (MK_COMB (@lem2440809) (@lem2440808)). Qed.
Lemma lem2440811 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2440812 (n : int) : (term528 n) = (term545 n).
Proof. exact (MK_COMB (@lem2440810) (@lem2440811 n)). Qed.
Lemma lem2440813 (n : int) : (term527 n) = (term545 n).
Proof. exact (TRANS (@lem2440710 n) (@lem2440812 n)). Qed.
Lemma lem2440814 (n : int) : (term545 n) = term95.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2440815 (n : int) : (term527 n) = term95.
Proof. exact (TRANS (@lem2440813 n) (@lem2440814 n)). Qed.
Lemma lem2440816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440817 (n : int) : (term546 n) = term392.
Proof. exact (MK_COMB (@lem2440816) (@lem2440815 n)). Qed.
Lemma lem2440818 (x : int) (y : int) : (term584 x y) = (term585 x y).
Proof. exact (@lem1982753 (term201 x) (real_of_int x) (real_of_int y) (term198 y)). Qed.
Lemma lem2440819 (x : int) : (term527 x) = (term528 x).
Proof. exact (@lem1982713 term132 (real_of_int x)). Qed.
Lemma lem2440821 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440822 : term80 = term134.
Proof. exact (@lem2440821 term81). Qed.
Lemma lem2440824 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2440825 : term132 = term137.
Proof. exact (@lem2440824 term81). Qed.
Lemma lem2440826 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440827 : term529 = term530.
Proof. exact (MK_COMB (@lem2440826) (@lem2440825)). Qed.
Lemma lem2440828 : term531 = term532.
Proof. exact (MK_COMB (@lem2440827) (@lem2440822)). Qed.
Lemma lem2440829 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2440831 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440832 : term497 = term503.
Proof. exact (@lem2440831 (NUMERAL 0) term81). Qed.
Lemma lem2440833 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440834 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440835 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440834 h1) (fun h1 : term503 = True => @lem2440833)). Qed.
Lemma lem2440836 : term503 = True.
Proof. exact (EQ_MP (@lem2440835) (@lem2440833)). Qed.
Lemma lem2440837 : term497 = True.
Proof. exact (TRANS (@lem2440832) (@lem2440836)). Qed.
Lemma lem2440838 : True = term497.
Proof. exact (SYM (@lem2440837)). Qed.
Lemma lem2440839 : term497.
Proof. exact (EQ_MP (@lem2440838) (@lem0)). Qed.
Lemma lem2440840 : term534.
Proof. exact (@lem2440829 (@lem2440839)). Qed.
Lemma lem2440842 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440843 : term497 = term503.
Proof. exact (@lem2440842 (NUMERAL 0) term81). Qed.
Lemma lem2440844 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440845 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440846 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440845 h1) (fun h1 : term503 = True => @lem2440844)). Qed.
Lemma lem2440847 : term503 = True.
Proof. exact (EQ_MP (@lem2440846) (@lem2440844)). Qed.
Lemma lem2440848 : term497 = True.
Proof. exact (TRANS (@lem2440843) (@lem2440847)). Qed.
Lemma lem2440849 : True = term497.
Proof. exact (SYM (@lem2440848)). Qed.
Lemma lem2440850 : term497.
Proof. exact (EQ_MP (@lem2440849) (@lem0)). Qed.
Lemma lem2440851 : term535.
Proof. exact (@lem2440840 (@lem2440850)). Qed.
Lemma lem2440853 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440854 : term497 = term503.
Proof. exact (@lem2440853 (NUMERAL 0) term81). Qed.
Lemma lem2440855 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440856 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440857 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440856 h1) (fun h1 : term503 = True => @lem2440855)). Qed.
Lemma lem2440858 : term503 = True.
Proof. exact (EQ_MP (@lem2440857) (@lem2440855)). Qed.
Lemma lem2440859 : term497 = True.
Proof. exact (TRANS (@lem2440854) (@lem2440858)). Qed.
Lemma lem2440860 : True = term497.
Proof. exact (SYM (@lem2440859)). Qed.
Lemma lem2440861 : term497.
Proof. exact (EQ_MP (@lem2440860) (@lem0)). Qed.
Lemma lem2440862 : term536.
Proof. exact (@lem2440851 (@lem2440861)). Qed.
Lemma lem2440864 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440865 : term145 = term146.
Proof. exact (@lem2440864 term81 term81). Qed.
Lemma lem2440866 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440867 : term148 = term81.
Proof. exact (EQ_MP (@lem2440866) (@lem940073)). Qed.
Lemma lem2440868 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440869 : term146 = term80.
Proof. exact (MK_COMB (@lem2440868) (@lem2440867)). Qed.
Lemma lem2440870 : term145 = term80.
Proof. exact (TRANS (@lem2440865) (@lem2440869)). Qed.
Lemma lem2440872 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2440873 : term140 = term151.
Proof. exact (@lem2440872 term81 term81). Qed.
Lemma lem2440874 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440875 : term148 = term81.
Proof. exact (EQ_MP (@lem2440874) (@lem940073)). Qed.
Lemma lem2440876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440877 : term146 = term80.
Proof. exact (MK_COMB (@lem2440876) (@lem2440875)). Qed.
Lemma lem2440878 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2440879 : term151 = term132.
Proof. exact (MK_COMB (@lem2440878) (@lem2440877)). Qed.
Lemma lem2440880 : term140 = term132.
Proof. exact (TRANS (@lem2440873) (@lem2440879)). Qed.
Lemma lem2440881 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440882 : term537 = term529.
Proof. exact (MK_COMB (@lem2440881) (@lem2440880)). Qed.
Lemma lem2440883 : term538 = term531.
Proof. exact (MK_COMB (@lem2440882) (@lem2440870)). Qed.
Lemma lem2440885 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2440886 : term531 = term95.
Proof. exact (@lem2440885 term81). Qed.
Lemma lem2440887 : term538 = term95.
Proof. exact (TRANS (@lem2440883) (@lem2440886)). Qed.
Lemma lem2440888 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440889 : term540 = term541.
Proof. exact (MK_COMB (@lem2440888) (@lem2440887)). Qed.
Lemma lem2440890 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2440891 : term542 = term508.
Proof. exact (MK_COMB (@lem2440889) (@lem2440890)). Qed.
Lemma lem2440893 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440894 : term508 = term95.
Proof. exact (@lem2440893 term81). Qed.
Lemma lem2440895 : term542 = term95.
Proof. exact (TRANS (@lem2440891) (@lem2440894)). Qed.
Lemma lem2440897 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440898 : term145 = term146.
Proof. exact (@lem2440897 term81 term81). Qed.
Lemma lem2440899 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440900 : term148 = term81.
Proof. exact (EQ_MP (@lem2440899) (@lem940073)). Qed.
Lemma lem2440901 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440902 : term146 = term80.
Proof. exact (MK_COMB (@lem2440901) (@lem2440900)). Qed.
Lemma lem2440903 : term145 = term80.
Proof. exact (TRANS (@lem2440898) (@lem2440902)). Qed.
Lemma lem2440904 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2440905 : term543 = term508.
Proof. exact (MK_COMB (@lem2440904) (@lem2440903)). Qed.
Lemma lem2440907 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2440908 : term508 = term95.
Proof. exact (@lem2440907 term81). Qed.
Lemma lem2440909 : term543 = term95.
Proof. exact (TRANS (@lem2440905) (@lem2440908)). Qed.
Lemma lem2440910 : term95 = term543.
Proof. exact (SYM (@lem2440909)). Qed.
Lemma lem2440911 : term542 = term543.
Proof. exact (TRANS (@lem2440895) (@lem2440910)). Qed.
Lemma lem2440912 : term532 = term179.
Proof. exact (@lem2440862 (@lem2440911)). Qed.
Lemma lem2440913 : term531 = term179.
Proof. exact (TRANS (@lem2440828) (@lem2440912)). Qed.
Lemma lem2440915 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2440916 : term179 = term95.
Proof. exact (@lem2440915 term95). Qed.
Lemma lem2440917 : term531 = term95.
Proof. exact (TRANS (@lem2440913) (@lem2440916)). Qed.
Lemma lem2440918 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440919 : term544 = term541.
Proof. exact (MK_COMB (@lem2440918) (@lem2440917)). Qed.
Lemma lem2440920 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2440921 (x : int) : (term528 x) = (term545 x).
Proof. exact (MK_COMB (@lem2440919) (@lem2440920 x)). Qed.
Lemma lem2440922 (x : int) : (term527 x) = (term545 x).
Proof. exact (TRANS (@lem2440819 x) (@lem2440921 x)). Qed.
Lemma lem2440923 (x : int) : (term545 x) = term95.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2440924 (x : int) : (term527 x) = term95.
Proof. exact (TRANS (@lem2440922 x) (@lem2440923 x)). Qed.
Lemma lem2440925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440926 (x : int) : (term546 x) = term392.
Proof. exact (MK_COMB (@lem2440925) (@lem2440924 x)). Qed.
Lemma lem2440927 (y : int) : (term586 y) = (term587 y).
Proof. exact (@lem1982763 (real_of_int y) (term201 y) term132). Qed.
Lemma lem2440928 (y : int) : (term549 y) = (term528 y).
Proof. exact (@lem1982715 term132 (real_of_int y)). Qed.
Lemma lem2440930 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2440931 : term80 = term134.
Proof. exact (@lem2440930 term81). Qed.
Lemma lem2440933 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2440934 : term132 = term137.
Proof. exact (@lem2440933 term81). Qed.
Lemma lem2440935 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440936 : term529 = term530.
Proof. exact (MK_COMB (@lem2440935) (@lem2440934)). Qed.
Lemma lem2440937 : term531 = term532.
Proof. exact (MK_COMB (@lem2440936) (@lem2440931)). Qed.
Lemma lem2440938 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2440940 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440941 : term497 = term503.
Proof. exact (@lem2440940 (NUMERAL 0) term81). Qed.
Lemma lem2440942 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440943 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440944 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440943 h1) (fun h1 : term503 = True => @lem2440942)). Qed.
Lemma lem2440945 : term503 = True.
Proof. exact (EQ_MP (@lem2440944) (@lem2440942)). Qed.
Lemma lem2440946 : term497 = True.
Proof. exact (TRANS (@lem2440941) (@lem2440945)). Qed.
Lemma lem2440947 : True = term497.
Proof. exact (SYM (@lem2440946)). Qed.
Lemma lem2440948 : term497.
Proof. exact (EQ_MP (@lem2440947) (@lem0)). Qed.
Lemma lem2440949 : term534.
Proof. exact (@lem2440938 (@lem2440948)). Qed.
Lemma lem2440951 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440952 : term497 = term503.
Proof. exact (@lem2440951 (NUMERAL 0) term81). Qed.
Lemma lem2440953 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440954 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440955 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440954 h1) (fun h1 : term503 = True => @lem2440953)). Qed.
Lemma lem2440956 : term503 = True.
Proof. exact (EQ_MP (@lem2440955) (@lem2440953)). Qed.
Lemma lem2440957 : term497 = True.
Proof. exact (TRANS (@lem2440952) (@lem2440956)). Qed.
Lemma lem2440958 : True = term497.
Proof. exact (SYM (@lem2440957)). Qed.
Lemma lem2440959 : term497.
Proof. exact (EQ_MP (@lem2440958) (@lem0)). Qed.
Lemma lem2440960 : term535.
Proof. exact (@lem2440949 (@lem2440959)). Qed.
Lemma lem2440962 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2440963 : term497 = term503.
Proof. exact (@lem2440962 (NUMERAL 0) term81). Qed.
Lemma lem2440964 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2440965 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2440966 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2440965 h1) (fun h1 : term503 = True => @lem2440964)). Qed.
Lemma lem2440967 : term503 = True.
Proof. exact (EQ_MP (@lem2440966) (@lem2440964)). Qed.
Lemma lem2440968 : term497 = True.
Proof. exact (TRANS (@lem2440963) (@lem2440967)). Qed.
Lemma lem2440969 : True = term497.
Proof. exact (SYM (@lem2440968)). Qed.
Lemma lem2440970 : term497.
Proof. exact (EQ_MP (@lem2440969) (@lem0)). Qed.
Lemma lem2440971 : term536.
Proof. exact (@lem2440960 (@lem2440970)). Qed.
Lemma lem2440973 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2440974 : term145 = term146.
Proof. exact (@lem2440973 term81 term81). Qed.
Lemma lem2440975 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440976 : term148 = term81.
Proof. exact (EQ_MP (@lem2440975) (@lem940073)). Qed.
Lemma lem2440977 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440978 : term146 = term80.
Proof. exact (MK_COMB (@lem2440977) (@lem2440976)). Qed.
Lemma lem2440979 : term145 = term80.
Proof. exact (TRANS (@lem2440974) (@lem2440978)). Qed.
Lemma lem2440981 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2440982 : term140 = term151.
Proof. exact (@lem2440981 term81 term81). Qed.
Lemma lem2440983 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2440984 : term148 = term81.
Proof. exact (EQ_MP (@lem2440983) (@lem940073)). Qed.
Lemma lem2440985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2440986 : term146 = term80.
Proof. exact (MK_COMB (@lem2440985) (@lem2440984)). Qed.
Lemma lem2440987 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2440988 : term151 = term132.
Proof. exact (MK_COMB (@lem2440987) (@lem2440986)). Qed.
Lemma lem2440989 : term140 = term132.
Proof. exact (TRANS (@lem2440982) (@lem2440988)). Qed.
Lemma lem2440990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2440991 : term537 = term529.
Proof. exact (MK_COMB (@lem2440990) (@lem2440989)). Qed.
Lemma lem2440992 : term538 = term531.
Proof. exact (MK_COMB (@lem2440991) (@lem2440979)). Qed.
Lemma lem2440994 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2440995 : term531 = term95.
Proof. exact (@lem2440994 term81). Qed.
Lemma lem2440996 : term538 = term95.
Proof. exact (TRANS (@lem2440992) (@lem2440995)). Qed.
Lemma lem2440997 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2440998 : term540 = term541.
Proof. exact (MK_COMB (@lem2440997) (@lem2440996)). Qed.
Lemma lem2440999 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2441000 : term542 = term508.
Proof. exact (MK_COMB (@lem2440998) (@lem2440999)). Qed.
Lemma lem2441002 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441003 : term508 = term95.
Proof. exact (@lem2441002 term81). Qed.
Lemma lem2441004 : term542 = term95.
Proof. exact (TRANS (@lem2441000) (@lem2441003)). Qed.
Lemma lem2441006 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441007 : term145 = term146.
Proof. exact (@lem2441006 term81 term81). Qed.
Lemma lem2441008 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441009 : term148 = term81.
Proof. exact (EQ_MP (@lem2441008) (@lem940073)). Qed.
Lemma lem2441010 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441011 : term146 = term80.
Proof. exact (MK_COMB (@lem2441010) (@lem2441009)). Qed.
Lemma lem2441012 : term145 = term80.
Proof. exact (TRANS (@lem2441007) (@lem2441011)). Qed.
Lemma lem2441013 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2441014 : term543 = term508.
Proof. exact (MK_COMB (@lem2441013) (@lem2441012)). Qed.
Lemma lem2441016 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441017 : term508 = term95.
Proof. exact (@lem2441016 term81). Qed.
Lemma lem2441018 : term543 = term95.
Proof. exact (TRANS (@lem2441014) (@lem2441017)). Qed.
Lemma lem2441019 : term95 = term543.
Proof. exact (SYM (@lem2441018)). Qed.
Lemma lem2441020 : term542 = term543.
Proof. exact (TRANS (@lem2441004) (@lem2441019)). Qed.
Lemma lem2441021 : term532 = term179.
Proof. exact (@lem2440971 (@lem2441020)). Qed.
Lemma lem2441022 : term531 = term179.
Proof. exact (TRANS (@lem2440937) (@lem2441021)). Qed.
Lemma lem2441024 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2441025 : term179 = term95.
Proof. exact (@lem2441024 term95). Qed.
Lemma lem2441026 : term531 = term95.
Proof. exact (TRANS (@lem2441022) (@lem2441025)). Qed.
Lemma lem2441027 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441028 : term544 = term541.
Proof. exact (MK_COMB (@lem2441027) (@lem2441026)). Qed.
Lemma lem2441029 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2441030 (y : int) : (term528 y) = (term545 y).
Proof. exact (MK_COMB (@lem2441028) (@lem2441029 y)). Qed.
Lemma lem2441031 (y : int) : (term549 y) = (term545 y).
Proof. exact (TRANS (@lem2440928 y) (@lem2441030 y)). Qed.
Lemma lem2441032 (y : int) : (term545 y) = term95.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2441033 (y : int) : (term549 y) = term95.
Proof. exact (TRANS (@lem2441031 y) (@lem2441032 y)). Qed.
Lemma lem2441034 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441035 (y : int) : (term550 y) = term392.
Proof. exact (MK_COMB (@lem2441034) (@lem2441033 y)). Qed.
Lemma lem2441036 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem2441037 (y : int) : (term587 y) = term553.
Proof. exact (MK_COMB (@lem2441035 y) (@lem2441036)). Qed.
Lemma lem2441038 (y : int) : (term586 y) = term553.
Proof. exact (TRANS (@lem2440927 y) (@lem2441037 y)). Qed.
Lemma lem2441039 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2441040 (y : int) : (term586 y) = term132.
Proof. exact (TRANS (@lem2441038 y) (@lem2441039)). Qed.
Lemma lem2441041 (x : int) (y : int) : (term585 x y) = term553.
Proof. exact (MK_COMB (@lem2440926 x) (@lem2441040 y)). Qed.
Lemma lem2441042 (x : int) (y : int) : (term584 x y) = term553.
Proof. exact (TRANS (@lem2440818 x y) (@lem2441041 x y)). Qed.
Lemma lem2441043 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2441044 (x : int) (y : int) : (term584 x y) = term132.
Proof. exact (TRANS (@lem2441042 x y) (@lem2441043)). Qed.
Lemma lem2441045 (n : int) (x : int) (y : int) : (term583 n x y) = term553.
Proof. exact (MK_COMB (@lem2440817 n) (@lem2441044 x y)). Qed.
Lemma lem2441046 (n : int) (x : int) (y : int) : (term582 n x y) = term553.
Proof. exact (TRANS (@lem2440709 n x y) (@lem2441045 n x y)). Qed.
Lemma lem2441047 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2441048 (n : int) (x : int) (y : int) : (term582 n x y) = term132.
Proof. exact (TRANS (@lem2441046 n x y) (@lem2441047)). Qed.
Lemma lem2441049 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2441050 (n : int) (x : int) (y : int) : (term588 n x y) = term555.
Proof. exact (MK_COMB (@lem2441049) (@lem2441048 n x y)). Qed.
Lemma lem2441051 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2441052 (n : int) (x : int) (y : int) : (term581 n x y) = term556.
Proof. exact (MK_COMB (@lem2441050 n x y) (@lem2441051)). Qed.
Lemma lem2441053 (n : int) (x : int) (y : int) (h1 : term442 n x y) : term556.
Proof. exact (EQ_MP (@lem2441052 n x y) (@lem2440708 n x y h1)). Qed.
Lemma lem2441055 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2441056 : term556 = term557.
Proof. exact (@lem2441055 term95 term132). Qed.
Lemma lem2441058 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2441059 : term132 = term137.
Proof. exact (@lem2441058 term81). Qed.
Lemma lem2441061 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441062 : term95 = term179.
Proof. exact (@lem2441061 (NUMERAL 0)). Qed.
Lemma lem2441063 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2441064 : term558 = term559.
Proof. exact (MK_COMB (@lem2441063) (@lem2441062)). Qed.
Lemma lem2441065 : term557 = term560.
Proof. exact (MK_COMB (@lem2441064) (@lem2441059)). Qed.
Lemma lem2441066 : term561.
Proof. exact (@lem1980026 term95 term80 term132 term80). Qed.
Lemma lem2441068 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441069 : term497 = term503.
Proof. exact (@lem2441068 (NUMERAL 0) term81). Qed.
Lemma lem2441070 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441071 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441072 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441071 h1) (fun h1 : term503 = True => @lem2441070)). Qed.
Lemma lem2441073 : term503 = True.
Proof. exact (EQ_MP (@lem2441072) (@lem2441070)). Qed.
Lemma lem2441074 : term497 = True.
Proof. exact (TRANS (@lem2441069) (@lem2441073)). Qed.
Lemma lem2441075 : True = term497.
Proof. exact (SYM (@lem2441074)). Qed.
Lemma lem2441076 : term497.
Proof. exact (EQ_MP (@lem2441075) (@lem0)). Qed.
Lemma lem2441077 : term562.
Proof. exact (@lem2441066 (@lem2441076)). Qed.
Lemma lem2441079 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441080 : term497 = term503.
Proof. exact (@lem2441079 (NUMERAL 0) term81). Qed.
Lemma lem2441081 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441082 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441083 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441082 h1) (fun h1 : term503 = True => @lem2441081)). Qed.
Lemma lem2441084 : term503 = True.
Proof. exact (EQ_MP (@lem2441083) (@lem2441081)). Qed.
Lemma lem2441085 : term497 = True.
Proof. exact (TRANS (@lem2441080) (@lem2441084)). Qed.
Lemma lem2441086 : True = term497.
Proof. exact (SYM (@lem2441085)). Qed.
Lemma lem2441087 : term497.
Proof. exact (EQ_MP (@lem2441086) (@lem0)). Qed.
Lemma lem2441088 : term560 = term563.
Proof. exact (@lem2441077 (@lem2441087)). Qed.
Lemma lem2441090 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2441091 : term140 = term151.
Proof. exact (@lem2441090 term81 term81). Qed.
Lemma lem2441092 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441093 : term148 = term81.
Proof. exact (EQ_MP (@lem2441092) (@lem940073)). Qed.
Lemma lem2441094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441095 : term146 = term80.
Proof. exact (MK_COMB (@lem2441094) (@lem2441093)). Qed.
Lemma lem2441096 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2441097 : term151 = term132.
Proof. exact (MK_COMB (@lem2441096) (@lem2441095)). Qed.
Lemma lem2441098 : term140 = term132.
Proof. exact (TRANS (@lem2441091) (@lem2441097)). Qed.
Lemma lem2441100 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441101 : term508 = term95.
Proof. exact (@lem2441100 term81). Qed.
Lemma lem2441102 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2441103 : term564 = term558.
Proof. exact (MK_COMB (@lem2441102) (@lem2441101)). Qed.
Lemma lem2441104 : term563 = term557.
Proof. exact (MK_COMB (@lem2441103) (@lem2441098)). Qed.
Lemma lem2441106 (m : nat) (n : nat) : (term565 m n) = (term566 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2441107 : term557 = term567.
Proof. exact (@lem2441106 (NUMERAL 0) term81). Qed.
Lemma lem2441108 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441109 (h1 : term504 = (BIT1 0)) : (term81 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2441110 : (term504 = (BIT1 0)) = ((term81 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441109 h1) (fun h1 : (term81 = (NUMERAL 0)) = False => @lem2441108)). Qed.
Lemma lem2441111 : (term81 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2441110) (@lem2441108)). Qed.
Lemma lem2441112 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2441113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2441114 : term568 = (and True).
Proof. exact (MK_COMB (@lem2441113) (@lem2441112)). Qed.
Lemma lem2441115 : term567 = (True /\ False).
Proof. exact (MK_COMB (@lem2441114) (@lem2441111)). Qed.
Lemma lem2441117 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2441118 : term567 = False.
Proof. exact (TRANS (@lem2441115) (@lem2441117)). Qed.
Lemma lem2441119 : term557 = False.
Proof. exact (TRANS (@lem2441107) (@lem2441118)). Qed.
Lemma lem2441120 : term563 = False.
Proof. exact (TRANS (@lem2441104) (@lem2441119)). Qed.
Lemma lem2441121 : term560 = False.
Proof. exact (TRANS (@lem2441088) (@lem2441120)). Qed.
Lemma lem2441122 : term557 = False.
Proof. exact (TRANS (@lem2441065) (@lem2441121)). Qed.
Lemma lem2441123 : term556 = False.
Proof. exact (TRANS (@lem2441056) (@lem2441122)). Qed.
Lemma lem2441124 (n : int) (x : int) (y : int) (h1 : term442 n x y) : False.
Proof. exact (EQ_MP (@lem2441123) (@lem2441053 n x y h1)). Qed.
Lemma lem2441125 (n : int) (x : int) (y : int) (h1 : term444 n x y) : False.
Proof. exact (or_elim (@lem2439960 n x y h1) (fun h0 : term387 n x y => @lem2440542 n x y h0) (fun h0 : term442 n x y => @lem2441124 n x y h0)). Qed.
Lemma lem2441126 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term446 n x y.
Proof. exact (h1). Qed.
Lemma lem2441127 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term244 n x y.
Proof. exact (proj2 (@lem2441126 n x y h1)). Qed.
Lemma lem2441131 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term231 x y.
Proof. exact (proj2 (@lem2441127 n x y h1)). Qed.
Lemma lem2441133 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term204 x y.
Proof. exact (proj2 (@lem2441131 n x y h1)). Qed.
Lemma lem2441134 (n : int) (x : int) (y : int) (h1 : term446 n x y) : (term122 x y) = term95.
Proof. exact (proj1 (@lem2441131 n x y h1)). Qed.
Lemma lem2441136 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2441137 : term496 = term497.
Proof. exact (@lem2441136 term95 term80). Qed.
Lemma lem2441139 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441140 : term80 = term134.
Proof. exact (@lem2441139 term81). Qed.
Lemma lem2441142 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441143 : term95 = term179.
Proof. exact (@lem2441142 (NUMERAL 0)). Qed.
Lemma lem2441144 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2441145 : term498 = term499.
Proof. exact (MK_COMB (@lem2441144) (@lem2441143)). Qed.
Lemma lem2441146 : term497 = term500.
Proof. exact (MK_COMB (@lem2441145) (@lem2441140)). Qed.
Lemma lem2441147 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2441149 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441150 : term497 = term503.
Proof. exact (@lem2441149 (NUMERAL 0) term81). Qed.
Lemma lem2441151 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441152 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441153 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441152 h1) (fun h1 : term503 = True => @lem2441151)). Qed.
Lemma lem2441154 : term503 = True.
Proof. exact (EQ_MP (@lem2441153) (@lem2441151)). Qed.
Lemma lem2441155 : term497 = True.
Proof. exact (TRANS (@lem2441150) (@lem2441154)). Qed.
Lemma lem2441156 : True = term497.
Proof. exact (SYM (@lem2441155)). Qed.
Lemma lem2441157 : term497.
Proof. exact (EQ_MP (@lem2441156) (@lem0)). Qed.
Lemma lem2441158 : term505.
Proof. exact (@lem2441147 (@lem2441157)). Qed.
Lemma lem2441160 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441161 : term497 = term503.
Proof. exact (@lem2441160 (NUMERAL 0) term81). Qed.
Lemma lem2441162 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441163 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441164 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441163 h1) (fun h1 : term503 = True => @lem2441162)). Qed.
Lemma lem2441165 : term503 = True.
Proof. exact (EQ_MP (@lem2441164) (@lem2441162)). Qed.
Lemma lem2441166 : term497 = True.
Proof. exact (TRANS (@lem2441161) (@lem2441165)). Qed.
Lemma lem2441167 : True = term497.
Proof. exact (SYM (@lem2441166)). Qed.
Lemma lem2441168 : term497.
Proof. exact (EQ_MP (@lem2441167) (@lem0)). Qed.
Lemma lem2441169 : term500 = term506.
Proof. exact (@lem2441158 (@lem2441168)). Qed.
Lemma lem2441171 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441172 : term145 = term146.
Proof. exact (@lem2441171 term81 term81). Qed.
Lemma lem2441173 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441174 : term148 = term81.
Proof. exact (EQ_MP (@lem2441173) (@lem940073)). Qed.
Lemma lem2441175 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441176 : term146 = term80.
Proof. exact (MK_COMB (@lem2441175) (@lem2441174)). Qed.
Lemma lem2441177 : term145 = term80.
Proof. exact (TRANS (@lem2441172) (@lem2441176)). Qed.
Lemma lem2441179 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441180 : term508 = term95.
Proof. exact (@lem2441179 term81). Qed.
Lemma lem2441181 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2441182 : term509 = term498.
Proof. exact (MK_COMB (@lem2441181) (@lem2441180)). Qed.
Lemma lem2441183 : term506 = term497.
Proof. exact (MK_COMB (@lem2441182) (@lem2441177)). Qed.
Lemma lem2441185 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441186 : term497 = term503.
Proof. exact (@lem2441185 (NUMERAL 0) term81). Qed.
Lemma lem2441187 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441188 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441189 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441188 h1) (fun h1 : term503 = True => @lem2441187)). Qed.
Lemma lem2441190 : term503 = True.
Proof. exact (EQ_MP (@lem2441189) (@lem2441187)). Qed.
Lemma lem2441191 : term497 = True.
Proof. exact (TRANS (@lem2441186) (@lem2441190)). Qed.
Lemma lem2441192 : term506 = True.
Proof. exact (TRANS (@lem2441183) (@lem2441191)). Qed.
Lemma lem2441193 : term500 = True.
Proof. exact (TRANS (@lem2441169) (@lem2441192)). Qed.
Lemma lem2441194 : term497 = True.
Proof. exact (TRANS (@lem2441146) (@lem2441193)). Qed.
Lemma lem2441195 : term496 = True.
Proof. exact (TRANS (@lem2441137) (@lem2441194)). Qed.
Lemma lem2441196 : True = term496.
Proof. exact (SYM (@lem2441195)). Qed.
Lemma lem2441197 : term496.
Proof. exact (EQ_MP (@lem2441196) (@lem0)). Qed.
Lemma lem2441198 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term589 x y.
Proof. exact (conj (@lem2441197) (@lem2441133 n x y h1)). Qed.
Lemma lem2441200 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2441201 (x : int) (y : int) : term590 x y.
Proof. exact (@lem2441200 term80 (term200 x y)). Qed.
Lemma lem2441202 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term591 x y.
Proof. exact (@lem2441201 x y (@lem2441198 n x y h1)). Qed.
Lemma lem2441203 (x : int) (y : int) : (term592 x y) = (term200 x y).
Proof. exact (@lem1982733 (term200 x y)). Qed.
Lemma lem2441204 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2441205 (x : int) (y : int) : (term593 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem2441204) (@lem2441203 x y)). Qed.
Lemma lem2441206 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2441207 (x : int) (y : int) : (term591 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem2441205 x y) (@lem2441206)). Qed.
Lemma lem2441208 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term204 x y.
Proof. exact (EQ_MP (@lem2441207 x y) (@lem2441202 n x y h1)). Qed.
Lemma lem2441210 (y : real) : term594 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2441211 (x : int) (y : int) : term595 x y.
Proof. exact (@lem2441210 (term122 x y)). Qed.
Lemma lem2441212 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term596 x y.
Proof. exact (@lem2441211 x y (@lem2441134 n x y h1)). Qed.
Lemma lem2441213 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term597 x y.
Proof. exact (@lem2441212 n x y h1 term80). Qed.
Lemma lem2441214 (x : int) (y : int) : (term597 x y) = ((term252 x y) = term95).
Proof. exact (eq_refl (term597 x y)). Qed.
Lemma lem2441215 (n : int) (x : int) (y : int) (h1 : term446 n x y) : (term252 x y) = term95.
Proof. exact (EQ_MP (@lem2441214 x y) (@lem2441213 n x y h1)). Qed.
Lemma lem2441216 (x : int) (y : int) : (term252 x y) = (term122 x y).
Proof. exact (@lem1982733 (term122 x y)). Qed.
Lemma lem2441217 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2441218 (x : int) (y : int) : (term598 x y) = (term189 x y).
Proof. exact (MK_COMB (@lem2441217) (@lem2441216 x y)). Qed.
Lemma lem2441219 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2441220 (x : int) (y : int) : ((term252 x y) = term95) = ((term122 x y) = term95).
Proof. exact (MK_COMB (@lem2441218 x y) (@lem2441219)). Qed.
Lemma lem2441221 (n : int) (x : int) (y : int) (h1 : term446 n x y) : (term122 x y) = term95.
Proof. exact (EQ_MP (@lem2441220 x y) (@lem2441215 n x y h1)). Qed.
Lemma lem2441222 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term231 x y.
Proof. exact (conj (@lem2441221 n x y h1) (@lem2441208 n x y h1)). Qed.
Lemma lem2441224 (x : real) (y : real) : term599 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2441225 (x : int) (y : int) : term600 x y.
Proof. exact (@lem2441224 (term122 x y) (term200 x y)). Qed.
Lemma lem2441226 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term601 x y.
Proof. exact (@lem2441225 x y (@lem2441222 n x y h1)). Qed.
Lemma lem2441227 (x : int) (y : int) : (term547 x y) = (term548 x y).
Proof. exact (@lem1982753 (real_of_int x) (term201 x) (term201 y) (term251 y)). Qed.
Lemma lem2441228 (x : int) : (term549 x) = (term528 x).
Proof. exact (@lem1982715 term132 (real_of_int x)). Qed.
Lemma lem2441230 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441231 : term80 = term134.
Proof. exact (@lem2441230 term81). Qed.
Lemma lem2441233 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2441234 : term132 = term137.
Proof. exact (@lem2441233 term81). Qed.
Lemma lem2441235 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441236 : term529 = term530.
Proof. exact (MK_COMB (@lem2441235) (@lem2441234)). Qed.
Lemma lem2441237 : term531 = term532.
Proof. exact (MK_COMB (@lem2441236) (@lem2441231)). Qed.
Lemma lem2441238 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2441240 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441241 : term497 = term503.
Proof. exact (@lem2441240 (NUMERAL 0) term81). Qed.
Lemma lem2441242 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441243 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441244 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441243 h1) (fun h1 : term503 = True => @lem2441242)). Qed.
Lemma lem2441245 : term503 = True.
Proof. exact (EQ_MP (@lem2441244) (@lem2441242)). Qed.
Lemma lem2441246 : term497 = True.
Proof. exact (TRANS (@lem2441241) (@lem2441245)). Qed.
Lemma lem2441247 : True = term497.
Proof. exact (SYM (@lem2441246)). Qed.
Lemma lem2441248 : term497.
Proof. exact (EQ_MP (@lem2441247) (@lem0)). Qed.
Lemma lem2441249 : term534.
Proof. exact (@lem2441238 (@lem2441248)). Qed.
Lemma lem2441251 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441252 : term497 = term503.
Proof. exact (@lem2441251 (NUMERAL 0) term81). Qed.
Lemma lem2441253 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441254 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441255 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441254 h1) (fun h1 : term503 = True => @lem2441253)). Qed.
Lemma lem2441256 : term503 = True.
Proof. exact (EQ_MP (@lem2441255) (@lem2441253)). Qed.
Lemma lem2441257 : term497 = True.
Proof. exact (TRANS (@lem2441252) (@lem2441256)). Qed.
Lemma lem2441258 : True = term497.
Proof. exact (SYM (@lem2441257)). Qed.
Lemma lem2441259 : term497.
Proof. exact (EQ_MP (@lem2441258) (@lem0)). Qed.
Lemma lem2441260 : term535.
Proof. exact (@lem2441249 (@lem2441259)). Qed.
Lemma lem2441262 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441263 : term497 = term503.
Proof. exact (@lem2441262 (NUMERAL 0) term81). Qed.
Lemma lem2441264 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441265 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441266 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441265 h1) (fun h1 : term503 = True => @lem2441264)). Qed.
Lemma lem2441267 : term503 = True.
Proof. exact (EQ_MP (@lem2441266) (@lem2441264)). Qed.
Lemma lem2441268 : term497 = True.
Proof. exact (TRANS (@lem2441263) (@lem2441267)). Qed.
Lemma lem2441269 : True = term497.
Proof. exact (SYM (@lem2441268)). Qed.
Lemma lem2441270 : term497.
Proof. exact (EQ_MP (@lem2441269) (@lem0)). Qed.
Lemma lem2441271 : term536.
Proof. exact (@lem2441260 (@lem2441270)). Qed.
Lemma lem2441273 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441274 : term145 = term146.
Proof. exact (@lem2441273 term81 term81). Qed.
Lemma lem2441275 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441276 : term148 = term81.
Proof. exact (EQ_MP (@lem2441275) (@lem940073)). Qed.
Lemma lem2441277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441278 : term146 = term80.
Proof. exact (MK_COMB (@lem2441277) (@lem2441276)). Qed.
Lemma lem2441279 : term145 = term80.
Proof. exact (TRANS (@lem2441274) (@lem2441278)). Qed.
Lemma lem2441281 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2441282 : term140 = term151.
Proof. exact (@lem2441281 term81 term81). Qed.
Lemma lem2441283 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441284 : term148 = term81.
Proof. exact (EQ_MP (@lem2441283) (@lem940073)). Qed.
Lemma lem2441285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441286 : term146 = term80.
Proof. exact (MK_COMB (@lem2441285) (@lem2441284)). Qed.
Lemma lem2441287 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2441288 : term151 = term132.
Proof. exact (MK_COMB (@lem2441287) (@lem2441286)). Qed.
Lemma lem2441289 : term140 = term132.
Proof. exact (TRANS (@lem2441282) (@lem2441288)). Qed.
Lemma lem2441290 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441291 : term537 = term529.
Proof. exact (MK_COMB (@lem2441290) (@lem2441289)). Qed.
Lemma lem2441292 : term538 = term531.
Proof. exact (MK_COMB (@lem2441291) (@lem2441279)). Qed.
Lemma lem2441294 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2441295 : term531 = term95.
Proof. exact (@lem2441294 term81). Qed.
Lemma lem2441296 : term538 = term95.
Proof. exact (TRANS (@lem2441292) (@lem2441295)). Qed.
Lemma lem2441297 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441298 : term540 = term541.
Proof. exact (MK_COMB (@lem2441297) (@lem2441296)). Qed.
Lemma lem2441299 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2441300 : term542 = term508.
Proof. exact (MK_COMB (@lem2441298) (@lem2441299)). Qed.
Lemma lem2441302 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441303 : term508 = term95.
Proof. exact (@lem2441302 term81). Qed.
Lemma lem2441304 : term542 = term95.
Proof. exact (TRANS (@lem2441300) (@lem2441303)). Qed.
Lemma lem2441306 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441307 : term145 = term146.
Proof. exact (@lem2441306 term81 term81). Qed.
Lemma lem2441308 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441309 : term148 = term81.
Proof. exact (EQ_MP (@lem2441308) (@lem940073)). Qed.
Lemma lem2441310 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441311 : term146 = term80.
Proof. exact (MK_COMB (@lem2441310) (@lem2441309)). Qed.
Lemma lem2441312 : term145 = term80.
Proof. exact (TRANS (@lem2441307) (@lem2441311)). Qed.
Lemma lem2441313 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2441314 : term543 = term508.
Proof. exact (MK_COMB (@lem2441313) (@lem2441312)). Qed.
Lemma lem2441316 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441317 : term508 = term95.
Proof. exact (@lem2441316 term81). Qed.
Lemma lem2441318 : term543 = term95.
Proof. exact (TRANS (@lem2441314) (@lem2441317)). Qed.
Lemma lem2441319 : term95 = term543.
Proof. exact (SYM (@lem2441318)). Qed.
Lemma lem2441320 : term542 = term543.
Proof. exact (TRANS (@lem2441304) (@lem2441319)). Qed.
Lemma lem2441321 : term532 = term179.
Proof. exact (@lem2441271 (@lem2441320)). Qed.
Lemma lem2441322 : term531 = term179.
Proof. exact (TRANS (@lem2441237) (@lem2441321)). Qed.
Lemma lem2441324 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2441325 : term179 = term95.
Proof. exact (@lem2441324 term95). Qed.
Lemma lem2441326 : term531 = term95.
Proof. exact (TRANS (@lem2441322) (@lem2441325)). Qed.
Lemma lem2441327 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441328 : term544 = term541.
Proof. exact (MK_COMB (@lem2441327) (@lem2441326)). Qed.
Lemma lem2441329 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2441330 (x : int) : (term528 x) = (term545 x).
Proof. exact (MK_COMB (@lem2441328) (@lem2441329 x)). Qed.
Lemma lem2441331 (x : int) : (term549 x) = (term545 x).
Proof. exact (TRANS (@lem2441228 x) (@lem2441330 x)). Qed.
Lemma lem2441332 (x : int) : (term545 x) = term95.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2441333 (x : int) : (term549 x) = term95.
Proof. exact (TRANS (@lem2441331 x) (@lem2441332 x)). Qed.
Lemma lem2441334 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441335 (x : int) : (term550 x) = term392.
Proof. exact (MK_COMB (@lem2441334) (@lem2441333 x)). Qed.
Lemma lem2441336 (y : int) : (term551 y) = (term552 y).
Proof. exact (@lem1982763 (term201 y) (real_of_int y) term132). Qed.
Lemma lem2441337 (y : int) : (term527 y) = (term528 y).
Proof. exact (@lem1982713 term132 (real_of_int y)). Qed.
Lemma lem2441339 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441340 : term80 = term134.
Proof. exact (@lem2441339 term81). Qed.
Lemma lem2441342 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2441343 : term132 = term137.
Proof. exact (@lem2441342 term81). Qed.
Lemma lem2441344 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441345 : term529 = term530.
Proof. exact (MK_COMB (@lem2441344) (@lem2441343)). Qed.
Lemma lem2441346 : term531 = term532.
Proof. exact (MK_COMB (@lem2441345) (@lem2441340)). Qed.
Lemma lem2441347 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2441349 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441350 : term497 = term503.
Proof. exact (@lem2441349 (NUMERAL 0) term81). Qed.
Lemma lem2441351 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441352 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441353 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441352 h1) (fun h1 : term503 = True => @lem2441351)). Qed.
Lemma lem2441354 : term503 = True.
Proof. exact (EQ_MP (@lem2441353) (@lem2441351)). Qed.
Lemma lem2441355 : term497 = True.
Proof. exact (TRANS (@lem2441350) (@lem2441354)). Qed.
Lemma lem2441356 : True = term497.
Proof. exact (SYM (@lem2441355)). Qed.
Lemma lem2441357 : term497.
Proof. exact (EQ_MP (@lem2441356) (@lem0)). Qed.
Lemma lem2441358 : term534.
Proof. exact (@lem2441347 (@lem2441357)). Qed.
Lemma lem2441360 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441361 : term497 = term503.
Proof. exact (@lem2441360 (NUMERAL 0) term81). Qed.
Lemma lem2441362 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441363 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441364 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441363 h1) (fun h1 : term503 = True => @lem2441362)). Qed.
Lemma lem2441365 : term503 = True.
Proof. exact (EQ_MP (@lem2441364) (@lem2441362)). Qed.
Lemma lem2441366 : term497 = True.
Proof. exact (TRANS (@lem2441361) (@lem2441365)). Qed.
Lemma lem2441367 : True = term497.
Proof. exact (SYM (@lem2441366)). Qed.
Lemma lem2441368 : term497.
Proof. exact (EQ_MP (@lem2441367) (@lem0)). Qed.
Lemma lem2441369 : term535.
Proof. exact (@lem2441358 (@lem2441368)). Qed.
Lemma lem2441371 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441372 : term497 = term503.
Proof. exact (@lem2441371 (NUMERAL 0) term81). Qed.
Lemma lem2441373 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441374 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441375 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441374 h1) (fun h1 : term503 = True => @lem2441373)). Qed.
Lemma lem2441376 : term503 = True.
Proof. exact (EQ_MP (@lem2441375) (@lem2441373)). Qed.
Lemma lem2441377 : term497 = True.
Proof. exact (TRANS (@lem2441372) (@lem2441376)). Qed.
Lemma lem2441378 : True = term497.
Proof. exact (SYM (@lem2441377)). Qed.
Lemma lem2441379 : term497.
Proof. exact (EQ_MP (@lem2441378) (@lem0)). Qed.
Lemma lem2441380 : term536.
Proof. exact (@lem2441369 (@lem2441379)). Qed.
Lemma lem2441382 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441383 : term145 = term146.
Proof. exact (@lem2441382 term81 term81). Qed.
Lemma lem2441384 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441385 : term148 = term81.
Proof. exact (EQ_MP (@lem2441384) (@lem940073)). Qed.
Lemma lem2441386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441387 : term146 = term80.
Proof. exact (MK_COMB (@lem2441386) (@lem2441385)). Qed.
Lemma lem2441388 : term145 = term80.
Proof. exact (TRANS (@lem2441383) (@lem2441387)). Qed.
Lemma lem2441390 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2441391 : term140 = term151.
Proof. exact (@lem2441390 term81 term81). Qed.
Lemma lem2441392 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441393 : term148 = term81.
Proof. exact (EQ_MP (@lem2441392) (@lem940073)). Qed.
Lemma lem2441394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441395 : term146 = term80.
Proof. exact (MK_COMB (@lem2441394) (@lem2441393)). Qed.
Lemma lem2441396 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2441397 : term151 = term132.
Proof. exact (MK_COMB (@lem2441396) (@lem2441395)). Qed.
Lemma lem2441398 : term140 = term132.
Proof. exact (TRANS (@lem2441391) (@lem2441397)). Qed.
Lemma lem2441399 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441400 : term537 = term529.
Proof. exact (MK_COMB (@lem2441399) (@lem2441398)). Qed.
Lemma lem2441401 : term538 = term531.
Proof. exact (MK_COMB (@lem2441400) (@lem2441388)). Qed.
Lemma lem2441403 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2441404 : term531 = term95.
Proof. exact (@lem2441403 term81). Qed.
Lemma lem2441405 : term538 = term95.
Proof. exact (TRANS (@lem2441401) (@lem2441404)). Qed.
Lemma lem2441406 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441407 : term540 = term541.
Proof. exact (MK_COMB (@lem2441406) (@lem2441405)). Qed.
Lemma lem2441408 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2441409 : term542 = term508.
Proof. exact (MK_COMB (@lem2441407) (@lem2441408)). Qed.
Lemma lem2441411 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441412 : term508 = term95.
Proof. exact (@lem2441411 term81). Qed.
Lemma lem2441413 : term542 = term95.
Proof. exact (TRANS (@lem2441409) (@lem2441412)). Qed.
Lemma lem2441415 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441416 : term145 = term146.
Proof. exact (@lem2441415 term81 term81). Qed.
Lemma lem2441417 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441418 : term148 = term81.
Proof. exact (EQ_MP (@lem2441417) (@lem940073)). Qed.
Lemma lem2441419 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441420 : term146 = term80.
Proof. exact (MK_COMB (@lem2441419) (@lem2441418)). Qed.
Lemma lem2441421 : term145 = term80.
Proof. exact (TRANS (@lem2441416) (@lem2441420)). Qed.
Lemma lem2441422 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2441423 : term543 = term508.
Proof. exact (MK_COMB (@lem2441422) (@lem2441421)). Qed.
Lemma lem2441425 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441426 : term508 = term95.
Proof. exact (@lem2441425 term81). Qed.
Lemma lem2441427 : term543 = term95.
Proof. exact (TRANS (@lem2441423) (@lem2441426)). Qed.
Lemma lem2441428 : term95 = term543.
Proof. exact (SYM (@lem2441427)). Qed.
Lemma lem2441429 : term542 = term543.
Proof. exact (TRANS (@lem2441413) (@lem2441428)). Qed.
Lemma lem2441430 : term532 = term179.
Proof. exact (@lem2441380 (@lem2441429)). Qed.
Lemma lem2441431 : term531 = term179.
Proof. exact (TRANS (@lem2441346) (@lem2441430)). Qed.
Lemma lem2441433 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2441434 : term179 = term95.
Proof. exact (@lem2441433 term95). Qed.
Lemma lem2441435 : term531 = term95.
Proof. exact (TRANS (@lem2441431) (@lem2441434)). Qed.
Lemma lem2441436 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441437 : term544 = term541.
Proof. exact (MK_COMB (@lem2441436) (@lem2441435)). Qed.
Lemma lem2441438 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2441439 (y : int) : (term528 y) = (term545 y).
Proof. exact (MK_COMB (@lem2441437) (@lem2441438 y)). Qed.
Lemma lem2441440 (y : int) : (term527 y) = (term545 y).
Proof. exact (TRANS (@lem2441337 y) (@lem2441439 y)). Qed.
Lemma lem2441441 (y : int) : (term545 y) = term95.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2441442 (y : int) : (term527 y) = term95.
Proof. exact (TRANS (@lem2441440 y) (@lem2441441 y)). Qed.
Lemma lem2441443 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441444 (y : int) : (term546 y) = term392.
Proof. exact (MK_COMB (@lem2441443) (@lem2441442 y)). Qed.
Lemma lem2441445 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem2441446 (y : int) : (term552 y) = term553.
Proof. exact (MK_COMB (@lem2441444 y) (@lem2441445)). Qed.
Lemma lem2441447 (y : int) : (term551 y) = term553.
Proof. exact (TRANS (@lem2441336 y) (@lem2441446 y)). Qed.
Lemma lem2441448 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2441449 (y : int) : (term551 y) = term132.
Proof. exact (TRANS (@lem2441447 y) (@lem2441448)). Qed.
Lemma lem2441450 (x : int) (y : int) : (term548 x y) = term553.
Proof. exact (MK_COMB (@lem2441335 x) (@lem2441449 y)). Qed.
Lemma lem2441451 (x : int) (y : int) : (term547 x y) = term553.
Proof. exact (TRANS (@lem2441227 x y) (@lem2441450 x y)). Qed.
Lemma lem2441452 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2441453 (x : int) (y : int) : (term547 x y) = term132.
Proof. exact (TRANS (@lem2441451 x y) (@lem2441452)). Qed.
Lemma lem2441454 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2441455 (x : int) (y : int) : (term602 x y) = term555.
Proof. exact (MK_COMB (@lem2441454) (@lem2441453 x y)). Qed.
Lemma lem2441456 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2441457 (x : int) (y : int) : (term601 x y) = term556.
Proof. exact (MK_COMB (@lem2441455 x y) (@lem2441456)). Qed.
Lemma lem2441458 (n : int) (x : int) (y : int) (h1 : term446 n x y) : term556.
Proof. exact (EQ_MP (@lem2441457 x y) (@lem2441226 n x y h1)). Qed.
Lemma lem2441460 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2441461 : term556 = term557.
Proof. exact (@lem2441460 term95 term132). Qed.
Lemma lem2441463 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2441464 : term132 = term137.
Proof. exact (@lem2441463 term81). Qed.
Lemma lem2441466 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441467 : term95 = term179.
Proof. exact (@lem2441466 (NUMERAL 0)). Qed.
Lemma lem2441468 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2441469 : term558 = term559.
Proof. exact (MK_COMB (@lem2441468) (@lem2441467)). Qed.
Lemma lem2441470 : term557 = term560.
Proof. exact (MK_COMB (@lem2441469) (@lem2441464)). Qed.
Lemma lem2441471 : term561.
Proof. exact (@lem1980026 term95 term80 term132 term80). Qed.
Lemma lem2441473 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441474 : term497 = term503.
Proof. exact (@lem2441473 (NUMERAL 0) term81). Qed.
Lemma lem2441475 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441476 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441477 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441476 h1) (fun h1 : term503 = True => @lem2441475)). Qed.
Lemma lem2441478 : term503 = True.
Proof. exact (EQ_MP (@lem2441477) (@lem2441475)). Qed.
Lemma lem2441479 : term497 = True.
Proof. exact (TRANS (@lem2441474) (@lem2441478)). Qed.
Lemma lem2441480 : True = term497.
Proof. exact (SYM (@lem2441479)). Qed.
Lemma lem2441481 : term497.
Proof. exact (EQ_MP (@lem2441480) (@lem0)). Qed.
Lemma lem2441482 : term562.
Proof. exact (@lem2441471 (@lem2441481)). Qed.
Lemma lem2441484 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441485 : term497 = term503.
Proof. exact (@lem2441484 (NUMERAL 0) term81). Qed.
Lemma lem2441486 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441487 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441488 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441487 h1) (fun h1 : term503 = True => @lem2441486)). Qed.
Lemma lem2441489 : term503 = True.
Proof. exact (EQ_MP (@lem2441488) (@lem2441486)). Qed.
Lemma lem2441490 : term497 = True.
Proof. exact (TRANS (@lem2441485) (@lem2441489)). Qed.
Lemma lem2441491 : True = term497.
Proof. exact (SYM (@lem2441490)). Qed.
Lemma lem2441492 : term497.
Proof. exact (EQ_MP (@lem2441491) (@lem0)). Qed.
Lemma lem2441493 : term560 = term563.
Proof. exact (@lem2441482 (@lem2441492)). Qed.
Lemma lem2441495 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2441496 : term140 = term151.
Proof. exact (@lem2441495 term81 term81). Qed.
Lemma lem2441497 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441498 : term148 = term81.
Proof. exact (EQ_MP (@lem2441497) (@lem940073)). Qed.
Lemma lem2441499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441500 : term146 = term80.
Proof. exact (MK_COMB (@lem2441499) (@lem2441498)). Qed.
Lemma lem2441501 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2441502 : term151 = term132.
Proof. exact (MK_COMB (@lem2441501) (@lem2441500)). Qed.
Lemma lem2441503 : term140 = term132.
Proof. exact (TRANS (@lem2441496) (@lem2441502)). Qed.
Lemma lem2441505 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441506 : term508 = term95.
Proof. exact (@lem2441505 term81). Qed.
Lemma lem2441507 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2441508 : term564 = term558.
Proof. exact (MK_COMB (@lem2441507) (@lem2441506)). Qed.
Lemma lem2441509 : term563 = term557.
Proof. exact (MK_COMB (@lem2441508) (@lem2441503)). Qed.
Lemma lem2441511 (m : nat) (n : nat) : (term565 m n) = (term566 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2441512 : term557 = term567.
Proof. exact (@lem2441511 (NUMERAL 0) term81). Qed.
Lemma lem2441513 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441514 (h1 : term504 = (BIT1 0)) : (term81 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2441515 : (term504 = (BIT1 0)) = ((term81 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441514 h1) (fun h1 : (term81 = (NUMERAL 0)) = False => @lem2441513)). Qed.
Lemma lem2441516 : (term81 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2441515) (@lem2441513)). Qed.
Lemma lem2441517 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2441518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2441519 : term568 = (and True).
Proof. exact (MK_COMB (@lem2441518) (@lem2441517)). Qed.
Lemma lem2441520 : term567 = (True /\ False).
Proof. exact (MK_COMB (@lem2441519) (@lem2441516)). Qed.
Lemma lem2441522 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2441523 : term567 = False.
Proof. exact (TRANS (@lem2441520) (@lem2441522)). Qed.
Lemma lem2441524 : term557 = False.
Proof. exact (TRANS (@lem2441512) (@lem2441523)). Qed.
Lemma lem2441525 : term563 = False.
Proof. exact (TRANS (@lem2441509) (@lem2441524)). Qed.
Lemma lem2441526 : term560 = False.
Proof. exact (TRANS (@lem2441493) (@lem2441525)). Qed.
Lemma lem2441527 : term557 = False.
Proof. exact (TRANS (@lem2441470) (@lem2441526)). Qed.
Lemma lem2441528 : term556 = False.
Proof. exact (TRANS (@lem2441461) (@lem2441527)). Qed.
Lemma lem2441529 (n : int) (x : int) (y : int) (h1 : term446 n x y) : False.
Proof. exact (EQ_MP (@lem2441528) (@lem2441458 n x y h1)). Qed.
Lemma lem2441530 (n : int) (x : int) (y : int) (h1 : term449 n x y) : False.
Proof. exact (or_elim (@lem2439959 n x y h1) (fun h0 : term444 n x y => @lem2441125 n x y h0) (fun h0 : term446 n x y => @lem2441529 n x y h0)). Qed.
Lemma lem2441531 (n : int) (x : int) (y : int) (h1 : term493 n x y) : term493 n x y.
Proof. exact (h1). Qed.
Lemma lem2441532 (n : int) (x : int) (y : int) (h1 : term488 n x y) : term488 n x y.
Proof. exact (h1). Qed.
Lemma lem2441533 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term480 n x y.
Proof. exact (h1). Qed.
Lemma lem2441534 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term479 n x y.
Proof. exact (proj2 (@lem2441533 n x y h1)). Qed.
Lemma lem2441536 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term478 n x y.
Proof. exact (proj2 (@lem2441534 n x y h1)). Qed.
Lemma lem2441537 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term292 n x y.
Proof. exact (proj1 (@lem2441534 n x y h1)). Qed.
Lemma lem2441539 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term289 n x y.
Proof. exact (proj1 (@lem2441537 n x y h1)). Qed.
Lemma lem2441540 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term476 n x y.
Proof. exact (proj2 (@lem2441536 n x y h1)). Qed.
Lemma lem2441543 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term373 n x y.
Proof. exact (proj1 (@lem2441540 n x y h1)). Qed.
Lemma lem2441545 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term355 n x y.
Proof. exact (proj1 (@lem2441543 n x y h1)). Qed.
Lemma lem2441547 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2441548 : term496 = term497.
Proof. exact (@lem2441547 term95 term80). Qed.
Lemma lem2441550 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441551 : term80 = term134.
Proof. exact (@lem2441550 term81). Qed.
Lemma lem2441553 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441554 : term95 = term179.
Proof. exact (@lem2441553 (NUMERAL 0)). Qed.
Lemma lem2441555 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2441556 : term498 = term499.
Proof. exact (MK_COMB (@lem2441555) (@lem2441554)). Qed.
Lemma lem2441557 : term497 = term500.
Proof. exact (MK_COMB (@lem2441556) (@lem2441551)). Qed.
Lemma lem2441558 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2441560 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441561 : term497 = term503.
Proof. exact (@lem2441560 (NUMERAL 0) term81). Qed.
Lemma lem2441562 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441563 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441564 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441563 h1) (fun h1 : term503 = True => @lem2441562)). Qed.
Lemma lem2441565 : term503 = True.
Proof. exact (EQ_MP (@lem2441564) (@lem2441562)). Qed.
Lemma lem2441566 : term497 = True.
Proof. exact (TRANS (@lem2441561) (@lem2441565)). Qed.
Lemma lem2441567 : True = term497.
Proof. exact (SYM (@lem2441566)). Qed.
Lemma lem2441568 : term497.
Proof. exact (EQ_MP (@lem2441567) (@lem0)). Qed.
Lemma lem2441569 : term505.
Proof. exact (@lem2441558 (@lem2441568)). Qed.
Lemma lem2441571 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441572 : term497 = term503.
Proof. exact (@lem2441571 (NUMERAL 0) term81). Qed.
Lemma lem2441573 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441574 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441575 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441574 h1) (fun h1 : term503 = True => @lem2441573)). Qed.
Lemma lem2441576 : term503 = True.
Proof. exact (EQ_MP (@lem2441575) (@lem2441573)). Qed.
Lemma lem2441577 : term497 = True.
Proof. exact (TRANS (@lem2441572) (@lem2441576)). Qed.
Lemma lem2441578 : True = term497.
Proof. exact (SYM (@lem2441577)). Qed.
Lemma lem2441579 : term497.
Proof. exact (EQ_MP (@lem2441578) (@lem0)). Qed.
Lemma lem2441580 : term500 = term506.
Proof. exact (@lem2441569 (@lem2441579)). Qed.
Lemma lem2441582 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441583 : term145 = term146.
Proof. exact (@lem2441582 term81 term81). Qed.
Lemma lem2441584 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441585 : term148 = term81.
Proof. exact (EQ_MP (@lem2441584) (@lem940073)). Qed.
Lemma lem2441586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441587 : term146 = term80.
Proof. exact (MK_COMB (@lem2441586) (@lem2441585)). Qed.
Lemma lem2441588 : term145 = term80.
Proof. exact (TRANS (@lem2441583) (@lem2441587)). Qed.
Lemma lem2441590 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441591 : term508 = term95.
Proof. exact (@lem2441590 term81). Qed.
Lemma lem2441592 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2441593 : term509 = term498.
Proof. exact (MK_COMB (@lem2441592) (@lem2441591)). Qed.
Lemma lem2441594 : term506 = term497.
Proof. exact (MK_COMB (@lem2441593) (@lem2441588)). Qed.
Lemma lem2441596 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441597 : term497 = term503.
Proof. exact (@lem2441596 (NUMERAL 0) term81). Qed.
Lemma lem2441598 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441599 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441600 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441599 h1) (fun h1 : term503 = True => @lem2441598)). Qed.
Lemma lem2441601 : term503 = True.
Proof. exact (EQ_MP (@lem2441600) (@lem2441598)). Qed.
Lemma lem2441602 : term497 = True.
Proof. exact (TRANS (@lem2441597) (@lem2441601)). Qed.
Lemma lem2441603 : term506 = True.
Proof. exact (TRANS (@lem2441594) (@lem2441602)). Qed.
Lemma lem2441604 : term500 = True.
Proof. exact (TRANS (@lem2441580) (@lem2441603)). Qed.
Lemma lem2441605 : term497 = True.
Proof. exact (TRANS (@lem2441557) (@lem2441604)). Qed.
Lemma lem2441606 : term496 = True.
Proof. exact (TRANS (@lem2441548) (@lem2441605)). Qed.
Lemma lem2441607 : True = term496.
Proof. exact (SYM (@lem2441606)). Qed.
Lemma lem2441608 : term496.
Proof. exact (EQ_MP (@lem2441607) (@lem0)). Qed.
Lemma lem2441609 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term510 n x y.
Proof. exact (conj (@lem2441608) (@lem2441539 n x y h1)). Qed.
Lemma lem2441611 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2441612 (n : int) (x : int) (y : int) : term512 n x y.
Proof. exact (@lem2441611 term80 (term285 n x y)). Qed.
Lemma lem2441613 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term513 n x y.
Proof. exact (@lem2441612 n x y (@lem2441609 n x y h1)). Qed.
Lemma lem2441614 (n : int) (x : int) (y : int) : (term514 n x y) = (term285 n x y).
Proof. exact (@lem1982733 (term285 n x y)). Qed.
Lemma lem2441615 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2441616 (n : int) (x : int) (y : int) : (term515 n x y) = (term287 n x y).
Proof. exact (MK_COMB (@lem2441615) (@lem2441614 n x y)). Qed.
Lemma lem2441617 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2441618 (n : int) (x : int) (y : int) : (term513 n x y) = (term289 n x y).
Proof. exact (MK_COMB (@lem2441616 n x y) (@lem2441617)). Qed.
Lemma lem2441619 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term289 n x y.
Proof. exact (EQ_MP (@lem2441618 n x y) (@lem2441613 n x y h1)). Qed.
Lemma lem2441621 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2441622 : term496 = term497.
Proof. exact (@lem2441621 term95 term80). Qed.
Lemma lem2441624 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441625 : term80 = term134.
Proof. exact (@lem2441624 term81). Qed.
Lemma lem2441627 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441628 : term95 = term179.
Proof. exact (@lem2441627 (NUMERAL 0)). Qed.
Lemma lem2441629 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2441630 : term498 = term499.
Proof. exact (MK_COMB (@lem2441629) (@lem2441628)). Qed.
Lemma lem2441631 : term497 = term500.
Proof. exact (MK_COMB (@lem2441630) (@lem2441625)). Qed.
Lemma lem2441632 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2441634 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441635 : term497 = term503.
Proof. exact (@lem2441634 (NUMERAL 0) term81). Qed.
Lemma lem2441636 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441637 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441638 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441637 h1) (fun h1 : term503 = True => @lem2441636)). Qed.
Lemma lem2441639 : term503 = True.
Proof. exact (EQ_MP (@lem2441638) (@lem2441636)). Qed.
Lemma lem2441640 : term497 = True.
Proof. exact (TRANS (@lem2441635) (@lem2441639)). Qed.
Lemma lem2441641 : True = term497.
Proof. exact (SYM (@lem2441640)). Qed.
Lemma lem2441642 : term497.
Proof. exact (EQ_MP (@lem2441641) (@lem0)). Qed.
Lemma lem2441643 : term505.
Proof. exact (@lem2441632 (@lem2441642)). Qed.
Lemma lem2441645 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441646 : term497 = term503.
Proof. exact (@lem2441645 (NUMERAL 0) term81). Qed.
Lemma lem2441647 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441648 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441649 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441648 h1) (fun h1 : term503 = True => @lem2441647)). Qed.
Lemma lem2441650 : term503 = True.
Proof. exact (EQ_MP (@lem2441649) (@lem2441647)). Qed.
Lemma lem2441651 : term497 = True.
Proof. exact (TRANS (@lem2441646) (@lem2441650)). Qed.
Lemma lem2441652 : True = term497.
Proof. exact (SYM (@lem2441651)). Qed.
Lemma lem2441653 : term497.
Proof. exact (EQ_MP (@lem2441652) (@lem0)). Qed.
Lemma lem2441654 : term500 = term506.
Proof. exact (@lem2441643 (@lem2441653)). Qed.
Lemma lem2441656 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441657 : term145 = term146.
Proof. exact (@lem2441656 term81 term81). Qed.
Lemma lem2441658 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441659 : term148 = term81.
Proof. exact (EQ_MP (@lem2441658) (@lem940073)). Qed.
Lemma lem2441660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441661 : term146 = term80.
Proof. exact (MK_COMB (@lem2441660) (@lem2441659)). Qed.
Lemma lem2441662 : term145 = term80.
Proof. exact (TRANS (@lem2441657) (@lem2441661)). Qed.
Lemma lem2441664 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441665 : term508 = term95.
Proof. exact (@lem2441664 term81). Qed.
Lemma lem2441666 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2441667 : term509 = term498.
Proof. exact (MK_COMB (@lem2441666) (@lem2441665)). Qed.
Lemma lem2441668 : term506 = term497.
Proof. exact (MK_COMB (@lem2441667) (@lem2441662)). Qed.
Lemma lem2441670 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441671 : term497 = term503.
Proof. exact (@lem2441670 (NUMERAL 0) term81). Qed.
Lemma lem2441672 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441673 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441674 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441673 h1) (fun h1 : term503 = True => @lem2441672)). Qed.
Lemma lem2441675 : term503 = True.
Proof. exact (EQ_MP (@lem2441674) (@lem2441672)). Qed.
Lemma lem2441676 : term497 = True.
Proof. exact (TRANS (@lem2441671) (@lem2441675)). Qed.
Lemma lem2441677 : term506 = True.
Proof. exact (TRANS (@lem2441668) (@lem2441676)). Qed.
Lemma lem2441678 : term500 = True.
Proof. exact (TRANS (@lem2441654) (@lem2441677)). Qed.
Lemma lem2441679 : term497 = True.
Proof. exact (TRANS (@lem2441631) (@lem2441678)). Qed.
Lemma lem2441680 : term496 = True.
Proof. exact (TRANS (@lem2441622) (@lem2441679)). Qed.
Lemma lem2441681 : True = term496.
Proof. exact (SYM (@lem2441680)). Qed.
Lemma lem2441682 : term496.
Proof. exact (EQ_MP (@lem2441681) (@lem0)). Qed.
Lemma lem2441683 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term516 n x y.
Proof. exact (conj (@lem2441682) (@lem2441545 n x y h1)). Qed.
Lemma lem2441685 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2441686 (n : int) (x : int) (y : int) : term517 n x y.
Proof. exact (@lem2441685 term80 (term345 n x y)). Qed.
Lemma lem2441687 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term518 n x y.
Proof. exact (@lem2441686 n x y (@lem2441683 n x y h1)). Qed.
Lemma lem2441688 (n : int) (x : int) (y : int) : (term519 n x y) = (term345 n x y).
Proof. exact (@lem1982733 (term345 n x y)). Qed.
Lemma lem2441689 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2441690 (n : int) (x : int) (y : int) : (term520 n x y) = (term354 n x y).
Proof. exact (MK_COMB (@lem2441689) (@lem2441688 n x y)). Qed.
Lemma lem2441691 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2441692 (n : int) (x : int) (y : int) : (term518 n x y) = (term355 n x y).
Proof. exact (MK_COMB (@lem2441690 n x y) (@lem2441691)). Qed.
Lemma lem2441693 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term355 n x y.
Proof. exact (EQ_MP (@lem2441692 n x y) (@lem2441687 n x y h1)). Qed.
Lemma lem2441694 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term521 n x y.
Proof. exact (conj (@lem2441693 n x y h1) (@lem2441619 n x y h1)). Qed.
Lemma lem2441696 (x : real) (y : real) : term522 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2441697 (n : int) (x : int) (y : int) : term523 n x y.
Proof. exact (@lem2441696 (term345 n x y) (term285 n x y)). Qed.
Lemma lem2441698 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term524 n x y.
Proof. exact (@lem2441697 n x y (@lem2441694 n x y h1)). Qed.
Lemma lem2441699 (n : int) (x : int) (y : int) : (term525 n x y) = (term526 n x y).
Proof. exact (@lem1982753 (term201 n) (real_of_int n) (term122 x y) (term200 x y)). Qed.
Lemma lem2441700 (n : int) : (term527 n) = (term528 n).
Proof. exact (@lem1982713 term132 (real_of_int n)). Qed.
Lemma lem2441702 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441703 : term80 = term134.
Proof. exact (@lem2441702 term81). Qed.
Lemma lem2441705 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2441706 : term132 = term137.
Proof. exact (@lem2441705 term81). Qed.
Lemma lem2441707 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441708 : term529 = term530.
Proof. exact (MK_COMB (@lem2441707) (@lem2441706)). Qed.
Lemma lem2441709 : term531 = term532.
Proof. exact (MK_COMB (@lem2441708) (@lem2441703)). Qed.
Lemma lem2441710 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2441712 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441713 : term497 = term503.
Proof. exact (@lem2441712 (NUMERAL 0) term81). Qed.
Lemma lem2441714 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441715 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441716 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441715 h1) (fun h1 : term503 = True => @lem2441714)). Qed.
Lemma lem2441717 : term503 = True.
Proof. exact (EQ_MP (@lem2441716) (@lem2441714)). Qed.
Lemma lem2441718 : term497 = True.
Proof. exact (TRANS (@lem2441713) (@lem2441717)). Qed.
Lemma lem2441719 : True = term497.
Proof. exact (SYM (@lem2441718)). Qed.
Lemma lem2441720 : term497.
Proof. exact (EQ_MP (@lem2441719) (@lem0)). Qed.
Lemma lem2441721 : term534.
Proof. exact (@lem2441710 (@lem2441720)). Qed.
Lemma lem2441723 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441724 : term497 = term503.
Proof. exact (@lem2441723 (NUMERAL 0) term81). Qed.
Lemma lem2441725 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441726 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441727 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441726 h1) (fun h1 : term503 = True => @lem2441725)). Qed.
Lemma lem2441728 : term503 = True.
Proof. exact (EQ_MP (@lem2441727) (@lem2441725)). Qed.
Lemma lem2441729 : term497 = True.
Proof. exact (TRANS (@lem2441724) (@lem2441728)). Qed.
Lemma lem2441730 : True = term497.
Proof. exact (SYM (@lem2441729)). Qed.
Lemma lem2441731 : term497.
Proof. exact (EQ_MP (@lem2441730) (@lem0)). Qed.
Lemma lem2441732 : term535.
Proof. exact (@lem2441721 (@lem2441731)). Qed.
Lemma lem2441734 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441735 : term497 = term503.
Proof. exact (@lem2441734 (NUMERAL 0) term81). Qed.
Lemma lem2441736 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441737 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441738 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441737 h1) (fun h1 : term503 = True => @lem2441736)). Qed.
Lemma lem2441739 : term503 = True.
Proof. exact (EQ_MP (@lem2441738) (@lem2441736)). Qed.
Lemma lem2441740 : term497 = True.
Proof. exact (TRANS (@lem2441735) (@lem2441739)). Qed.
Lemma lem2441741 : True = term497.
Proof. exact (SYM (@lem2441740)). Qed.
Lemma lem2441742 : term497.
Proof. exact (EQ_MP (@lem2441741) (@lem0)). Qed.
Lemma lem2441743 : term536.
Proof. exact (@lem2441732 (@lem2441742)). Qed.
Lemma lem2441745 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441746 : term145 = term146.
Proof. exact (@lem2441745 term81 term81). Qed.
Lemma lem2441747 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441748 : term148 = term81.
Proof. exact (EQ_MP (@lem2441747) (@lem940073)). Qed.
Lemma lem2441749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441750 : term146 = term80.
Proof. exact (MK_COMB (@lem2441749) (@lem2441748)). Qed.
Lemma lem2441751 : term145 = term80.
Proof. exact (TRANS (@lem2441746) (@lem2441750)). Qed.
Lemma lem2441753 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2441754 : term140 = term151.
Proof. exact (@lem2441753 term81 term81). Qed.
Lemma lem2441755 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441756 : term148 = term81.
Proof. exact (EQ_MP (@lem2441755) (@lem940073)). Qed.
Lemma lem2441757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441758 : term146 = term80.
Proof. exact (MK_COMB (@lem2441757) (@lem2441756)). Qed.
Lemma lem2441759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2441760 : term151 = term132.
Proof. exact (MK_COMB (@lem2441759) (@lem2441758)). Qed.
Lemma lem2441761 : term140 = term132.
Proof. exact (TRANS (@lem2441754) (@lem2441760)). Qed.
Lemma lem2441762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441763 : term537 = term529.
Proof. exact (MK_COMB (@lem2441762) (@lem2441761)). Qed.
Lemma lem2441764 : term538 = term531.
Proof. exact (MK_COMB (@lem2441763) (@lem2441751)). Qed.
Lemma lem2441766 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2441767 : term531 = term95.
Proof. exact (@lem2441766 term81). Qed.
Lemma lem2441768 : term538 = term95.
Proof. exact (TRANS (@lem2441764) (@lem2441767)). Qed.
Lemma lem2441769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441770 : term540 = term541.
Proof. exact (MK_COMB (@lem2441769) (@lem2441768)). Qed.
Lemma lem2441771 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2441772 : term542 = term508.
Proof. exact (MK_COMB (@lem2441770) (@lem2441771)). Qed.
Lemma lem2441774 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441775 : term508 = term95.
Proof. exact (@lem2441774 term81). Qed.
Lemma lem2441776 : term542 = term95.
Proof. exact (TRANS (@lem2441772) (@lem2441775)). Qed.
Lemma lem2441778 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441779 : term145 = term146.
Proof. exact (@lem2441778 term81 term81). Qed.
Lemma lem2441780 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441781 : term148 = term81.
Proof. exact (EQ_MP (@lem2441780) (@lem940073)). Qed.
Lemma lem2441782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441783 : term146 = term80.
Proof. exact (MK_COMB (@lem2441782) (@lem2441781)). Qed.
Lemma lem2441784 : term145 = term80.
Proof. exact (TRANS (@lem2441779) (@lem2441783)). Qed.
Lemma lem2441785 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2441786 : term543 = term508.
Proof. exact (MK_COMB (@lem2441785) (@lem2441784)). Qed.
Lemma lem2441788 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441789 : term508 = term95.
Proof. exact (@lem2441788 term81). Qed.
Lemma lem2441790 : term543 = term95.
Proof. exact (TRANS (@lem2441786) (@lem2441789)). Qed.
Lemma lem2441791 : term95 = term543.
Proof. exact (SYM (@lem2441790)). Qed.
Lemma lem2441792 : term542 = term543.
Proof. exact (TRANS (@lem2441776) (@lem2441791)). Qed.
Lemma lem2441793 : term532 = term179.
Proof. exact (@lem2441743 (@lem2441792)). Qed.
Lemma lem2441794 : term531 = term179.
Proof. exact (TRANS (@lem2441709) (@lem2441793)). Qed.
Lemma lem2441796 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2441797 : term179 = term95.
Proof. exact (@lem2441796 term95). Qed.
Lemma lem2441798 : term531 = term95.
Proof. exact (TRANS (@lem2441794) (@lem2441797)). Qed.
Lemma lem2441799 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441800 : term544 = term541.
Proof. exact (MK_COMB (@lem2441799) (@lem2441798)). Qed.
Lemma lem2441801 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2441802 (n : int) : (term528 n) = (term545 n).
Proof. exact (MK_COMB (@lem2441800) (@lem2441801 n)). Qed.
Lemma lem2441803 (n : int) : (term527 n) = (term545 n).
Proof. exact (TRANS (@lem2441700 n) (@lem2441802 n)). Qed.
Lemma lem2441804 (n : int) : (term545 n) = term95.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2441805 (n : int) : (term527 n) = term95.
Proof. exact (TRANS (@lem2441803 n) (@lem2441804 n)). Qed.
Lemma lem2441806 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441807 (n : int) : (term546 n) = term392.
Proof. exact (MK_COMB (@lem2441806) (@lem2441805 n)). Qed.
Lemma lem2441808 (x : int) (y : int) : (term547 x y) = (term548 x y).
Proof. exact (@lem1982753 (real_of_int x) (term201 x) (term201 y) (term251 y)). Qed.
Lemma lem2441809 (x : int) : (term549 x) = (term528 x).
Proof. exact (@lem1982715 term132 (real_of_int x)). Qed.
Lemma lem2441811 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441812 : term80 = term134.
Proof. exact (@lem2441811 term81). Qed.
Lemma lem2441814 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2441815 : term132 = term137.
Proof. exact (@lem2441814 term81). Qed.
Lemma lem2441816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441817 : term529 = term530.
Proof. exact (MK_COMB (@lem2441816) (@lem2441815)). Qed.
Lemma lem2441818 : term531 = term532.
Proof. exact (MK_COMB (@lem2441817) (@lem2441812)). Qed.
Lemma lem2441819 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2441821 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441822 : term497 = term503.
Proof. exact (@lem2441821 (NUMERAL 0) term81). Qed.
Lemma lem2441823 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441824 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441825 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441824 h1) (fun h1 : term503 = True => @lem2441823)). Qed.
Lemma lem2441826 : term503 = True.
Proof. exact (EQ_MP (@lem2441825) (@lem2441823)). Qed.
Lemma lem2441827 : term497 = True.
Proof. exact (TRANS (@lem2441822) (@lem2441826)). Qed.
Lemma lem2441828 : True = term497.
Proof. exact (SYM (@lem2441827)). Qed.
Lemma lem2441829 : term497.
Proof. exact (EQ_MP (@lem2441828) (@lem0)). Qed.
Lemma lem2441830 : term534.
Proof. exact (@lem2441819 (@lem2441829)). Qed.
Lemma lem2441832 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441833 : term497 = term503.
Proof. exact (@lem2441832 (NUMERAL 0) term81). Qed.
Lemma lem2441834 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441835 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441836 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441835 h1) (fun h1 : term503 = True => @lem2441834)). Qed.
Lemma lem2441837 : term503 = True.
Proof. exact (EQ_MP (@lem2441836) (@lem2441834)). Qed.
Lemma lem2441838 : term497 = True.
Proof. exact (TRANS (@lem2441833) (@lem2441837)). Qed.
Lemma lem2441839 : True = term497.
Proof. exact (SYM (@lem2441838)). Qed.
Lemma lem2441840 : term497.
Proof. exact (EQ_MP (@lem2441839) (@lem0)). Qed.
Lemma lem2441841 : term535.
Proof. exact (@lem2441830 (@lem2441840)). Qed.
Lemma lem2441843 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441844 : term497 = term503.
Proof. exact (@lem2441843 (NUMERAL 0) term81). Qed.
Lemma lem2441845 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441846 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441847 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441846 h1) (fun h1 : term503 = True => @lem2441845)). Qed.
Lemma lem2441848 : term503 = True.
Proof. exact (EQ_MP (@lem2441847) (@lem2441845)). Qed.
Lemma lem2441849 : term497 = True.
Proof. exact (TRANS (@lem2441844) (@lem2441848)). Qed.
Lemma lem2441850 : True = term497.
Proof. exact (SYM (@lem2441849)). Qed.
Lemma lem2441851 : term497.
Proof. exact (EQ_MP (@lem2441850) (@lem0)). Qed.
Lemma lem2441852 : term536.
Proof. exact (@lem2441841 (@lem2441851)). Qed.
Lemma lem2441854 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441855 : term145 = term146.
Proof. exact (@lem2441854 term81 term81). Qed.
Lemma lem2441856 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441857 : term148 = term81.
Proof. exact (EQ_MP (@lem2441856) (@lem940073)). Qed.
Lemma lem2441858 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441859 : term146 = term80.
Proof. exact (MK_COMB (@lem2441858) (@lem2441857)). Qed.
Lemma lem2441860 : term145 = term80.
Proof. exact (TRANS (@lem2441855) (@lem2441859)). Qed.
Lemma lem2441862 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2441863 : term140 = term151.
Proof. exact (@lem2441862 term81 term81). Qed.
Lemma lem2441864 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441865 : term148 = term81.
Proof. exact (EQ_MP (@lem2441864) (@lem940073)). Qed.
Lemma lem2441866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441867 : term146 = term80.
Proof. exact (MK_COMB (@lem2441866) (@lem2441865)). Qed.
Lemma lem2441868 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2441869 : term151 = term132.
Proof. exact (MK_COMB (@lem2441868) (@lem2441867)). Qed.
Lemma lem2441870 : term140 = term132.
Proof. exact (TRANS (@lem2441863) (@lem2441869)). Qed.
Lemma lem2441871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441872 : term537 = term529.
Proof. exact (MK_COMB (@lem2441871) (@lem2441870)). Qed.
Lemma lem2441873 : term538 = term531.
Proof. exact (MK_COMB (@lem2441872) (@lem2441860)). Qed.
Lemma lem2441875 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2441876 : term531 = term95.
Proof. exact (@lem2441875 term81). Qed.
Lemma lem2441877 : term538 = term95.
Proof. exact (TRANS (@lem2441873) (@lem2441876)). Qed.
Lemma lem2441878 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441879 : term540 = term541.
Proof. exact (MK_COMB (@lem2441878) (@lem2441877)). Qed.
Lemma lem2441880 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2441881 : term542 = term508.
Proof. exact (MK_COMB (@lem2441879) (@lem2441880)). Qed.
Lemma lem2441883 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441884 : term508 = term95.
Proof. exact (@lem2441883 term81). Qed.
Lemma lem2441885 : term542 = term95.
Proof. exact (TRANS (@lem2441881) (@lem2441884)). Qed.
Lemma lem2441887 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441888 : term145 = term146.
Proof. exact (@lem2441887 term81 term81). Qed.
Lemma lem2441889 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441890 : term148 = term81.
Proof. exact (EQ_MP (@lem2441889) (@lem940073)). Qed.
Lemma lem2441891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441892 : term146 = term80.
Proof. exact (MK_COMB (@lem2441891) (@lem2441890)). Qed.
Lemma lem2441893 : term145 = term80.
Proof. exact (TRANS (@lem2441888) (@lem2441892)). Qed.
Lemma lem2441894 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2441895 : term543 = term508.
Proof. exact (MK_COMB (@lem2441894) (@lem2441893)). Qed.
Lemma lem2441897 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441898 : term508 = term95.
Proof. exact (@lem2441897 term81). Qed.
Lemma lem2441899 : term543 = term95.
Proof. exact (TRANS (@lem2441895) (@lem2441898)). Qed.
Lemma lem2441900 : term95 = term543.
Proof. exact (SYM (@lem2441899)). Qed.
Lemma lem2441901 : term542 = term543.
Proof. exact (TRANS (@lem2441885) (@lem2441900)). Qed.
Lemma lem2441902 : term532 = term179.
Proof. exact (@lem2441852 (@lem2441901)). Qed.
Lemma lem2441903 : term531 = term179.
Proof. exact (TRANS (@lem2441818) (@lem2441902)). Qed.
Lemma lem2441905 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2441906 : term179 = term95.
Proof. exact (@lem2441905 term95). Qed.
Lemma lem2441907 : term531 = term95.
Proof. exact (TRANS (@lem2441903) (@lem2441906)). Qed.
Lemma lem2441908 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441909 : term544 = term541.
Proof. exact (MK_COMB (@lem2441908) (@lem2441907)). Qed.
Lemma lem2441910 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2441911 (x : int) : (term528 x) = (term545 x).
Proof. exact (MK_COMB (@lem2441909) (@lem2441910 x)). Qed.
Lemma lem2441912 (x : int) : (term549 x) = (term545 x).
Proof. exact (TRANS (@lem2441809 x) (@lem2441911 x)). Qed.
Lemma lem2441913 (x : int) : (term545 x) = term95.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2441914 (x : int) : (term549 x) = term95.
Proof. exact (TRANS (@lem2441912 x) (@lem2441913 x)). Qed.
Lemma lem2441915 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441916 (x : int) : (term550 x) = term392.
Proof. exact (MK_COMB (@lem2441915) (@lem2441914 x)). Qed.
Lemma lem2441917 (y : int) : (term551 y) = (term552 y).
Proof. exact (@lem1982763 (term201 y) (real_of_int y) term132). Qed.
Lemma lem2441918 (y : int) : (term527 y) = (term528 y).
Proof. exact (@lem1982713 term132 (real_of_int y)). Qed.
Lemma lem2441920 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2441921 : term80 = term134.
Proof. exact (@lem2441920 term81). Qed.
Lemma lem2441923 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2441924 : term132 = term137.
Proof. exact (@lem2441923 term81). Qed.
Lemma lem2441925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441926 : term529 = term530.
Proof. exact (MK_COMB (@lem2441925) (@lem2441924)). Qed.
Lemma lem2441927 : term531 = term532.
Proof. exact (MK_COMB (@lem2441926) (@lem2441921)). Qed.
Lemma lem2441928 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2441930 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441931 : term497 = term503.
Proof. exact (@lem2441930 (NUMERAL 0) term81). Qed.
Lemma lem2441932 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441933 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441934 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441933 h1) (fun h1 : term503 = True => @lem2441932)). Qed.
Lemma lem2441935 : term503 = True.
Proof. exact (EQ_MP (@lem2441934) (@lem2441932)). Qed.
Lemma lem2441936 : term497 = True.
Proof. exact (TRANS (@lem2441931) (@lem2441935)). Qed.
Lemma lem2441937 : True = term497.
Proof. exact (SYM (@lem2441936)). Qed.
Lemma lem2441938 : term497.
Proof. exact (EQ_MP (@lem2441937) (@lem0)). Qed.
Lemma lem2441939 : term534.
Proof. exact (@lem2441928 (@lem2441938)). Qed.
Lemma lem2441941 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441942 : term497 = term503.
Proof. exact (@lem2441941 (NUMERAL 0) term81). Qed.
Lemma lem2441943 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441944 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441945 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441944 h1) (fun h1 : term503 = True => @lem2441943)). Qed.
Lemma lem2441946 : term503 = True.
Proof. exact (EQ_MP (@lem2441945) (@lem2441943)). Qed.
Lemma lem2441947 : term497 = True.
Proof. exact (TRANS (@lem2441942) (@lem2441946)). Qed.
Lemma lem2441948 : True = term497.
Proof. exact (SYM (@lem2441947)). Qed.
Lemma lem2441949 : term497.
Proof. exact (EQ_MP (@lem2441948) (@lem0)). Qed.
Lemma lem2441950 : term535.
Proof. exact (@lem2441939 (@lem2441949)). Qed.
Lemma lem2441952 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2441953 : term497 = term503.
Proof. exact (@lem2441952 (NUMERAL 0) term81). Qed.
Lemma lem2441954 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2441955 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2441956 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2441955 h1) (fun h1 : term503 = True => @lem2441954)). Qed.
Lemma lem2441957 : term503 = True.
Proof. exact (EQ_MP (@lem2441956) (@lem2441954)). Qed.
Lemma lem2441958 : term497 = True.
Proof. exact (TRANS (@lem2441953) (@lem2441957)). Qed.
Lemma lem2441959 : True = term497.
Proof. exact (SYM (@lem2441958)). Qed.
Lemma lem2441960 : term497.
Proof. exact (EQ_MP (@lem2441959) (@lem0)). Qed.
Lemma lem2441961 : term536.
Proof. exact (@lem2441950 (@lem2441960)). Qed.
Lemma lem2441963 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441964 : term145 = term146.
Proof. exact (@lem2441963 term81 term81). Qed.
Lemma lem2441965 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441966 : term148 = term81.
Proof. exact (EQ_MP (@lem2441965) (@lem940073)). Qed.
Lemma lem2441967 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441968 : term146 = term80.
Proof. exact (MK_COMB (@lem2441967) (@lem2441966)). Qed.
Lemma lem2441969 : term145 = term80.
Proof. exact (TRANS (@lem2441964) (@lem2441968)). Qed.
Lemma lem2441971 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2441972 : term140 = term151.
Proof. exact (@lem2441971 term81 term81). Qed.
Lemma lem2441973 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441974 : term148 = term81.
Proof. exact (EQ_MP (@lem2441973) (@lem940073)). Qed.
Lemma lem2441975 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2441976 : term146 = term80.
Proof. exact (MK_COMB (@lem2441975) (@lem2441974)). Qed.
Lemma lem2441977 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2441978 : term151 = term132.
Proof. exact (MK_COMB (@lem2441977) (@lem2441976)). Qed.
Lemma lem2441979 : term140 = term132.
Proof. exact (TRANS (@lem2441972) (@lem2441978)). Qed.
Lemma lem2441980 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2441981 : term537 = term529.
Proof. exact (MK_COMB (@lem2441980) (@lem2441979)). Qed.
Lemma lem2441982 : term538 = term531.
Proof. exact (MK_COMB (@lem2441981) (@lem2441969)). Qed.
Lemma lem2441984 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2441985 : term531 = term95.
Proof. exact (@lem2441984 term81). Qed.
Lemma lem2441986 : term538 = term95.
Proof. exact (TRANS (@lem2441982) (@lem2441985)). Qed.
Lemma lem2441987 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2441988 : term540 = term541.
Proof. exact (MK_COMB (@lem2441987) (@lem2441986)). Qed.
Lemma lem2441989 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2441990 : term542 = term508.
Proof. exact (MK_COMB (@lem2441988) (@lem2441989)). Qed.
Lemma lem2441992 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2441993 : term508 = term95.
Proof. exact (@lem2441992 term81). Qed.
Lemma lem2441994 : term542 = term95.
Proof. exact (TRANS (@lem2441990) (@lem2441993)). Qed.
Lemma lem2441996 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2441997 : term145 = term146.
Proof. exact (@lem2441996 term81 term81). Qed.
Lemma lem2441998 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2441999 : term148 = term81.
Proof. exact (EQ_MP (@lem2441998) (@lem940073)). Qed.
Lemma lem2442000 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442001 : term146 = term80.
Proof. exact (MK_COMB (@lem2442000) (@lem2441999)). Qed.
Lemma lem2442002 : term145 = term80.
Proof. exact (TRANS (@lem2441997) (@lem2442001)). Qed.
Lemma lem2442003 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2442004 : term543 = term508.
Proof. exact (MK_COMB (@lem2442003) (@lem2442002)). Qed.
Lemma lem2442006 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442007 : term508 = term95.
Proof. exact (@lem2442006 term81). Qed.
Lemma lem2442008 : term543 = term95.
Proof. exact (TRANS (@lem2442004) (@lem2442007)). Qed.
Lemma lem2442009 : term95 = term543.
Proof. exact (SYM (@lem2442008)). Qed.
Lemma lem2442010 : term542 = term543.
Proof. exact (TRANS (@lem2441994) (@lem2442009)). Qed.
Lemma lem2442011 : term532 = term179.
Proof. exact (@lem2441961 (@lem2442010)). Qed.
Lemma lem2442012 : term531 = term179.
Proof. exact (TRANS (@lem2441927) (@lem2442011)). Qed.
Lemma lem2442014 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2442015 : term179 = term95.
Proof. exact (@lem2442014 term95). Qed.
Lemma lem2442016 : term531 = term95.
Proof. exact (TRANS (@lem2442012) (@lem2442015)). Qed.
Lemma lem2442017 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442018 : term544 = term541.
Proof. exact (MK_COMB (@lem2442017) (@lem2442016)). Qed.
Lemma lem2442019 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2442020 (y : int) : (term528 y) = (term545 y).
Proof. exact (MK_COMB (@lem2442018) (@lem2442019 y)). Qed.
Lemma lem2442021 (y : int) : (term527 y) = (term545 y).
Proof. exact (TRANS (@lem2441918 y) (@lem2442020 y)). Qed.
Lemma lem2442022 (y : int) : (term545 y) = term95.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2442023 (y : int) : (term527 y) = term95.
Proof. exact (TRANS (@lem2442021 y) (@lem2442022 y)). Qed.
Lemma lem2442024 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442025 (y : int) : (term546 y) = term392.
Proof. exact (MK_COMB (@lem2442024) (@lem2442023 y)). Qed.
Lemma lem2442026 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem2442027 (y : int) : (term552 y) = term553.
Proof. exact (MK_COMB (@lem2442025 y) (@lem2442026)). Qed.
Lemma lem2442028 (y : int) : (term551 y) = term553.
Proof. exact (TRANS (@lem2441917 y) (@lem2442027 y)). Qed.
Lemma lem2442029 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2442030 (y : int) : (term551 y) = term132.
Proof. exact (TRANS (@lem2442028 y) (@lem2442029)). Qed.
Lemma lem2442031 (x : int) (y : int) : (term548 x y) = term553.
Proof. exact (MK_COMB (@lem2441916 x) (@lem2442030 y)). Qed.
Lemma lem2442032 (x : int) (y : int) : (term547 x y) = term553.
Proof. exact (TRANS (@lem2441808 x y) (@lem2442031 x y)). Qed.
Lemma lem2442033 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2442034 (x : int) (y : int) : (term547 x y) = term132.
Proof. exact (TRANS (@lem2442032 x y) (@lem2442033)). Qed.
Lemma lem2442035 (n : int) (x : int) (y : int) : (term526 n x y) = term553.
Proof. exact (MK_COMB (@lem2441807 n) (@lem2442034 x y)). Qed.
Lemma lem2442036 (n : int) (x : int) (y : int) : (term525 n x y) = term553.
Proof. exact (TRANS (@lem2441699 n x y) (@lem2442035 n x y)). Qed.
Lemma lem2442037 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2442038 (n : int) (x : int) (y : int) : (term525 n x y) = term132.
Proof. exact (TRANS (@lem2442036 n x y) (@lem2442037)). Qed.
Lemma lem2442039 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2442040 (n : int) (x : int) (y : int) : (term554 n x y) = term555.
Proof. exact (MK_COMB (@lem2442039) (@lem2442038 n x y)). Qed.
Lemma lem2442041 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2442042 (n : int) (x : int) (y : int) : (term524 n x y) = term556.
Proof. exact (MK_COMB (@lem2442040 n x y) (@lem2442041)). Qed.
Lemma lem2442043 (n : int) (x : int) (y : int) (h1 : term480 n x y) : term556.
Proof. exact (EQ_MP (@lem2442042 n x y) (@lem2441698 n x y h1)). Qed.
Lemma lem2442045 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2442046 : term556 = term557.
Proof. exact (@lem2442045 term95 term132). Qed.
Lemma lem2442048 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442049 : term132 = term137.
Proof. exact (@lem2442048 term81). Qed.
Lemma lem2442051 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442052 : term95 = term179.
Proof. exact (@lem2442051 (NUMERAL 0)). Qed.
Lemma lem2442053 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2442054 : term558 = term559.
Proof. exact (MK_COMB (@lem2442053) (@lem2442052)). Qed.
Lemma lem2442055 : term557 = term560.
Proof. exact (MK_COMB (@lem2442054) (@lem2442049)). Qed.
Lemma lem2442056 : term561.
Proof. exact (@lem1980026 term95 term80 term132 term80). Qed.
Lemma lem2442058 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442059 : term497 = term503.
Proof. exact (@lem2442058 (NUMERAL 0) term81). Qed.
Lemma lem2442060 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442061 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442062 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442061 h1) (fun h1 : term503 = True => @lem2442060)). Qed.
Lemma lem2442063 : term503 = True.
Proof. exact (EQ_MP (@lem2442062) (@lem2442060)). Qed.
Lemma lem2442064 : term497 = True.
Proof. exact (TRANS (@lem2442059) (@lem2442063)). Qed.
Lemma lem2442065 : True = term497.
Proof. exact (SYM (@lem2442064)). Qed.
Lemma lem2442066 : term497.
Proof. exact (EQ_MP (@lem2442065) (@lem0)). Qed.
Lemma lem2442067 : term562.
Proof. exact (@lem2442056 (@lem2442066)). Qed.
Lemma lem2442069 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442070 : term497 = term503.
Proof. exact (@lem2442069 (NUMERAL 0) term81). Qed.
Lemma lem2442071 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442072 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442073 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442072 h1) (fun h1 : term503 = True => @lem2442071)). Qed.
Lemma lem2442074 : term503 = True.
Proof. exact (EQ_MP (@lem2442073) (@lem2442071)). Qed.
Lemma lem2442075 : term497 = True.
Proof. exact (TRANS (@lem2442070) (@lem2442074)). Qed.
Lemma lem2442076 : True = term497.
Proof. exact (SYM (@lem2442075)). Qed.
Lemma lem2442077 : term497.
Proof. exact (EQ_MP (@lem2442076) (@lem0)). Qed.
Lemma lem2442078 : term560 = term563.
Proof. exact (@lem2442067 (@lem2442077)). Qed.
Lemma lem2442080 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2442081 : term140 = term151.
Proof. exact (@lem2442080 term81 term81). Qed.
Lemma lem2442082 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442083 : term148 = term81.
Proof. exact (EQ_MP (@lem2442082) (@lem940073)). Qed.
Lemma lem2442084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442085 : term146 = term80.
Proof. exact (MK_COMB (@lem2442084) (@lem2442083)). Qed.
Lemma lem2442086 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2442087 : term151 = term132.
Proof. exact (MK_COMB (@lem2442086) (@lem2442085)). Qed.
Lemma lem2442088 : term140 = term132.
Proof. exact (TRANS (@lem2442081) (@lem2442087)). Qed.
Lemma lem2442090 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442091 : term508 = term95.
Proof. exact (@lem2442090 term81). Qed.
Lemma lem2442092 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2442093 : term564 = term558.
Proof. exact (MK_COMB (@lem2442092) (@lem2442091)). Qed.
Lemma lem2442094 : term563 = term557.
Proof. exact (MK_COMB (@lem2442093) (@lem2442088)). Qed.
Lemma lem2442096 (m : nat) (n : nat) : (term565 m n) = (term566 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2442097 : term557 = term567.
Proof. exact (@lem2442096 (NUMERAL 0) term81). Qed.
Lemma lem2442098 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442099 (h1 : term504 = (BIT1 0)) : (term81 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2442100 : (term504 = (BIT1 0)) = ((term81 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442099 h1) (fun h1 : (term81 = (NUMERAL 0)) = False => @lem2442098)). Qed.
Lemma lem2442101 : (term81 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2442100) (@lem2442098)). Qed.
Lemma lem2442102 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2442103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2442104 : term568 = (and True).
Proof. exact (MK_COMB (@lem2442103) (@lem2442102)). Qed.
Lemma lem2442105 : term567 = (True /\ False).
Proof. exact (MK_COMB (@lem2442104) (@lem2442101)). Qed.
Lemma lem2442107 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2442108 : term567 = False.
Proof. exact (TRANS (@lem2442105) (@lem2442107)). Qed.
Lemma lem2442109 : term557 = False.
Proof. exact (TRANS (@lem2442097) (@lem2442108)). Qed.
Lemma lem2442110 : term563 = False.
Proof. exact (TRANS (@lem2442094) (@lem2442109)). Qed.
Lemma lem2442111 : term560 = False.
Proof. exact (TRANS (@lem2442078) (@lem2442110)). Qed.
Lemma lem2442112 : term557 = False.
Proof. exact (TRANS (@lem2442055) (@lem2442111)). Qed.
Lemma lem2442113 : term556 = False.
Proof. exact (TRANS (@lem2442046) (@lem2442112)). Qed.
Lemma lem2442114 (n : int) (x : int) (y : int) (h1 : term480 n x y) : False.
Proof. exact (EQ_MP (@lem2442113) (@lem2442043 n x y h1)). Qed.
Lemma lem2442115 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term486 n x y.
Proof. exact (h1). Qed.
Lemma lem2442116 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term485 n x y.
Proof. exact (proj2 (@lem2442115 n x y h1)). Qed.
Lemma lem2442118 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term484 n x y.
Proof. exact (proj2 (@lem2442116 n x y h1)). Qed.
Lemma lem2442119 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term292 n x y.
Proof. exact (proj1 (@lem2442116 n x y h1)). Qed.
Lemma lem2442120 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term264 n x y.
Proof. exact (proj2 (@lem2442119 n x y h1)). Qed.
Lemma lem2442122 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term482 n x y.
Proof. exact (proj2 (@lem2442118 n x y h1)). Qed.
Lemma lem2442125 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term433 n x y.
Proof. exact (proj1 (@lem2442122 n x y h1)). Qed.
Lemma lem2442127 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term414 n x y.
Proof. exact (proj1 (@lem2442125 n x y h1)). Qed.
Lemma lem2442129 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2442130 : term496 = term497.
Proof. exact (@lem2442129 term95 term80). Qed.
Lemma lem2442132 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442133 : term80 = term134.
Proof. exact (@lem2442132 term81). Qed.
Lemma lem2442135 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442136 : term95 = term179.
Proof. exact (@lem2442135 (NUMERAL 0)). Qed.
Lemma lem2442137 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2442138 : term498 = term499.
Proof. exact (MK_COMB (@lem2442137) (@lem2442136)). Qed.
Lemma lem2442139 : term497 = term500.
Proof. exact (MK_COMB (@lem2442138) (@lem2442133)). Qed.
Lemma lem2442140 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2442142 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442143 : term497 = term503.
Proof. exact (@lem2442142 (NUMERAL 0) term81). Qed.
Lemma lem2442144 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442145 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442146 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442145 h1) (fun h1 : term503 = True => @lem2442144)). Qed.
Lemma lem2442147 : term503 = True.
Proof. exact (EQ_MP (@lem2442146) (@lem2442144)). Qed.
Lemma lem2442148 : term497 = True.
Proof. exact (TRANS (@lem2442143) (@lem2442147)). Qed.
Lemma lem2442149 : True = term497.
Proof. exact (SYM (@lem2442148)). Qed.
Lemma lem2442150 : term497.
Proof. exact (EQ_MP (@lem2442149) (@lem0)). Qed.
Lemma lem2442151 : term505.
Proof. exact (@lem2442140 (@lem2442150)). Qed.
Lemma lem2442153 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442154 : term497 = term503.
Proof. exact (@lem2442153 (NUMERAL 0) term81). Qed.
Lemma lem2442155 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442156 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442157 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442156 h1) (fun h1 : term503 = True => @lem2442155)). Qed.
Lemma lem2442158 : term503 = True.
Proof. exact (EQ_MP (@lem2442157) (@lem2442155)). Qed.
Lemma lem2442159 : term497 = True.
Proof. exact (TRANS (@lem2442154) (@lem2442158)). Qed.
Lemma lem2442160 : True = term497.
Proof. exact (SYM (@lem2442159)). Qed.
Lemma lem2442161 : term497.
Proof. exact (EQ_MP (@lem2442160) (@lem0)). Qed.
Lemma lem2442162 : term500 = term506.
Proof. exact (@lem2442151 (@lem2442161)). Qed.
Lemma lem2442164 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442165 : term145 = term146.
Proof. exact (@lem2442164 term81 term81). Qed.
Lemma lem2442166 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442167 : term148 = term81.
Proof. exact (EQ_MP (@lem2442166) (@lem940073)). Qed.
Lemma lem2442168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442169 : term146 = term80.
Proof. exact (MK_COMB (@lem2442168) (@lem2442167)). Qed.
Lemma lem2442170 : term145 = term80.
Proof. exact (TRANS (@lem2442165) (@lem2442169)). Qed.
Lemma lem2442172 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442173 : term508 = term95.
Proof. exact (@lem2442172 term81). Qed.
Lemma lem2442174 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2442175 : term509 = term498.
Proof. exact (MK_COMB (@lem2442174) (@lem2442173)). Qed.
Lemma lem2442176 : term506 = term497.
Proof. exact (MK_COMB (@lem2442175) (@lem2442170)). Qed.
Lemma lem2442178 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442179 : term497 = term503.
Proof. exact (@lem2442178 (NUMERAL 0) term81). Qed.
Lemma lem2442180 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442181 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442182 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442181 h1) (fun h1 : term503 = True => @lem2442180)). Qed.
Lemma lem2442183 : term503 = True.
Proof. exact (EQ_MP (@lem2442182) (@lem2442180)). Qed.
Lemma lem2442184 : term497 = True.
Proof. exact (TRANS (@lem2442179) (@lem2442183)). Qed.
Lemma lem2442185 : term506 = True.
Proof. exact (TRANS (@lem2442176) (@lem2442184)). Qed.
Lemma lem2442186 : term500 = True.
Proof. exact (TRANS (@lem2442162) (@lem2442185)). Qed.
Lemma lem2442187 : term497 = True.
Proof. exact (TRANS (@lem2442139) (@lem2442186)). Qed.
Lemma lem2442188 : term496 = True.
Proof. exact (TRANS (@lem2442130) (@lem2442187)). Qed.
Lemma lem2442189 : True = term496.
Proof. exact (SYM (@lem2442188)). Qed.
Lemma lem2442190 : term496.
Proof. exact (EQ_MP (@lem2442189) (@lem0)). Qed.
Lemma lem2442191 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term569 n x y.
Proof. exact (conj (@lem2442190) (@lem2442120 n x y h1)). Qed.
Lemma lem2442193 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2442194 (n : int) (x : int) (y : int) : term570 n x y.
Proof. exact (@lem2442193 term80 (term260 n x y)). Qed.
Lemma lem2442195 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term571 n x y.
Proof. exact (@lem2442194 n x y (@lem2442191 n x y h1)). Qed.
Lemma lem2442196 (n : int) (x : int) (y : int) : (term572 n x y) = (term260 n x y).
Proof. exact (@lem1982733 (term260 n x y)). Qed.
Lemma lem2442197 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2442198 (n : int) (x : int) (y : int) : (term573 n x y) = (term262 n x y).
Proof. exact (MK_COMB (@lem2442197) (@lem2442196 n x y)). Qed.
Lemma lem2442199 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2442200 (n : int) (x : int) (y : int) : (term571 n x y) = (term264 n x y).
Proof. exact (MK_COMB (@lem2442198 n x y) (@lem2442199)). Qed.
Lemma lem2442201 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term264 n x y.
Proof. exact (EQ_MP (@lem2442200 n x y) (@lem2442195 n x y h1)). Qed.
Lemma lem2442203 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2442204 : term496 = term497.
Proof. exact (@lem2442203 term95 term80). Qed.
Lemma lem2442206 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442207 : term80 = term134.
Proof. exact (@lem2442206 term81). Qed.
Lemma lem2442209 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442210 : term95 = term179.
Proof. exact (@lem2442209 (NUMERAL 0)). Qed.
Lemma lem2442211 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2442212 : term498 = term499.
Proof. exact (MK_COMB (@lem2442211) (@lem2442210)). Qed.
Lemma lem2442213 : term497 = term500.
Proof. exact (MK_COMB (@lem2442212) (@lem2442207)). Qed.
Lemma lem2442214 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2442216 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442217 : term497 = term503.
Proof. exact (@lem2442216 (NUMERAL 0) term81). Qed.
Lemma lem2442218 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442219 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442220 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442219 h1) (fun h1 : term503 = True => @lem2442218)). Qed.
Lemma lem2442221 : term503 = True.
Proof. exact (EQ_MP (@lem2442220) (@lem2442218)). Qed.
Lemma lem2442222 : term497 = True.
Proof. exact (TRANS (@lem2442217) (@lem2442221)). Qed.
Lemma lem2442223 : True = term497.
Proof. exact (SYM (@lem2442222)). Qed.
Lemma lem2442224 : term497.
Proof. exact (EQ_MP (@lem2442223) (@lem0)). Qed.
Lemma lem2442225 : term505.
Proof. exact (@lem2442214 (@lem2442224)). Qed.
Lemma lem2442227 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442228 : term497 = term503.
Proof. exact (@lem2442227 (NUMERAL 0) term81). Qed.
Lemma lem2442229 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442230 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442231 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442230 h1) (fun h1 : term503 = True => @lem2442229)). Qed.
Lemma lem2442232 : term503 = True.
Proof. exact (EQ_MP (@lem2442231) (@lem2442229)). Qed.
Lemma lem2442233 : term497 = True.
Proof. exact (TRANS (@lem2442228) (@lem2442232)). Qed.
Lemma lem2442234 : True = term497.
Proof. exact (SYM (@lem2442233)). Qed.
Lemma lem2442235 : term497.
Proof. exact (EQ_MP (@lem2442234) (@lem0)). Qed.
Lemma lem2442236 : term500 = term506.
Proof. exact (@lem2442225 (@lem2442235)). Qed.
Lemma lem2442238 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442239 : term145 = term146.
Proof. exact (@lem2442238 term81 term81). Qed.
Lemma lem2442240 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442241 : term148 = term81.
Proof. exact (EQ_MP (@lem2442240) (@lem940073)). Qed.
Lemma lem2442242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442243 : term146 = term80.
Proof. exact (MK_COMB (@lem2442242) (@lem2442241)). Qed.
Lemma lem2442244 : term145 = term80.
Proof. exact (TRANS (@lem2442239) (@lem2442243)). Qed.
Lemma lem2442246 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442247 : term508 = term95.
Proof. exact (@lem2442246 term81). Qed.
Lemma lem2442248 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2442249 : term509 = term498.
Proof. exact (MK_COMB (@lem2442248) (@lem2442247)). Qed.
Lemma lem2442250 : term506 = term497.
Proof. exact (MK_COMB (@lem2442249) (@lem2442244)). Qed.
Lemma lem2442252 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442253 : term497 = term503.
Proof. exact (@lem2442252 (NUMERAL 0) term81). Qed.
Lemma lem2442254 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442255 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442256 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442255 h1) (fun h1 : term503 = True => @lem2442254)). Qed.
Lemma lem2442257 : term503 = True.
Proof. exact (EQ_MP (@lem2442256) (@lem2442254)). Qed.
Lemma lem2442258 : term497 = True.
Proof. exact (TRANS (@lem2442253) (@lem2442257)). Qed.
Lemma lem2442259 : term506 = True.
Proof. exact (TRANS (@lem2442250) (@lem2442258)). Qed.
Lemma lem2442260 : term500 = True.
Proof. exact (TRANS (@lem2442236) (@lem2442259)). Qed.
Lemma lem2442261 : term497 = True.
Proof. exact (TRANS (@lem2442213) (@lem2442260)). Qed.
Lemma lem2442262 : term496 = True.
Proof. exact (TRANS (@lem2442204) (@lem2442261)). Qed.
Lemma lem2442263 : True = term496.
Proof. exact (SYM (@lem2442262)). Qed.
Lemma lem2442264 : term496.
Proof. exact (EQ_MP (@lem2442263) (@lem0)). Qed.
Lemma lem2442265 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term574 n x y.
Proof. exact (conj (@lem2442264) (@lem2442127 n x y h1)). Qed.
Lemma lem2442267 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2442268 (n : int) (x : int) (y : int) : term575 n x y.
Proof. exact (@lem2442267 term80 (term404 n x y)). Qed.
Lemma lem2442269 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term576 n x y.
Proof. exact (@lem2442268 n x y (@lem2442265 n x y h1)). Qed.
Lemma lem2442270 (n : int) (x : int) (y : int) : (term577 n x y) = (term404 n x y).
Proof. exact (@lem1982733 (term404 n x y)). Qed.
Lemma lem2442271 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2442272 (n : int) (x : int) (y : int) : (term578 n x y) = (term413 n x y).
Proof. exact (MK_COMB (@lem2442271) (@lem2442270 n x y)). Qed.
Lemma lem2442273 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2442274 (n : int) (x : int) (y : int) : (term576 n x y) = (term414 n x y).
Proof. exact (MK_COMB (@lem2442272 n x y) (@lem2442273)). Qed.
Lemma lem2442275 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term414 n x y.
Proof. exact (EQ_MP (@lem2442274 n x y) (@lem2442269 n x y h1)). Qed.
Lemma lem2442276 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term579 n x y.
Proof. exact (conj (@lem2442275 n x y h1) (@lem2442201 n x y h1)). Qed.
Lemma lem2442278 (x : real) (y : real) : term522 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2442279 (n : int) (x : int) (y : int) : term580 n x y.
Proof. exact (@lem2442278 (term404 n x y) (term260 n x y)). Qed.
Lemma lem2442280 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term581 n x y.
Proof. exact (@lem2442279 n x y (@lem2442276 n x y h1)). Qed.
Lemma lem2442281 (n : int) (x : int) (y : int) : (term582 n x y) = (term583 n x y).
Proof. exact (@lem1982753 (term201 n) (real_of_int n) (term278 x y) (term199 x y)). Qed.
Lemma lem2442282 (n : int) : (term527 n) = (term528 n).
Proof. exact (@lem1982713 term132 (real_of_int n)). Qed.
Lemma lem2442284 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442285 : term80 = term134.
Proof. exact (@lem2442284 term81). Qed.
Lemma lem2442287 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442288 : term132 = term137.
Proof. exact (@lem2442287 term81). Qed.
Lemma lem2442289 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442290 : term529 = term530.
Proof. exact (MK_COMB (@lem2442289) (@lem2442288)). Qed.
Lemma lem2442291 : term531 = term532.
Proof. exact (MK_COMB (@lem2442290) (@lem2442285)). Qed.
Lemma lem2442292 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2442294 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442295 : term497 = term503.
Proof. exact (@lem2442294 (NUMERAL 0) term81). Qed.
Lemma lem2442296 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442297 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442298 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442297 h1) (fun h1 : term503 = True => @lem2442296)). Qed.
Lemma lem2442299 : term503 = True.
Proof. exact (EQ_MP (@lem2442298) (@lem2442296)). Qed.
Lemma lem2442300 : term497 = True.
Proof. exact (TRANS (@lem2442295) (@lem2442299)). Qed.
Lemma lem2442301 : True = term497.
Proof. exact (SYM (@lem2442300)). Qed.
Lemma lem2442302 : term497.
Proof. exact (EQ_MP (@lem2442301) (@lem0)). Qed.
Lemma lem2442303 : term534.
Proof. exact (@lem2442292 (@lem2442302)). Qed.
Lemma lem2442305 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442306 : term497 = term503.
Proof. exact (@lem2442305 (NUMERAL 0) term81). Qed.
Lemma lem2442307 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442308 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442309 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442308 h1) (fun h1 : term503 = True => @lem2442307)). Qed.
Lemma lem2442310 : term503 = True.
Proof. exact (EQ_MP (@lem2442309) (@lem2442307)). Qed.
Lemma lem2442311 : term497 = True.
Proof. exact (TRANS (@lem2442306) (@lem2442310)). Qed.
Lemma lem2442312 : True = term497.
Proof. exact (SYM (@lem2442311)). Qed.
Lemma lem2442313 : term497.
Proof. exact (EQ_MP (@lem2442312) (@lem0)). Qed.
Lemma lem2442314 : term535.
Proof. exact (@lem2442303 (@lem2442313)). Qed.
Lemma lem2442316 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442317 : term497 = term503.
Proof. exact (@lem2442316 (NUMERAL 0) term81). Qed.
Lemma lem2442318 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442319 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442320 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442319 h1) (fun h1 : term503 = True => @lem2442318)). Qed.
Lemma lem2442321 : term503 = True.
Proof. exact (EQ_MP (@lem2442320) (@lem2442318)). Qed.
Lemma lem2442322 : term497 = True.
Proof. exact (TRANS (@lem2442317) (@lem2442321)). Qed.
Lemma lem2442323 : True = term497.
Proof. exact (SYM (@lem2442322)). Qed.
Lemma lem2442324 : term497.
Proof. exact (EQ_MP (@lem2442323) (@lem0)). Qed.
Lemma lem2442325 : term536.
Proof. exact (@lem2442314 (@lem2442324)). Qed.
Lemma lem2442327 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442328 : term145 = term146.
Proof. exact (@lem2442327 term81 term81). Qed.
Lemma lem2442329 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442330 : term148 = term81.
Proof. exact (EQ_MP (@lem2442329) (@lem940073)). Qed.
Lemma lem2442331 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442332 : term146 = term80.
Proof. exact (MK_COMB (@lem2442331) (@lem2442330)). Qed.
Lemma lem2442333 : term145 = term80.
Proof. exact (TRANS (@lem2442328) (@lem2442332)). Qed.
Lemma lem2442335 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2442336 : term140 = term151.
Proof. exact (@lem2442335 term81 term81). Qed.
Lemma lem2442337 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442338 : term148 = term81.
Proof. exact (EQ_MP (@lem2442337) (@lem940073)). Qed.
Lemma lem2442339 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442340 : term146 = term80.
Proof. exact (MK_COMB (@lem2442339) (@lem2442338)). Qed.
Lemma lem2442341 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2442342 : term151 = term132.
Proof. exact (MK_COMB (@lem2442341) (@lem2442340)). Qed.
Lemma lem2442343 : term140 = term132.
Proof. exact (TRANS (@lem2442336) (@lem2442342)). Qed.
Lemma lem2442344 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442345 : term537 = term529.
Proof. exact (MK_COMB (@lem2442344) (@lem2442343)). Qed.
Lemma lem2442346 : term538 = term531.
Proof. exact (MK_COMB (@lem2442345) (@lem2442333)). Qed.
Lemma lem2442348 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2442349 : term531 = term95.
Proof. exact (@lem2442348 term81). Qed.
Lemma lem2442350 : term538 = term95.
Proof. exact (TRANS (@lem2442346) (@lem2442349)). Qed.
Lemma lem2442351 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442352 : term540 = term541.
Proof. exact (MK_COMB (@lem2442351) (@lem2442350)). Qed.
Lemma lem2442353 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2442354 : term542 = term508.
Proof. exact (MK_COMB (@lem2442352) (@lem2442353)). Qed.
Lemma lem2442356 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442357 : term508 = term95.
Proof. exact (@lem2442356 term81). Qed.
Lemma lem2442358 : term542 = term95.
Proof. exact (TRANS (@lem2442354) (@lem2442357)). Qed.
Lemma lem2442360 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442361 : term145 = term146.
Proof. exact (@lem2442360 term81 term81). Qed.
Lemma lem2442362 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442363 : term148 = term81.
Proof. exact (EQ_MP (@lem2442362) (@lem940073)). Qed.
Lemma lem2442364 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442365 : term146 = term80.
Proof. exact (MK_COMB (@lem2442364) (@lem2442363)). Qed.
Lemma lem2442366 : term145 = term80.
Proof. exact (TRANS (@lem2442361) (@lem2442365)). Qed.
Lemma lem2442367 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2442368 : term543 = term508.
Proof. exact (MK_COMB (@lem2442367) (@lem2442366)). Qed.
Lemma lem2442370 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442371 : term508 = term95.
Proof. exact (@lem2442370 term81). Qed.
Lemma lem2442372 : term543 = term95.
Proof. exact (TRANS (@lem2442368) (@lem2442371)). Qed.
Lemma lem2442373 : term95 = term543.
Proof. exact (SYM (@lem2442372)). Qed.
Lemma lem2442374 : term542 = term543.
Proof. exact (TRANS (@lem2442358) (@lem2442373)). Qed.
Lemma lem2442375 : term532 = term179.
Proof. exact (@lem2442325 (@lem2442374)). Qed.
Lemma lem2442376 : term531 = term179.
Proof. exact (TRANS (@lem2442291) (@lem2442375)). Qed.
Lemma lem2442378 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2442379 : term179 = term95.
Proof. exact (@lem2442378 term95). Qed.
Lemma lem2442380 : term531 = term95.
Proof. exact (TRANS (@lem2442376) (@lem2442379)). Qed.
Lemma lem2442381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442382 : term544 = term541.
Proof. exact (MK_COMB (@lem2442381) (@lem2442380)). Qed.
Lemma lem2442383 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2442384 (n : int) : (term528 n) = (term545 n).
Proof. exact (MK_COMB (@lem2442382) (@lem2442383 n)). Qed.
Lemma lem2442385 (n : int) : (term527 n) = (term545 n).
Proof. exact (TRANS (@lem2442282 n) (@lem2442384 n)). Qed.
Lemma lem2442386 (n : int) : (term545 n) = term95.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2442387 (n : int) : (term527 n) = term95.
Proof. exact (TRANS (@lem2442385 n) (@lem2442386 n)). Qed.
Lemma lem2442388 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442389 (n : int) : (term546 n) = term392.
Proof. exact (MK_COMB (@lem2442388) (@lem2442387 n)). Qed.
Lemma lem2442390 (x : int) (y : int) : (term584 x y) = (term585 x y).
Proof. exact (@lem1982753 (term201 x) (real_of_int x) (real_of_int y) (term198 y)). Qed.
Lemma lem2442391 (x : int) : (term527 x) = (term528 x).
Proof. exact (@lem1982713 term132 (real_of_int x)). Qed.
Lemma lem2442393 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442394 : term80 = term134.
Proof. exact (@lem2442393 term81). Qed.
Lemma lem2442396 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442397 : term132 = term137.
Proof. exact (@lem2442396 term81). Qed.
Lemma lem2442398 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442399 : term529 = term530.
Proof. exact (MK_COMB (@lem2442398) (@lem2442397)). Qed.
Lemma lem2442400 : term531 = term532.
Proof. exact (MK_COMB (@lem2442399) (@lem2442394)). Qed.
Lemma lem2442401 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2442403 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442404 : term497 = term503.
Proof. exact (@lem2442403 (NUMERAL 0) term81). Qed.
Lemma lem2442405 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442406 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442407 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442406 h1) (fun h1 : term503 = True => @lem2442405)). Qed.
Lemma lem2442408 : term503 = True.
Proof. exact (EQ_MP (@lem2442407) (@lem2442405)). Qed.
Lemma lem2442409 : term497 = True.
Proof. exact (TRANS (@lem2442404) (@lem2442408)). Qed.
Lemma lem2442410 : True = term497.
Proof. exact (SYM (@lem2442409)). Qed.
Lemma lem2442411 : term497.
Proof. exact (EQ_MP (@lem2442410) (@lem0)). Qed.
Lemma lem2442412 : term534.
Proof. exact (@lem2442401 (@lem2442411)). Qed.
Lemma lem2442414 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442415 : term497 = term503.
Proof. exact (@lem2442414 (NUMERAL 0) term81). Qed.
Lemma lem2442416 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442417 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442418 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442417 h1) (fun h1 : term503 = True => @lem2442416)). Qed.
Lemma lem2442419 : term503 = True.
Proof. exact (EQ_MP (@lem2442418) (@lem2442416)). Qed.
Lemma lem2442420 : term497 = True.
Proof. exact (TRANS (@lem2442415) (@lem2442419)). Qed.
Lemma lem2442421 : True = term497.
Proof. exact (SYM (@lem2442420)). Qed.
Lemma lem2442422 : term497.
Proof. exact (EQ_MP (@lem2442421) (@lem0)). Qed.
Lemma lem2442423 : term535.
Proof. exact (@lem2442412 (@lem2442422)). Qed.
Lemma lem2442425 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442426 : term497 = term503.
Proof. exact (@lem2442425 (NUMERAL 0) term81). Qed.
Lemma lem2442427 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442428 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442429 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442428 h1) (fun h1 : term503 = True => @lem2442427)). Qed.
Lemma lem2442430 : term503 = True.
Proof. exact (EQ_MP (@lem2442429) (@lem2442427)). Qed.
Lemma lem2442431 : term497 = True.
Proof. exact (TRANS (@lem2442426) (@lem2442430)). Qed.
Lemma lem2442432 : True = term497.
Proof. exact (SYM (@lem2442431)). Qed.
Lemma lem2442433 : term497.
Proof. exact (EQ_MP (@lem2442432) (@lem0)). Qed.
Lemma lem2442434 : term536.
Proof. exact (@lem2442423 (@lem2442433)). Qed.
Lemma lem2442436 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442437 : term145 = term146.
Proof. exact (@lem2442436 term81 term81). Qed.
Lemma lem2442438 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442439 : term148 = term81.
Proof. exact (EQ_MP (@lem2442438) (@lem940073)). Qed.
Lemma lem2442440 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442441 : term146 = term80.
Proof. exact (MK_COMB (@lem2442440) (@lem2442439)). Qed.
Lemma lem2442442 : term145 = term80.
Proof. exact (TRANS (@lem2442437) (@lem2442441)). Qed.
Lemma lem2442444 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2442445 : term140 = term151.
Proof. exact (@lem2442444 term81 term81). Qed.
Lemma lem2442446 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442447 : term148 = term81.
Proof. exact (EQ_MP (@lem2442446) (@lem940073)). Qed.
Lemma lem2442448 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442449 : term146 = term80.
Proof. exact (MK_COMB (@lem2442448) (@lem2442447)). Qed.
Lemma lem2442450 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2442451 : term151 = term132.
Proof. exact (MK_COMB (@lem2442450) (@lem2442449)). Qed.
Lemma lem2442452 : term140 = term132.
Proof. exact (TRANS (@lem2442445) (@lem2442451)). Qed.
Lemma lem2442453 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442454 : term537 = term529.
Proof. exact (MK_COMB (@lem2442453) (@lem2442452)). Qed.
Lemma lem2442455 : term538 = term531.
Proof. exact (MK_COMB (@lem2442454) (@lem2442442)). Qed.
Lemma lem2442457 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2442458 : term531 = term95.
Proof. exact (@lem2442457 term81). Qed.
Lemma lem2442459 : term538 = term95.
Proof. exact (TRANS (@lem2442455) (@lem2442458)). Qed.
Lemma lem2442460 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442461 : term540 = term541.
Proof. exact (MK_COMB (@lem2442460) (@lem2442459)). Qed.
Lemma lem2442462 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2442463 : term542 = term508.
Proof. exact (MK_COMB (@lem2442461) (@lem2442462)). Qed.
Lemma lem2442465 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442466 : term508 = term95.
Proof. exact (@lem2442465 term81). Qed.
Lemma lem2442467 : term542 = term95.
Proof. exact (TRANS (@lem2442463) (@lem2442466)). Qed.
Lemma lem2442469 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442470 : term145 = term146.
Proof. exact (@lem2442469 term81 term81). Qed.
Lemma lem2442471 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442472 : term148 = term81.
Proof. exact (EQ_MP (@lem2442471) (@lem940073)). Qed.
Lemma lem2442473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442474 : term146 = term80.
Proof. exact (MK_COMB (@lem2442473) (@lem2442472)). Qed.
Lemma lem2442475 : term145 = term80.
Proof. exact (TRANS (@lem2442470) (@lem2442474)). Qed.
Lemma lem2442476 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2442477 : term543 = term508.
Proof. exact (MK_COMB (@lem2442476) (@lem2442475)). Qed.
Lemma lem2442479 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442480 : term508 = term95.
Proof. exact (@lem2442479 term81). Qed.
Lemma lem2442481 : term543 = term95.
Proof. exact (TRANS (@lem2442477) (@lem2442480)). Qed.
Lemma lem2442482 : term95 = term543.
Proof. exact (SYM (@lem2442481)). Qed.
Lemma lem2442483 : term542 = term543.
Proof. exact (TRANS (@lem2442467) (@lem2442482)). Qed.
Lemma lem2442484 : term532 = term179.
Proof. exact (@lem2442434 (@lem2442483)). Qed.
Lemma lem2442485 : term531 = term179.
Proof. exact (TRANS (@lem2442400) (@lem2442484)). Qed.
Lemma lem2442487 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2442488 : term179 = term95.
Proof. exact (@lem2442487 term95). Qed.
Lemma lem2442489 : term531 = term95.
Proof. exact (TRANS (@lem2442485) (@lem2442488)). Qed.
Lemma lem2442490 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442491 : term544 = term541.
Proof. exact (MK_COMB (@lem2442490) (@lem2442489)). Qed.
Lemma lem2442492 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2442493 (x : int) : (term528 x) = (term545 x).
Proof. exact (MK_COMB (@lem2442491) (@lem2442492 x)). Qed.
Lemma lem2442494 (x : int) : (term527 x) = (term545 x).
Proof. exact (TRANS (@lem2442391 x) (@lem2442493 x)). Qed.
Lemma lem2442495 (x : int) : (term545 x) = term95.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2442496 (x : int) : (term527 x) = term95.
Proof. exact (TRANS (@lem2442494 x) (@lem2442495 x)). Qed.
Lemma lem2442497 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442498 (x : int) : (term546 x) = term392.
Proof. exact (MK_COMB (@lem2442497) (@lem2442496 x)). Qed.
Lemma lem2442499 (y : int) : (term586 y) = (term587 y).
Proof. exact (@lem1982763 (real_of_int y) (term201 y) term132). Qed.
Lemma lem2442500 (y : int) : (term549 y) = (term528 y).
Proof. exact (@lem1982715 term132 (real_of_int y)). Qed.
Lemma lem2442502 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442503 : term80 = term134.
Proof. exact (@lem2442502 term81). Qed.
Lemma lem2442505 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442506 : term132 = term137.
Proof. exact (@lem2442505 term81). Qed.
Lemma lem2442507 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442508 : term529 = term530.
Proof. exact (MK_COMB (@lem2442507) (@lem2442506)). Qed.
Lemma lem2442509 : term531 = term532.
Proof. exact (MK_COMB (@lem2442508) (@lem2442503)). Qed.
Lemma lem2442510 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2442512 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442513 : term497 = term503.
Proof. exact (@lem2442512 (NUMERAL 0) term81). Qed.
Lemma lem2442514 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442515 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442516 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442515 h1) (fun h1 : term503 = True => @lem2442514)). Qed.
Lemma lem2442517 : term503 = True.
Proof. exact (EQ_MP (@lem2442516) (@lem2442514)). Qed.
Lemma lem2442518 : term497 = True.
Proof. exact (TRANS (@lem2442513) (@lem2442517)). Qed.
Lemma lem2442519 : True = term497.
Proof. exact (SYM (@lem2442518)). Qed.
Lemma lem2442520 : term497.
Proof. exact (EQ_MP (@lem2442519) (@lem0)). Qed.
Lemma lem2442521 : term534.
Proof. exact (@lem2442510 (@lem2442520)). Qed.
Lemma lem2442523 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442524 : term497 = term503.
Proof. exact (@lem2442523 (NUMERAL 0) term81). Qed.
Lemma lem2442525 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442526 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442527 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442526 h1) (fun h1 : term503 = True => @lem2442525)). Qed.
Lemma lem2442528 : term503 = True.
Proof. exact (EQ_MP (@lem2442527) (@lem2442525)). Qed.
Lemma lem2442529 : term497 = True.
Proof. exact (TRANS (@lem2442524) (@lem2442528)). Qed.
Lemma lem2442530 : True = term497.
Proof. exact (SYM (@lem2442529)). Qed.
Lemma lem2442531 : term497.
Proof. exact (EQ_MP (@lem2442530) (@lem0)). Qed.
Lemma lem2442532 : term535.
Proof. exact (@lem2442521 (@lem2442531)). Qed.
Lemma lem2442534 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442535 : term497 = term503.
Proof. exact (@lem2442534 (NUMERAL 0) term81). Qed.
Lemma lem2442536 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442537 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442538 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442537 h1) (fun h1 : term503 = True => @lem2442536)). Qed.
Lemma lem2442539 : term503 = True.
Proof. exact (EQ_MP (@lem2442538) (@lem2442536)). Qed.
Lemma lem2442540 : term497 = True.
Proof. exact (TRANS (@lem2442535) (@lem2442539)). Qed.
Lemma lem2442541 : True = term497.
Proof. exact (SYM (@lem2442540)). Qed.
Lemma lem2442542 : term497.
Proof. exact (EQ_MP (@lem2442541) (@lem0)). Qed.
Lemma lem2442543 : term536.
Proof. exact (@lem2442532 (@lem2442542)). Qed.
Lemma lem2442545 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442546 : term145 = term146.
Proof. exact (@lem2442545 term81 term81). Qed.
Lemma lem2442547 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442548 : term148 = term81.
Proof. exact (EQ_MP (@lem2442547) (@lem940073)). Qed.
Lemma lem2442549 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442550 : term146 = term80.
Proof. exact (MK_COMB (@lem2442549) (@lem2442548)). Qed.
Lemma lem2442551 : term145 = term80.
Proof. exact (TRANS (@lem2442546) (@lem2442550)). Qed.
Lemma lem2442553 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2442554 : term140 = term151.
Proof. exact (@lem2442553 term81 term81). Qed.
Lemma lem2442555 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442556 : term148 = term81.
Proof. exact (EQ_MP (@lem2442555) (@lem940073)). Qed.
Lemma lem2442557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442558 : term146 = term80.
Proof. exact (MK_COMB (@lem2442557) (@lem2442556)). Qed.
Lemma lem2442559 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2442560 : term151 = term132.
Proof. exact (MK_COMB (@lem2442559) (@lem2442558)). Qed.
Lemma lem2442561 : term140 = term132.
Proof. exact (TRANS (@lem2442554) (@lem2442560)). Qed.
Lemma lem2442562 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442563 : term537 = term529.
Proof. exact (MK_COMB (@lem2442562) (@lem2442561)). Qed.
Lemma lem2442564 : term538 = term531.
Proof. exact (MK_COMB (@lem2442563) (@lem2442551)). Qed.
Lemma lem2442566 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2442567 : term531 = term95.
Proof. exact (@lem2442566 term81). Qed.
Lemma lem2442568 : term538 = term95.
Proof. exact (TRANS (@lem2442564) (@lem2442567)). Qed.
Lemma lem2442569 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442570 : term540 = term541.
Proof. exact (MK_COMB (@lem2442569) (@lem2442568)). Qed.
Lemma lem2442571 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2442572 : term542 = term508.
Proof. exact (MK_COMB (@lem2442570) (@lem2442571)). Qed.
Lemma lem2442574 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442575 : term508 = term95.
Proof. exact (@lem2442574 term81). Qed.
Lemma lem2442576 : term542 = term95.
Proof. exact (TRANS (@lem2442572) (@lem2442575)). Qed.
Lemma lem2442578 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442579 : term145 = term146.
Proof. exact (@lem2442578 term81 term81). Qed.
Lemma lem2442580 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442581 : term148 = term81.
Proof. exact (EQ_MP (@lem2442580) (@lem940073)). Qed.
Lemma lem2442582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442583 : term146 = term80.
Proof. exact (MK_COMB (@lem2442582) (@lem2442581)). Qed.
Lemma lem2442584 : term145 = term80.
Proof. exact (TRANS (@lem2442579) (@lem2442583)). Qed.
Lemma lem2442585 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2442586 : term543 = term508.
Proof. exact (MK_COMB (@lem2442585) (@lem2442584)). Qed.
Lemma lem2442588 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442589 : term508 = term95.
Proof. exact (@lem2442588 term81). Qed.
Lemma lem2442590 : term543 = term95.
Proof. exact (TRANS (@lem2442586) (@lem2442589)). Qed.
Lemma lem2442591 : term95 = term543.
Proof. exact (SYM (@lem2442590)). Qed.
Lemma lem2442592 : term542 = term543.
Proof. exact (TRANS (@lem2442576) (@lem2442591)). Qed.
Lemma lem2442593 : term532 = term179.
Proof. exact (@lem2442543 (@lem2442592)). Qed.
Lemma lem2442594 : term531 = term179.
Proof. exact (TRANS (@lem2442509) (@lem2442593)). Qed.
Lemma lem2442596 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2442597 : term179 = term95.
Proof. exact (@lem2442596 term95). Qed.
Lemma lem2442598 : term531 = term95.
Proof. exact (TRANS (@lem2442594) (@lem2442597)). Qed.
Lemma lem2442599 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442600 : term544 = term541.
Proof. exact (MK_COMB (@lem2442599) (@lem2442598)). Qed.
Lemma lem2442601 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2442602 (y : int) : (term528 y) = (term545 y).
Proof. exact (MK_COMB (@lem2442600) (@lem2442601 y)). Qed.
Lemma lem2442603 (y : int) : (term549 y) = (term545 y).
Proof. exact (TRANS (@lem2442500 y) (@lem2442602 y)). Qed.
Lemma lem2442604 (y : int) : (term545 y) = term95.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2442605 (y : int) : (term549 y) = term95.
Proof. exact (TRANS (@lem2442603 y) (@lem2442604 y)). Qed.
Lemma lem2442606 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442607 (y : int) : (term550 y) = term392.
Proof. exact (MK_COMB (@lem2442606) (@lem2442605 y)). Qed.
Lemma lem2442608 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem2442609 (y : int) : (term587 y) = term553.
Proof. exact (MK_COMB (@lem2442607 y) (@lem2442608)). Qed.
Lemma lem2442610 (y : int) : (term586 y) = term553.
Proof. exact (TRANS (@lem2442499 y) (@lem2442609 y)). Qed.
Lemma lem2442611 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2442612 (y : int) : (term586 y) = term132.
Proof. exact (TRANS (@lem2442610 y) (@lem2442611)). Qed.
Lemma lem2442613 (x : int) (y : int) : (term585 x y) = term553.
Proof. exact (MK_COMB (@lem2442498 x) (@lem2442612 y)). Qed.
Lemma lem2442614 (x : int) (y : int) : (term584 x y) = term553.
Proof. exact (TRANS (@lem2442390 x y) (@lem2442613 x y)). Qed.
Lemma lem2442615 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2442616 (x : int) (y : int) : (term584 x y) = term132.
Proof. exact (TRANS (@lem2442614 x y) (@lem2442615)). Qed.
Lemma lem2442617 (n : int) (x : int) (y : int) : (term583 n x y) = term553.
Proof. exact (MK_COMB (@lem2442389 n) (@lem2442616 x y)). Qed.
Lemma lem2442618 (n : int) (x : int) (y : int) : (term582 n x y) = term553.
Proof. exact (TRANS (@lem2442281 n x y) (@lem2442617 n x y)). Qed.
Lemma lem2442619 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2442620 (n : int) (x : int) (y : int) : (term582 n x y) = term132.
Proof. exact (TRANS (@lem2442618 n x y) (@lem2442619)). Qed.
Lemma lem2442621 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2442622 (n : int) (x : int) (y : int) : (term588 n x y) = term555.
Proof. exact (MK_COMB (@lem2442621) (@lem2442620 n x y)). Qed.
Lemma lem2442623 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2442624 (n : int) (x : int) (y : int) : (term581 n x y) = term556.
Proof. exact (MK_COMB (@lem2442622 n x y) (@lem2442623)). Qed.
Lemma lem2442625 (n : int) (x : int) (y : int) (h1 : term486 n x y) : term556.
Proof. exact (EQ_MP (@lem2442624 n x y) (@lem2442280 n x y h1)). Qed.
Lemma lem2442627 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2442628 : term556 = term557.
Proof. exact (@lem2442627 term95 term132). Qed.
Lemma lem2442630 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442631 : term132 = term137.
Proof. exact (@lem2442630 term81). Qed.
Lemma lem2442633 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442634 : term95 = term179.
Proof. exact (@lem2442633 (NUMERAL 0)). Qed.
Lemma lem2442635 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2442636 : term558 = term559.
Proof. exact (MK_COMB (@lem2442635) (@lem2442634)). Qed.
Lemma lem2442637 : term557 = term560.
Proof. exact (MK_COMB (@lem2442636) (@lem2442631)). Qed.
Lemma lem2442638 : term561.
Proof. exact (@lem1980026 term95 term80 term132 term80). Qed.
Lemma lem2442640 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442641 : term497 = term503.
Proof. exact (@lem2442640 (NUMERAL 0) term81). Qed.
Lemma lem2442642 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442643 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442644 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442643 h1) (fun h1 : term503 = True => @lem2442642)). Qed.
Lemma lem2442645 : term503 = True.
Proof. exact (EQ_MP (@lem2442644) (@lem2442642)). Qed.
Lemma lem2442646 : term497 = True.
Proof. exact (TRANS (@lem2442641) (@lem2442645)). Qed.
Lemma lem2442647 : True = term497.
Proof. exact (SYM (@lem2442646)). Qed.
Lemma lem2442648 : term497.
Proof. exact (EQ_MP (@lem2442647) (@lem0)). Qed.
Lemma lem2442649 : term562.
Proof. exact (@lem2442638 (@lem2442648)). Qed.
Lemma lem2442651 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442652 : term497 = term503.
Proof. exact (@lem2442651 (NUMERAL 0) term81). Qed.
Lemma lem2442653 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442654 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442655 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442654 h1) (fun h1 : term503 = True => @lem2442653)). Qed.
Lemma lem2442656 : term503 = True.
Proof. exact (EQ_MP (@lem2442655) (@lem2442653)). Qed.
Lemma lem2442657 : term497 = True.
Proof. exact (TRANS (@lem2442652) (@lem2442656)). Qed.
Lemma lem2442658 : True = term497.
Proof. exact (SYM (@lem2442657)). Qed.
Lemma lem2442659 : term497.
Proof. exact (EQ_MP (@lem2442658) (@lem0)). Qed.
Lemma lem2442660 : term560 = term563.
Proof. exact (@lem2442649 (@lem2442659)). Qed.
Lemma lem2442662 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2442663 : term140 = term151.
Proof. exact (@lem2442662 term81 term81). Qed.
Lemma lem2442664 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442665 : term148 = term81.
Proof. exact (EQ_MP (@lem2442664) (@lem940073)). Qed.
Lemma lem2442666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442667 : term146 = term80.
Proof. exact (MK_COMB (@lem2442666) (@lem2442665)). Qed.
Lemma lem2442668 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2442669 : term151 = term132.
Proof. exact (MK_COMB (@lem2442668) (@lem2442667)). Qed.
Lemma lem2442670 : term140 = term132.
Proof. exact (TRANS (@lem2442663) (@lem2442669)). Qed.
Lemma lem2442672 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442673 : term508 = term95.
Proof. exact (@lem2442672 term81). Qed.
Lemma lem2442674 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2442675 : term564 = term558.
Proof. exact (MK_COMB (@lem2442674) (@lem2442673)). Qed.
Lemma lem2442676 : term563 = term557.
Proof. exact (MK_COMB (@lem2442675) (@lem2442670)). Qed.
Lemma lem2442678 (m : nat) (n : nat) : (term565 m n) = (term566 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2442679 : term557 = term567.
Proof. exact (@lem2442678 (NUMERAL 0) term81). Qed.
Lemma lem2442680 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442681 (h1 : term504 = (BIT1 0)) : (term81 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2442682 : (term504 = (BIT1 0)) = ((term81 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442681 h1) (fun h1 : (term81 = (NUMERAL 0)) = False => @lem2442680)). Qed.
Lemma lem2442683 : (term81 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2442682) (@lem2442680)). Qed.
Lemma lem2442684 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2442685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2442686 : term568 = (and True).
Proof. exact (MK_COMB (@lem2442685) (@lem2442684)). Qed.
Lemma lem2442687 : term567 = (True /\ False).
Proof. exact (MK_COMB (@lem2442686) (@lem2442683)). Qed.
Lemma lem2442689 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2442690 : term567 = False.
Proof. exact (TRANS (@lem2442687) (@lem2442689)). Qed.
Lemma lem2442691 : term557 = False.
Proof. exact (TRANS (@lem2442679) (@lem2442690)). Qed.
Lemma lem2442692 : term563 = False.
Proof. exact (TRANS (@lem2442676) (@lem2442691)). Qed.
Lemma lem2442693 : term560 = False.
Proof. exact (TRANS (@lem2442660) (@lem2442692)). Qed.
Lemma lem2442694 : term557 = False.
Proof. exact (TRANS (@lem2442637) (@lem2442693)). Qed.
Lemma lem2442695 : term556 = False.
Proof. exact (TRANS (@lem2442628) (@lem2442694)). Qed.
Lemma lem2442696 (n : int) (x : int) (y : int) (h1 : term486 n x y) : False.
Proof. exact (EQ_MP (@lem2442695) (@lem2442625 n x y h1)). Qed.
Lemma lem2442697 (n : int) (x : int) (y : int) (h1 : term488 n x y) : False.
Proof. exact (or_elim (@lem2441532 n x y h1) (fun h0 : term480 n x y => @lem2442114 n x y h0) (fun h0 : term486 n x y => @lem2442696 n x y h0)). Qed.
Lemma lem2442698 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term490 n x y.
Proof. exact (h1). Qed.
Lemma lem2442699 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term240 n x y.
Proof. exact (proj2 (@lem2442698 n x y h1)). Qed.
Lemma lem2442703 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term227 x y.
Proof. exact (proj2 (@lem2442699 n x y h1)). Qed.
Lemma lem2442705 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term206 x y.
Proof. exact (proj2 (@lem2442703 n x y h1)). Qed.
Lemma lem2442706 (n : int) (x : int) (y : int) (h1 : term490 n x y) : (term122 x y) = term95.
Proof. exact (proj1 (@lem2442703 n x y h1)). Qed.
Lemma lem2442708 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2442709 : term496 = term497.
Proof. exact (@lem2442708 term95 term80). Qed.
Lemma lem2442711 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442712 : term80 = term134.
Proof. exact (@lem2442711 term81). Qed.
Lemma lem2442714 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442715 : term95 = term179.
Proof. exact (@lem2442714 (NUMERAL 0)). Qed.
Lemma lem2442716 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2442717 : term498 = term499.
Proof. exact (MK_COMB (@lem2442716) (@lem2442715)). Qed.
Lemma lem2442718 : term497 = term500.
Proof. exact (MK_COMB (@lem2442717) (@lem2442712)). Qed.
Lemma lem2442719 : term501.
Proof. exact (@lem1980255 term95 term80 term80 term80). Qed.
Lemma lem2442721 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442722 : term497 = term503.
Proof. exact (@lem2442721 (NUMERAL 0) term81). Qed.
Lemma lem2442723 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442724 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442725 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442724 h1) (fun h1 : term503 = True => @lem2442723)). Qed.
Lemma lem2442726 : term503 = True.
Proof. exact (EQ_MP (@lem2442725) (@lem2442723)). Qed.
Lemma lem2442727 : term497 = True.
Proof. exact (TRANS (@lem2442722) (@lem2442726)). Qed.
Lemma lem2442728 : True = term497.
Proof. exact (SYM (@lem2442727)). Qed.
Lemma lem2442729 : term497.
Proof. exact (EQ_MP (@lem2442728) (@lem0)). Qed.
Lemma lem2442730 : term505.
Proof. exact (@lem2442719 (@lem2442729)). Qed.
Lemma lem2442732 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442733 : term497 = term503.
Proof. exact (@lem2442732 (NUMERAL 0) term81). Qed.
Lemma lem2442734 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442735 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442736 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442735 h1) (fun h1 : term503 = True => @lem2442734)). Qed.
Lemma lem2442737 : term503 = True.
Proof. exact (EQ_MP (@lem2442736) (@lem2442734)). Qed.
Lemma lem2442738 : term497 = True.
Proof. exact (TRANS (@lem2442733) (@lem2442737)). Qed.
Lemma lem2442739 : True = term497.
Proof. exact (SYM (@lem2442738)). Qed.
Lemma lem2442740 : term497.
Proof. exact (EQ_MP (@lem2442739) (@lem0)). Qed.
Lemma lem2442741 : term500 = term506.
Proof. exact (@lem2442730 (@lem2442740)). Qed.
Lemma lem2442743 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442744 : term145 = term146.
Proof. exact (@lem2442743 term81 term81). Qed.
Lemma lem2442745 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442746 : term148 = term81.
Proof. exact (EQ_MP (@lem2442745) (@lem940073)). Qed.
Lemma lem2442747 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442748 : term146 = term80.
Proof. exact (MK_COMB (@lem2442747) (@lem2442746)). Qed.
Lemma lem2442749 : term145 = term80.
Proof. exact (TRANS (@lem2442744) (@lem2442748)). Qed.
Lemma lem2442751 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442752 : term508 = term95.
Proof. exact (@lem2442751 term81). Qed.
Lemma lem2442753 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2442754 : term509 = term498.
Proof. exact (MK_COMB (@lem2442753) (@lem2442752)). Qed.
Lemma lem2442755 : term506 = term497.
Proof. exact (MK_COMB (@lem2442754) (@lem2442749)). Qed.
Lemma lem2442757 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442758 : term497 = term503.
Proof. exact (@lem2442757 (NUMERAL 0) term81). Qed.
Lemma lem2442759 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442760 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442761 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442760 h1) (fun h1 : term503 = True => @lem2442759)). Qed.
Lemma lem2442762 : term503 = True.
Proof. exact (EQ_MP (@lem2442761) (@lem2442759)). Qed.
Lemma lem2442763 : term497 = True.
Proof. exact (TRANS (@lem2442758) (@lem2442762)). Qed.
Lemma lem2442764 : term506 = True.
Proof. exact (TRANS (@lem2442755) (@lem2442763)). Qed.
Lemma lem2442765 : term500 = True.
Proof. exact (TRANS (@lem2442741) (@lem2442764)). Qed.
Lemma lem2442766 : term497 = True.
Proof. exact (TRANS (@lem2442718) (@lem2442765)). Qed.
Lemma lem2442767 : term496 = True.
Proof. exact (TRANS (@lem2442709) (@lem2442766)). Qed.
Lemma lem2442768 : True = term496.
Proof. exact (SYM (@lem2442767)). Qed.
Lemma lem2442769 : term496.
Proof. exact (EQ_MP (@lem2442768) (@lem0)). Qed.
Lemma lem2442770 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term603 x y.
Proof. exact (conj (@lem2442769) (@lem2442705 n x y h1)). Qed.
Lemma lem2442772 (x : real) (y : real) : term511 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2442773 (x : int) (y : int) : term604 x y.
Proof. exact (@lem2442772 term80 (term199 x y)). Qed.
Lemma lem2442774 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term605 x y.
Proof. exact (@lem2442773 x y (@lem2442770 n x y h1)). Qed.
Lemma lem2442775 (x : int) (y : int) : (term606 x y) = (term199 x y).
Proof. exact (@lem1982733 (term199 x y)). Qed.
Lemma lem2442776 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2442777 (x : int) (y : int) : (term607 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem2442776) (@lem2442775 x y)). Qed.
Lemma lem2442778 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2442779 (x : int) (y : int) : (term605 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem2442777 x y) (@lem2442778)). Qed.
Lemma lem2442780 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term206 x y.
Proof. exact (EQ_MP (@lem2442779 x y) (@lem2442774 n x y h1)). Qed.
Lemma lem2442782 (y : real) : term594 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2442783 (x : int) (y : int) : term595 x y.
Proof. exact (@lem2442782 (term122 x y)). Qed.
Lemma lem2442784 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term596 x y.
Proof. exact (@lem2442783 x y (@lem2442706 n x y h1)). Qed.
Lemma lem2442785 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term608 x y.
Proof. exact (@lem2442784 n x y h1 term132). Qed.
Lemma lem2442786 (x : int) (y : int) : (term608 x y) = ((term265 x y) = term95).
Proof. exact (eq_refl (term608 x y)). Qed.
Lemma lem2442787 (n : int) (x : int) (y : int) (h1 : term490 n x y) : (term265 x y) = term95.
Proof. exact (EQ_MP (@lem2442786 x y) (@lem2442785 n x y h1)). Qed.
Lemma lem2442788 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term201 y)). Qed.
Lemma lem2442789 (y : int) : (term267 y) = (term268 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2442791 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442792 : term132 = term137.
Proof. exact (@lem2442791 term81). Qed.
Lemma lem2442794 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442795 : term132 = term137.
Proof. exact (@lem2442794 term81). Qed.
Lemma lem2442796 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442797 : term138 = term139.
Proof. exact (MK_COMB (@lem2442796) (@lem2442795)). Qed.
Lemma lem2442798 : term269 = term270.
Proof. exact (MK_COMB (@lem2442797) (@lem2442792)). Qed.
Lemma lem2442799 : term270 = term271.
Proof. exact (@lem1981613 term132 term132 term80 term80). Qed.
Lemma lem2442801 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442802 : term145 = term146.
Proof. exact (@lem2442801 term81 term81). Qed.
Lemma lem2442803 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442804 : term148 = term81.
Proof. exact (EQ_MP (@lem2442803) (@lem940073)). Qed.
Lemma lem2442805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442806 : term146 = term80.
Proof. exact (MK_COMB (@lem2442805) (@lem2442804)). Qed.
Lemma lem2442807 : term145 = term80.
Proof. exact (TRANS (@lem2442802) (@lem2442806)). Qed.
Lemma lem2442809 (m : nat) (n : nat) : (term272 m n) = (term144 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2442810 : term269 = term146.
Proof. exact (@lem2442809 term81 term81). Qed.
Lemma lem2442811 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442812 : term148 = term81.
Proof. exact (EQ_MP (@lem2442811) (@lem940073)). Qed.
Lemma lem2442813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442814 : term146 = term80.
Proof. exact (MK_COMB (@lem2442813) (@lem2442812)). Qed.
Lemma lem2442815 : term269 = term80.
Proof. exact (TRANS (@lem2442810) (@lem2442814)). Qed.
Lemma lem2442816 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2442817 : term273 = term274.
Proof. exact (MK_COMB (@lem2442816) (@lem2442815)). Qed.
Lemma lem2442818 : term271 = term134.
Proof. exact (MK_COMB (@lem2442817) (@lem2442807)). Qed.
Lemma lem2442819 : term270 = term134.
Proof. exact (TRANS (@lem2442799) (@lem2442818)). Qed.
Lemma lem2442820 : term269 = term134.
Proof. exact (TRANS (@lem2442798) (@lem2442819)). Qed.
Lemma lem2442822 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2442823 : term134 = term80.
Proof. exact (@lem2442822 term80). Qed.
Lemma lem2442824 : term269 = term80.
Proof. exact (TRANS (@lem2442820) (@lem2442823)). Qed.
Lemma lem2442825 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442826 : term275 = term276.
Proof. exact (MK_COMB (@lem2442825) (@lem2442824)). Qed.
Lemma lem2442827 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2442828 (y : int) : (term268 y) = (term277 y).
Proof. exact (MK_COMB (@lem2442826) (@lem2442827 y)). Qed.
Lemma lem2442829 (y : int) : (term267 y) = (term277 y).
Proof. exact (TRANS (@lem2442789 y) (@lem2442828 y)). Qed.
Lemma lem2442830 (y : int) : (term277 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2442831 (y : int) : (term267 y) = (real_of_int y).
Proof. exact (TRANS (@lem2442829 y) (@lem2442830 y)). Qed.
Lemma lem2442834 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2442835 (x : int) (y : int) : (term266 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem2442834 x) (@lem2442831 y)). Qed.
Lemma lem2442836 (x : int) (y : int) : (term265 x y) = (term278 x y).
Proof. exact (TRANS (@lem2442788 x y) (@lem2442835 x y)). Qed.
Lemma lem2442837 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2442838 (x : int) (y : int) : (term609 x y) = (term610 x y).
Proof. exact (MK_COMB (@lem2442837) (@lem2442836 x y)). Qed.
Lemma lem2442839 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2442840 (x : int) (y : int) : ((term265 x y) = term95) = ((term278 x y) = term95).
Proof. exact (MK_COMB (@lem2442838 x y) (@lem2442839)). Qed.
Lemma lem2442841 (n : int) (x : int) (y : int) (h1 : term490 n x y) : (term278 x y) = term95.
Proof. exact (EQ_MP (@lem2442840 x y) (@lem2442787 n x y h1)). Qed.
Lemma lem2442842 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term611 x y.
Proof. exact (conj (@lem2442841 n x y h1) (@lem2442780 n x y h1)). Qed.
Lemma lem2442844 (x : real) (y : real) : term599 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2442845 (x : int) (y : int) : term612 x y.
Proof. exact (@lem2442844 (term278 x y) (term199 x y)). Qed.
Lemma lem2442846 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term613 x y.
Proof. exact (@lem2442845 x y (@lem2442842 n x y h1)). Qed.
Lemma lem2442847 (x : int) (y : int) : (term584 x y) = (term585 x y).
Proof. exact (@lem1982753 (term201 x) (real_of_int x) (real_of_int y) (term198 y)). Qed.
Lemma lem2442848 (x : int) : (term527 x) = (term528 x).
Proof. exact (@lem1982713 term132 (real_of_int x)). Qed.
Lemma lem2442850 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442851 : term80 = term134.
Proof. exact (@lem2442850 term81). Qed.
Lemma lem2442853 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442854 : term132 = term137.
Proof. exact (@lem2442853 term81). Qed.
Lemma lem2442855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442856 : term529 = term530.
Proof. exact (MK_COMB (@lem2442855) (@lem2442854)). Qed.
Lemma lem2442857 : term531 = term532.
Proof. exact (MK_COMB (@lem2442856) (@lem2442851)). Qed.
Lemma lem2442858 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2442860 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442861 : term497 = term503.
Proof. exact (@lem2442860 (NUMERAL 0) term81). Qed.
Lemma lem2442862 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442863 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442864 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442863 h1) (fun h1 : term503 = True => @lem2442862)). Qed.
Lemma lem2442865 : term503 = True.
Proof. exact (EQ_MP (@lem2442864) (@lem2442862)). Qed.
Lemma lem2442866 : term497 = True.
Proof. exact (TRANS (@lem2442861) (@lem2442865)). Qed.
Lemma lem2442867 : True = term497.
Proof. exact (SYM (@lem2442866)). Qed.
Lemma lem2442868 : term497.
Proof. exact (EQ_MP (@lem2442867) (@lem0)). Qed.
Lemma lem2442869 : term534.
Proof. exact (@lem2442858 (@lem2442868)). Qed.
Lemma lem2442871 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442872 : term497 = term503.
Proof. exact (@lem2442871 (NUMERAL 0) term81). Qed.
Lemma lem2442873 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442874 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442875 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442874 h1) (fun h1 : term503 = True => @lem2442873)). Qed.
Lemma lem2442876 : term503 = True.
Proof. exact (EQ_MP (@lem2442875) (@lem2442873)). Qed.
Lemma lem2442877 : term497 = True.
Proof. exact (TRANS (@lem2442872) (@lem2442876)). Qed.
Lemma lem2442878 : True = term497.
Proof. exact (SYM (@lem2442877)). Qed.
Lemma lem2442879 : term497.
Proof. exact (EQ_MP (@lem2442878) (@lem0)). Qed.
Lemma lem2442880 : term535.
Proof. exact (@lem2442869 (@lem2442879)). Qed.
Lemma lem2442882 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442883 : term497 = term503.
Proof. exact (@lem2442882 (NUMERAL 0) term81). Qed.
Lemma lem2442884 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442885 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442886 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442885 h1) (fun h1 : term503 = True => @lem2442884)). Qed.
Lemma lem2442887 : term503 = True.
Proof. exact (EQ_MP (@lem2442886) (@lem2442884)). Qed.
Lemma lem2442888 : term497 = True.
Proof. exact (TRANS (@lem2442883) (@lem2442887)). Qed.
Lemma lem2442889 : True = term497.
Proof. exact (SYM (@lem2442888)). Qed.
Lemma lem2442890 : term497.
Proof. exact (EQ_MP (@lem2442889) (@lem0)). Qed.
Lemma lem2442891 : term536.
Proof. exact (@lem2442880 (@lem2442890)). Qed.
Lemma lem2442893 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442894 : term145 = term146.
Proof. exact (@lem2442893 term81 term81). Qed.
Lemma lem2442895 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442896 : term148 = term81.
Proof. exact (EQ_MP (@lem2442895) (@lem940073)). Qed.
Lemma lem2442897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442898 : term146 = term80.
Proof. exact (MK_COMB (@lem2442897) (@lem2442896)). Qed.
Lemma lem2442899 : term145 = term80.
Proof. exact (TRANS (@lem2442894) (@lem2442898)). Qed.
Lemma lem2442901 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2442902 : term140 = term151.
Proof. exact (@lem2442901 term81 term81). Qed.
Lemma lem2442903 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442904 : term148 = term81.
Proof. exact (EQ_MP (@lem2442903) (@lem940073)). Qed.
Lemma lem2442905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442906 : term146 = term80.
Proof. exact (MK_COMB (@lem2442905) (@lem2442904)). Qed.
Lemma lem2442907 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2442908 : term151 = term132.
Proof. exact (MK_COMB (@lem2442907) (@lem2442906)). Qed.
Lemma lem2442909 : term140 = term132.
Proof. exact (TRANS (@lem2442902) (@lem2442908)). Qed.
Lemma lem2442910 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442911 : term537 = term529.
Proof. exact (MK_COMB (@lem2442910) (@lem2442909)). Qed.
Lemma lem2442912 : term538 = term531.
Proof. exact (MK_COMB (@lem2442911) (@lem2442899)). Qed.
Lemma lem2442914 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2442915 : term531 = term95.
Proof. exact (@lem2442914 term81). Qed.
Lemma lem2442916 : term538 = term95.
Proof. exact (TRANS (@lem2442912) (@lem2442915)). Qed.
Lemma lem2442917 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442918 : term540 = term541.
Proof. exact (MK_COMB (@lem2442917) (@lem2442916)). Qed.
Lemma lem2442919 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2442920 : term542 = term508.
Proof. exact (MK_COMB (@lem2442918) (@lem2442919)). Qed.
Lemma lem2442922 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442923 : term508 = term95.
Proof. exact (@lem2442922 term81). Qed.
Lemma lem2442924 : term542 = term95.
Proof. exact (TRANS (@lem2442920) (@lem2442923)). Qed.
Lemma lem2442926 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2442927 : term145 = term146.
Proof. exact (@lem2442926 term81 term81). Qed.
Lemma lem2442928 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2442929 : term148 = term81.
Proof. exact (EQ_MP (@lem2442928) (@lem940073)). Qed.
Lemma lem2442930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2442931 : term146 = term80.
Proof. exact (MK_COMB (@lem2442930) (@lem2442929)). Qed.
Lemma lem2442932 : term145 = term80.
Proof. exact (TRANS (@lem2442927) (@lem2442931)). Qed.
Lemma lem2442933 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2442934 : term543 = term508.
Proof. exact (MK_COMB (@lem2442933) (@lem2442932)). Qed.
Lemma lem2442936 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2442937 : term508 = term95.
Proof. exact (@lem2442936 term81). Qed.
Lemma lem2442938 : term543 = term95.
Proof. exact (TRANS (@lem2442934) (@lem2442937)). Qed.
Lemma lem2442939 : term95 = term543.
Proof. exact (SYM (@lem2442938)). Qed.
Lemma lem2442940 : term542 = term543.
Proof. exact (TRANS (@lem2442924) (@lem2442939)). Qed.
Lemma lem2442941 : term532 = term179.
Proof. exact (@lem2442891 (@lem2442940)). Qed.
Lemma lem2442942 : term531 = term179.
Proof. exact (TRANS (@lem2442857) (@lem2442941)). Qed.
Lemma lem2442944 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2442945 : term179 = term95.
Proof. exact (@lem2442944 term95). Qed.
Lemma lem2442946 : term531 = term95.
Proof. exact (TRANS (@lem2442942) (@lem2442945)). Qed.
Lemma lem2442947 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2442948 : term544 = term541.
Proof. exact (MK_COMB (@lem2442947) (@lem2442946)). Qed.
Lemma lem2442949 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2442950 (x : int) : (term528 x) = (term545 x).
Proof. exact (MK_COMB (@lem2442948) (@lem2442949 x)). Qed.
Lemma lem2442951 (x : int) : (term527 x) = (term545 x).
Proof. exact (TRANS (@lem2442848 x) (@lem2442950 x)). Qed.
Lemma lem2442952 (x : int) : (term545 x) = term95.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2442953 (x : int) : (term527 x) = term95.
Proof. exact (TRANS (@lem2442951 x) (@lem2442952 x)). Qed.
Lemma lem2442954 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442955 (x : int) : (term546 x) = term392.
Proof. exact (MK_COMB (@lem2442954) (@lem2442953 x)). Qed.
Lemma lem2442956 (y : int) : (term586 y) = (term587 y).
Proof. exact (@lem1982763 (real_of_int y) (term201 y) term132). Qed.
Lemma lem2442957 (y : int) : (term549 y) = (term528 y).
Proof. exact (@lem1982715 term132 (real_of_int y)). Qed.
Lemma lem2442959 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2442960 : term80 = term134.
Proof. exact (@lem2442959 term81). Qed.
Lemma lem2442962 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2442963 : term132 = term137.
Proof. exact (@lem2442962 term81). Qed.
Lemma lem2442964 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2442965 : term529 = term530.
Proof. exact (MK_COMB (@lem2442964) (@lem2442963)). Qed.
Lemma lem2442966 : term531 = term532.
Proof. exact (MK_COMB (@lem2442965) (@lem2442960)). Qed.
Lemma lem2442967 : term533.
Proof. exact (@lem1981473 term132 term80 term80 term80 term95 term80). Qed.
Lemma lem2442969 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442970 : term497 = term503.
Proof. exact (@lem2442969 (NUMERAL 0) term81). Qed.
Lemma lem2442971 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442972 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442973 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442972 h1) (fun h1 : term503 = True => @lem2442971)). Qed.
Lemma lem2442974 : term503 = True.
Proof. exact (EQ_MP (@lem2442973) (@lem2442971)). Qed.
Lemma lem2442975 : term497 = True.
Proof. exact (TRANS (@lem2442970) (@lem2442974)). Qed.
Lemma lem2442976 : True = term497.
Proof. exact (SYM (@lem2442975)). Qed.
Lemma lem2442977 : term497.
Proof. exact (EQ_MP (@lem2442976) (@lem0)). Qed.
Lemma lem2442978 : term534.
Proof. exact (@lem2442967 (@lem2442977)). Qed.
Lemma lem2442980 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442981 : term497 = term503.
Proof. exact (@lem2442980 (NUMERAL 0) term81). Qed.
Lemma lem2442982 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442983 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442984 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442983 h1) (fun h1 : term503 = True => @lem2442982)). Qed.
Lemma lem2442985 : term503 = True.
Proof. exact (EQ_MP (@lem2442984) (@lem2442982)). Qed.
Lemma lem2442986 : term497 = True.
Proof. exact (TRANS (@lem2442981) (@lem2442985)). Qed.
Lemma lem2442987 : True = term497.
Proof. exact (SYM (@lem2442986)). Qed.
Lemma lem2442988 : term497.
Proof. exact (EQ_MP (@lem2442987) (@lem0)). Qed.
Lemma lem2442989 : term535.
Proof. exact (@lem2442978 (@lem2442988)). Qed.
Lemma lem2442991 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2442992 : term497 = term503.
Proof. exact (@lem2442991 (NUMERAL 0) term81). Qed.
Lemma lem2442993 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2442994 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2442995 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2442994 h1) (fun h1 : term503 = True => @lem2442993)). Qed.
Lemma lem2442996 : term503 = True.
Proof. exact (EQ_MP (@lem2442995) (@lem2442993)). Qed.
Lemma lem2442997 : term497 = True.
Proof. exact (TRANS (@lem2442992) (@lem2442996)). Qed.
Lemma lem2442998 : True = term497.
Proof. exact (SYM (@lem2442997)). Qed.
Lemma lem2442999 : term497.
Proof. exact (EQ_MP (@lem2442998) (@lem0)). Qed.
Lemma lem2443000 : term536.
Proof. exact (@lem2442989 (@lem2442999)). Qed.
Lemma lem2443002 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2443003 : term145 = term146.
Proof. exact (@lem2443002 term81 term81). Qed.
Lemma lem2443004 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2443005 : term148 = term81.
Proof. exact (EQ_MP (@lem2443004) (@lem940073)). Qed.
Lemma lem2443006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2443007 : term146 = term80.
Proof. exact (MK_COMB (@lem2443006) (@lem2443005)). Qed.
Lemma lem2443008 : term145 = term80.
Proof. exact (TRANS (@lem2443003) (@lem2443007)). Qed.
Lemma lem2443010 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2443011 : term140 = term151.
Proof. exact (@lem2443010 term81 term81). Qed.
Lemma lem2443012 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2443013 : term148 = term81.
Proof. exact (EQ_MP (@lem2443012) (@lem940073)). Qed.
Lemma lem2443014 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2443015 : term146 = term80.
Proof. exact (MK_COMB (@lem2443014) (@lem2443013)). Qed.
Lemma lem2443016 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2443017 : term151 = term132.
Proof. exact (MK_COMB (@lem2443016) (@lem2443015)). Qed.
Lemma lem2443018 : term140 = term132.
Proof. exact (TRANS (@lem2443011) (@lem2443017)). Qed.
Lemma lem2443019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2443020 : term537 = term529.
Proof. exact (MK_COMB (@lem2443019) (@lem2443018)). Qed.
Lemma lem2443021 : term538 = term531.
Proof. exact (MK_COMB (@lem2443020) (@lem2443008)). Qed.
Lemma lem2443023 (m : nat) : (term539 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2443024 : term531 = term95.
Proof. exact (@lem2443023 term81). Qed.
Lemma lem2443025 : term538 = term95.
Proof. exact (TRANS (@lem2443021) (@lem2443024)). Qed.
Lemma lem2443026 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2443027 : term540 = term541.
Proof. exact (MK_COMB (@lem2443026) (@lem2443025)). Qed.
Lemma lem2443028 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2443029 : term542 = term508.
Proof. exact (MK_COMB (@lem2443027) (@lem2443028)). Qed.
Lemma lem2443031 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2443032 : term508 = term95.
Proof. exact (@lem2443031 term81). Qed.
Lemma lem2443033 : term542 = term95.
Proof. exact (TRANS (@lem2443029) (@lem2443032)). Qed.
Lemma lem2443035 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2443036 : term145 = term146.
Proof. exact (@lem2443035 term81 term81). Qed.
Lemma lem2443037 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2443038 : term148 = term81.
Proof. exact (EQ_MP (@lem2443037) (@lem940073)). Qed.
Lemma lem2443039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2443040 : term146 = term80.
Proof. exact (MK_COMB (@lem2443039) (@lem2443038)). Qed.
Lemma lem2443041 : term145 = term80.
Proof. exact (TRANS (@lem2443036) (@lem2443040)). Qed.
Lemma lem2443042 : term541 = term541.
Proof. exact (eq_refl term541). Qed.
Lemma lem2443043 : term543 = term508.
Proof. exact (MK_COMB (@lem2443042) (@lem2443041)). Qed.
Lemma lem2443045 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2443046 : term508 = term95.
Proof. exact (@lem2443045 term81). Qed.
Lemma lem2443047 : term543 = term95.
Proof. exact (TRANS (@lem2443043) (@lem2443046)). Qed.
Lemma lem2443048 : term95 = term543.
Proof. exact (SYM (@lem2443047)). Qed.
Lemma lem2443049 : term542 = term543.
Proof. exact (TRANS (@lem2443033) (@lem2443048)). Qed.
Lemma lem2443050 : term532 = term179.
Proof. exact (@lem2443000 (@lem2443049)). Qed.
Lemma lem2443051 : term531 = term179.
Proof. exact (TRANS (@lem2442966) (@lem2443050)). Qed.
Lemma lem2443053 (x : real) : (term154 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2443054 : term179 = term95.
Proof. exact (@lem2443053 term95). Qed.
Lemma lem2443055 : term531 = term95.
Proof. exact (TRANS (@lem2443051) (@lem2443054)). Qed.
Lemma lem2443056 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2443057 : term544 = term541.
Proof. exact (MK_COMB (@lem2443056) (@lem2443055)). Qed.
Lemma lem2443058 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2443059 (y : int) : (term528 y) = (term545 y).
Proof. exact (MK_COMB (@lem2443057) (@lem2443058 y)). Qed.
Lemma lem2443060 (y : int) : (term549 y) = (term545 y).
Proof. exact (TRANS (@lem2442957 y) (@lem2443059 y)). Qed.
Lemma lem2443061 (y : int) : (term545 y) = term95.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2443062 (y : int) : (term549 y) = term95.
Proof. exact (TRANS (@lem2443060 y) (@lem2443061 y)). Qed.
Lemma lem2443063 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2443064 (y : int) : (term550 y) = term392.
Proof. exact (MK_COMB (@lem2443063) (@lem2443062 y)). Qed.
Lemma lem2443065 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem2443066 (y : int) : (term587 y) = term553.
Proof. exact (MK_COMB (@lem2443064 y) (@lem2443065)). Qed.
Lemma lem2443067 (y : int) : (term586 y) = term553.
Proof. exact (TRANS (@lem2442956 y) (@lem2443066 y)). Qed.
Lemma lem2443068 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2443069 (y : int) : (term586 y) = term132.
Proof. exact (TRANS (@lem2443067 y) (@lem2443068)). Qed.
Lemma lem2443070 (x : int) (y : int) : (term585 x y) = term553.
Proof. exact (MK_COMB (@lem2442955 x) (@lem2443069 y)). Qed.
Lemma lem2443071 (x : int) (y : int) : (term584 x y) = term553.
Proof. exact (TRANS (@lem2442847 x y) (@lem2443070 x y)). Qed.
Lemma lem2443072 : term553 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2443073 (x : int) (y : int) : (term584 x y) = term132.
Proof. exact (TRANS (@lem2443071 x y) (@lem2443072)). Qed.
Lemma lem2443074 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2443075 (x : int) (y : int) : (term614 x y) = term555.
Proof. exact (MK_COMB (@lem2443074) (@lem2443073 x y)). Qed.
Lemma lem2443076 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem2443077 (x : int) (y : int) : (term613 x y) = term556.
Proof. exact (MK_COMB (@lem2443075 x y) (@lem2443076)). Qed.
Lemma lem2443078 (n : int) (x : int) (y : int) (h1 : term490 n x y) : term556.
Proof. exact (EQ_MP (@lem2443077 x y) (@lem2442846 n x y h1)). Qed.
Lemma lem2443080 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2443081 : term556 = term557.
Proof. exact (@lem2443080 term95 term132). Qed.
Lemma lem2443083 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2443084 : term132 = term137.
Proof. exact (@lem2443083 term81). Qed.
Lemma lem2443086 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2443087 : term95 = term179.
Proof. exact (@lem2443086 (NUMERAL 0)). Qed.
Lemma lem2443088 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2443089 : term558 = term559.
Proof. exact (MK_COMB (@lem2443088) (@lem2443087)). Qed.
Lemma lem2443090 : term557 = term560.
Proof. exact (MK_COMB (@lem2443089) (@lem2443084)). Qed.
Lemma lem2443091 : term561.
Proof. exact (@lem1980026 term95 term80 term132 term80). Qed.
Lemma lem2443093 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2443094 : term497 = term503.
Proof. exact (@lem2443093 (NUMERAL 0) term81). Qed.
Lemma lem2443095 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2443096 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2443097 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2443096 h1) (fun h1 : term503 = True => @lem2443095)). Qed.
Lemma lem2443098 : term503 = True.
Proof. exact (EQ_MP (@lem2443097) (@lem2443095)). Qed.
Lemma lem2443099 : term497 = True.
Proof. exact (TRANS (@lem2443094) (@lem2443098)). Qed.
Lemma lem2443100 : True = term497.
Proof. exact (SYM (@lem2443099)). Qed.
Lemma lem2443101 : term497.
Proof. exact (EQ_MP (@lem2443100) (@lem0)). Qed.
Lemma lem2443102 : term562.
Proof. exact (@lem2443091 (@lem2443101)). Qed.
Lemma lem2443104 (m : nat) (n : nat) : (term502 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2443105 : term497 = term503.
Proof. exact (@lem2443104 (NUMERAL 0) term81). Qed.
Lemma lem2443106 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2443107 (h1 : term504 = (BIT1 0)) : term503 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2443108 : (term504 = (BIT1 0)) = (term503 = True).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2443107 h1) (fun h1 : term503 = True => @lem2443106)). Qed.
Lemma lem2443109 : term503 = True.
Proof. exact (EQ_MP (@lem2443108) (@lem2443106)). Qed.
Lemma lem2443110 : term497 = True.
Proof. exact (TRANS (@lem2443105) (@lem2443109)). Qed.
Lemma lem2443111 : True = term497.
Proof. exact (SYM (@lem2443110)). Qed.
Lemma lem2443112 : term497.
Proof. exact (EQ_MP (@lem2443111) (@lem0)). Qed.
Lemma lem2443113 : term560 = term563.
Proof. exact (@lem2443102 (@lem2443112)). Qed.
Lemma lem2443115 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2443116 : term140 = term151.
Proof. exact (@lem2443115 term81 term81). Qed.
Lemma lem2443117 : (term147 = (BIT1 0)) = (term148 = term81).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2443118 : term148 = term81.
Proof. exact (EQ_MP (@lem2443117) (@lem940073)). Qed.
Lemma lem2443119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2443120 : term146 = term80.
Proof. exact (MK_COMB (@lem2443119) (@lem2443118)). Qed.
Lemma lem2443121 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2443122 : term151 = term132.
Proof. exact (MK_COMB (@lem2443121) (@lem2443120)). Qed.
Lemma lem2443123 : term140 = term132.
Proof. exact (TRANS (@lem2443116) (@lem2443122)). Qed.
Lemma lem2443125 (x : nat) : (term507 x) = term95.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2443126 : term508 = term95.
Proof. exact (@lem2443125 term81). Qed.
Lemma lem2443127 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2443128 : term564 = term558.
Proof. exact (MK_COMB (@lem2443127) (@lem2443126)). Qed.
Lemma lem2443129 : term563 = term557.
Proof. exact (MK_COMB (@lem2443128) (@lem2443123)). Qed.
Lemma lem2443131 (m : nat) (n : nat) : (term565 m n) = (term566 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2443132 : term557 = term567.
Proof. exact (@lem2443131 (NUMERAL 0) term81). Qed.
Lemma lem2443133 : term504 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2443134 (h1 : term504 = (BIT1 0)) : (term81 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2443135 : (term504 = (BIT1 0)) = ((term81 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term504 = (BIT1 0) => @lem2443134 h1) (fun h1 : (term81 = (NUMERAL 0)) = False => @lem2443133)). Qed.
Lemma lem2443136 : (term81 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2443135) (@lem2443133)). Qed.
Lemma lem2443137 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2443138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2443139 : term568 = (and True).
Proof. exact (MK_COMB (@lem2443138) (@lem2443137)). Qed.
Lemma lem2443140 : term567 = (True /\ False).
Proof. exact (MK_COMB (@lem2443139) (@lem2443136)). Qed.
Lemma lem2443142 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2443143 : term567 = False.
Proof. exact (TRANS (@lem2443140) (@lem2443142)). Qed.
Lemma lem2443144 : term557 = False.
Proof. exact (TRANS (@lem2443132) (@lem2443143)). Qed.
Lemma lem2443145 : term563 = False.
Proof. exact (TRANS (@lem2443129) (@lem2443144)). Qed.
Lemma lem2443146 : term560 = False.
Proof. exact (TRANS (@lem2443113) (@lem2443145)). Qed.
Lemma lem2443147 : term557 = False.
Proof. exact (TRANS (@lem2443090) (@lem2443146)). Qed.
Lemma lem2443148 : term556 = False.
Proof. exact (TRANS (@lem2443081) (@lem2443147)). Qed.
Lemma lem2443149 (n : int) (x : int) (y : int) (h1 : term490 n x y) : False.
Proof. exact (EQ_MP (@lem2443148) (@lem2443078 n x y h1)). Qed.
Lemma lem2443150 (n : int) (x : int) (y : int) (h1 : term493 n x y) : False.
Proof. exact (or_elim (@lem2441531 n x y h1) (fun h0 : term488 n x y => @lem2442697 n x y h0) (fun h0 : term490 n x y => @lem2443149 n x y h0)). Qed.
Lemma lem2443151 (n : int) (x : int) (y : int) (h1 : term495 n x y) : False.
Proof. exact (or_elim (@lem2439958 n x y h1) (fun h0 : term449 n x y => @lem2441530 n x y h0) (fun h0 : term493 n x y => @lem2443150 n x y h0)). Qed.
Lemma lem2443152 (n : int) (x : int) (y : int) (h1 : term247 n x y) : term247 n x y.
Proof. exact (h1). Qed.
Lemma lem2443153 (n : int) (x : int) (y : int) (h1 : term247 n x y) : term495 n x y.
Proof. exact (EQ_MP (@lem2439957 n x y) (@lem2443152 n x y h1)). Qed.
Lemma lem2443154 (n : int) (x : int) (y : int) (h1 : term247 n x y) : (term495 n x y) = False.
Proof. exact (prop_ext (fun h2 : term495 n x y => @lem2443151 n x y h2) (fun h2 : False => @lem2443153 n x y h1)). Qed.
Lemma lem2443155 (n : int) (x : int) (y : int) (h1 : term247 n x y) : False.
Proof. exact (EQ_MP (@lem2443154 n x y h1) (@lem2443153 n x y h1)). Qed.
Lemma lem2443156 (n : int) (y : int) (x : int) (h1 : term120 n y x) : term120 n y x.
Proof. exact (h1). Qed.
Lemma lem2443157 (n : int) (y : int) (x : int) (h1 : term120 n y x) : term247 n x y.
Proof. exact (EQ_MP (@lem2438279 n x y) (@lem2443156 n y x h1)). Qed.
Lemma lem2443158 (n : int) (y : int) (x : int) (h1 : term120 n y x) : (term247 n x y) = False.
Proof. exact (prop_ext (fun h2 : term247 n x y => @lem2443155 n x y h2) (fun h2 : False => @lem2443157 n y x h1)). Qed.
Lemma lem2443159 (n : int) (y : int) (x : int) (h1 : term120 n y x) : False.
Proof. exact (EQ_MP (@lem2443158 n y x h1) (@lem2443157 n y x h1)). Qed.
Lemma lem2443160 (n : int) (y : int) (x : int) : term615 n y x.
Proof. exact (fun h0 : term120 n y x => @lem2443159 n y x h0). Qed.
Lemma lem2443161 (n : int) (y : int) (x : int) : term616 n y x.
Proof. exact (@lem1386578 (term617 n y x)). Qed.
Lemma lem2443164 (n : int) (y : int) (x : int) : term617 n y x.
Proof. exact (@lem2443161 n y x (@lem2443160 n y x)). Qed.
Lemma lem2443165 (n : int) (x : int) (y : int) : (term118 n y x) = (term56 n x y).
Proof. exact (SYM (@lem2437796 n y x)). Qed.
Lemma lem2443166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2443167 (n : int) (x : int) (y : int) : (term617 n y x) = (term45 n x y).
Proof. exact (MK_COMB (@lem2443166) (@lem2443165 n x y)). Qed.
Lemma lem2443168 (n : int) (x : int) (y : int) : term45 n x y.
Proof. exact (EQ_MP (@lem2443167 n x y) (@lem2443164 n y x)). Qed.
Lemma lem2443169 (n : int) (x : int) (y : int) : term46 n x y.
Proof. exact (EQ_MP (@lem2437617 n x y) (@lem2443168 n x y)). Qed.
Lemma lem2443170 (n : int) (x : int) (y : int) : (term46 n x y) = ((term46 n x y) = True).
Proof. exact (@lem7 (term46 n x y)). Qed.
Lemma lem2443171 (n : int) (x : int) (y : int) : (term46 n x y) = True.
Proof. exact (EQ_MP (@lem2443170 n x y) (@lem2443169 n x y)). Qed.
Lemma lem2443172 (n : int) (x : int) (y : int) : True = (term46 n x y).
Proof. exact (SYM (@lem2443171 n x y)). Qed.
Lemma lem2443173 (n : int) (x : int) (y : int) : term46 n x y.
Proof. exact (EQ_MP (@lem2443172 n x y) (@lem0)). Qed.
Lemma lem2443174 (x : int) (y : int) (n : int) (h1 : term42 x y n) : term57 n x y.
Proof. exact (@lem2443173 n x y (@lem2437612 x y n h1)). Qed.
Lemma lem2443175 (x : int) (y : int) (n : int) (h1 : term22 n x y) (h2 : term42 x y n) : term53 n x y.
Proof. exact (@lem2443174 x y n h2 (@lem2437611 n x y h1)). Qed.
Lemma lem2443176 (x : int) (y : int) (n : int) (h1 : term22 n x y) (h2 : term42 x y n) : x = y.
Proof. exact (@lem2443175 x y n h1 h2 (@lem2437616 n x y h1)). Qed.
Lemma lem2443177 (n : int) (x : int) (y : int) (h1 : term25 n x y) : term22 n x y.
Proof. exact (proj2 (@lem2437610 n x y h1)). Qed.
Lemma lem2443178 (n : int) (x : int) (y : int) (h1 : term25 n x y) : term42 x y n.
Proof. exact (proj1 (@lem2437610 n x y h1)). Qed.
Lemma lem2443179 (x : int) (y : int) (n : int) (h1 : term22 n x y) (h2 : term42 x y n) : (term22 n x y) = (x = y).
Proof. exact (prop_ext (fun h3 : term22 n x y => @lem2443176 x y n h1 h2) (fun h3 : x = y => @lem2437611 n x y h1)). Qed.
Lemma lem2443180 (x : int) (y : int) (n : int) (h1 : term22 n x y) (h2 : term42 x y n) : x = y.
Proof. exact (EQ_MP (@lem2443179 x y n h1 h2) (@lem2437611 n x y h1)). Qed.
Lemma lem2443181 (x : int) (y : int) (n : int) (h1 : term22 n x y) (h2 : term42 x y n) : (term42 x y n) = (x = y).
Proof. exact (prop_ext (fun h3 : term42 x y n => @lem2443180 x y n h1 h2) (fun h3 : x = y => @lem2437612 x y n h2)). Qed.
Lemma lem2443182 (x : int) (y : int) (n : int) (h1 : term22 n x y) (h2 : term42 x y n) : x = y.
Proof. exact (EQ_MP (@lem2443181 x y n h1 h2) (@lem2437612 x y n h2)). Qed.
Lemma lem2443183 (x : int) (y : int) (n : int) (h1 : term25 n x y) (h2 : term42 x y n) : (term22 n x y) = (x = y).
Proof. exact (prop_ext (fun h3 : term22 n x y => @lem2443182 x y n h3 h2) (fun h3 : x = y => @lem2443177 n x y h1)). Qed.
Lemma lem2443184 (x : int) (y : int) (n : int) (h1 : term25 n x y) (h2 : term42 x y n) : x = y.
Proof. exact (EQ_MP (@lem2443183 x y n h1 h2) (@lem2443177 n x y h1)). Qed.
Lemma lem2443185 (n : int) (x : int) (y : int) (h1 : term25 n x y) : (term42 x y n) = (x = y).
Proof. exact (prop_ext (fun h2 : term42 x y n => @lem2443184 x y n h1 h2) (fun h2 : x = y => @lem2443178 n x y h1)). Qed.
Lemma lem2443186 (n : int) (x : int) (y : int) (h1 : term25 n x y) : x = y.
Proof. exact (EQ_MP (@lem2443185 n x y h1) (@lem2443178 n x y h1)). Qed.
Lemma lem2443187 (n : int) (x : int) (y : int) : term29 n x y.
Proof. exact (fun h0 : term25 n x y => @lem2443186 n x y h0). Qed.
Lemma lem2443192 (x : int) (y : int) : term33 x y.
Proof. exact (fun n : int => @lem2443187 n x y). Qed.
Lemma lem2443197 (x : int) : term37 x.
Proof. exact (fun y : int => @lem2443192 x y). Qed.
Lemma lem2443202 : term41.
Proof. exact (fun x : int => @lem2443197 x). Qed.
Lemma lem2443203 : term40.
Proof. exact (EQ_MP (@lem2437609) (@lem2443202)). Qed.
