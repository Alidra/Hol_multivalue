Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_ADD_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import INT_ADD_SYM_spec.
Require Import INT_NEG_ADD_spec.
Require Import INT_OF_NUM_ADD_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LE_EXISTS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_EQ_INV2_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_INV_MUL_spec.
Require Import REAL_MUL_AC_spec.
Require Import REAL_POW_ADD_spec.
Require Import REAL_POW_EQ_0_spec.
Require Import REAL_ZPOW_NEG_spec.
Require Import REAL_ZPOW_NUM_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import WLOG_LE_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1338712_spec.
Require Import thm1338912_spec.
Require Import thm1338986_spec.
Require Import thm1340174_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
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
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318541_spec.
Require Import thm2318542_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841544_spec.
Require Import thm2841585_spec.
Require Import thm2841586_spec.
Require Import thm2841588_spec.
Require Import thm2841589_spec.
Require Import thm2841591_spec.
Require Import thm2841592_spec.
Require Import thm2841615_spec.
Require Import thm2841616_spec.
Require Import thm2954598_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3175507 (x : real) : term0 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem3175508 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3175509 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3175508 x) (@lem3175507 x)). Qed.
Lemma lem3175510 (x : real) (y : real) : term2 x y.
Proof. exact (@lem3175509 x y). Qed.
Lemma lem3175511 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem3175512 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem3175511 x y) (@lem3175510 x y)). Qed.
Lemma lem3175513 (x : real) (y : real) (z : real) : term4 x y z.
Proof. exact (@lem3175512 x y z). Qed.
Lemma lem3175514 (x : real) (y : real) (z : real) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem3175516 (x : real) : term7 x.
Proof. exact (@lem3169304 x). Qed.
Lemma lem3175517 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem3175518 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem3175517 x) (@lem3175516 x)). Qed.
Lemma lem3175519 (x : real) (n : nat) : term9 x n.
Proof. exact (@lem3175518 x n). Qed.
Lemma lem3175520 (x : real) (n : nat) : (term9 x n) = ((term10 x n) = (real_pow x n)).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem3175522 (x : real) : term11 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem3175523 (x : real) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem3175524 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem3175523 x) (@lem3175522 x)). Qed.
Lemma lem3175525 (x : real) (m : nat) : term13 x m.
Proof. exact (@lem3175524 x m). Qed.
Lemma lem3175526 (m : nat) (x : real) : (term13 x m) = (term14 m x).
Proof. exact (eq_refl (term13 x m)). Qed.
Lemma lem3175527 (m : nat) (x : real) : term14 m x.
Proof. exact (EQ_MP (@lem3175526 m x) (@lem3175525 x m)). Qed.
Lemma lem3175528 (m : nat) (x : real) (n : nat) : term15 m x n.
Proof. exact (@lem3175527 m x n). Qed.
Lemma lem3175529 (m : nat) (x : real) (n : nat) : (term15 m x n) = ((term16 x m n) = (term17 m x n)).
Proof. exact (eq_refl (term15 m x n)). Qed.
Lemma lem3175560 (n : int) (m : int) : (term18 n m) = ((term19 n m) = m).
Proof. exact (@lem2318604 ((term19 n m) = m)). Qed.
Lemma lem3175573 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3175574 (n : int) (m : int) : (term22 n m) = (term23 n m).
Proof. exact (@lem3175573 m (term19 n m)). Qed.
Lemma lem3175576 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3175577 (n : int) (m : int) : (term25 n m) = (term26 n m).
Proof. exact (@lem3175576 (term27 n m) m). Qed.
Lemma lem3175579 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3175580 (n : int) (m : int) : (term30 n m) = (term31 n m).
Proof. exact (@lem3175579 (term19 n m) term32). Qed.
Lemma lem3175582 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3175583 (n : int) (m : int) : (term33 n m) = (term34 n m).
Proof. exact (@lem3175582 (int_neg n) (int_add n m)). Qed.
Lemma lem3175585 (x : int) : (term35 x) = (term36 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem3175586 (n : int) : (term35 n) = (term36 n).
Proof. exact (@lem3175585 n). Qed.
Lemma lem3175587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175588 (n : int) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem3175587) (@lem3175586 n)). Qed.
Lemma lem3175590 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3175591 (n : int) (m : int) : (term28 n m) = (term29 n m).
Proof. exact (@lem3175590 n m). Qed.
Lemma lem3175592 (n : int) (m : int) : (term34 n m) = (term39 n m).
Proof. exact (MK_COMB (@lem3175588 n) (@lem3175591 n m)). Qed.
Lemma lem3175593 (n : int) (m : int) : (term33 n m) = (term39 n m).
Proof. exact (TRANS (@lem3175583 n m) (@lem3175592 n m)). Qed.
Lemma lem3175594 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175595 (n : int) (m : int) : (term40 n m) = (term41 n m).
Proof. exact (MK_COMB (@lem3175594) (@lem3175593 n m)). Qed.
Lemma lem3175597 (n : nat) : (term42 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3175598 : term43 = term44.
Proof. exact (@lem3175597 term45). Qed.
Lemma lem3175599 (n : int) (m : int) : (term31 n m) = (term46 n m).
Proof. exact (MK_COMB (@lem3175595 n m) (@lem3175598)). Qed.
Lemma lem3175600 (n : int) (m : int) : (term30 n m) = (term46 n m).
Proof. exact (TRANS (@lem3175580 n m) (@lem3175599 n m)). Qed.
Lemma lem3175601 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3175602 (n : int) (m : int) : (term47 n m) = (term48 n m).
Proof. exact (MK_COMB (@lem3175601) (@lem3175600 n m)). Qed.
Lemma lem3175603 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem3175604 (n : int) (m : int) : (term26 n m) = (term49 n m).
Proof. exact (MK_COMB (@lem3175602 n m) (@lem3175603 m)). Qed.
Lemma lem3175605 (n : int) (m : int) : (term25 n m) = (term49 n m).
Proof. exact (TRANS (@lem3175577 n m) (@lem3175604 n m)). Qed.
Lemma lem3175606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3175607 (n : int) (m : int) : (term50 n m) = (term51 n m).
Proof. exact (MK_COMB (@lem3175606) (@lem3175605 n m)). Qed.
Lemma lem3175609 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3175610 (n : int) (m : int) : (term52 n m) = (term53 n m).
Proof. exact (@lem3175609 (term54 m) (term19 n m)). Qed.
Lemma lem3175612 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3175613 (m : int) : (term55 m) = (term56 m).
Proof. exact (@lem3175612 m term32). Qed.
Lemma lem3175615 (n : nat) : (term42 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3175616 : term43 = term44.
Proof. exact (@lem3175615 term45). Qed.
Lemma lem3175617 (m : int) : (term57 m) = (term57 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem3175618 (m : int) : (term56 m) = (term58 m).
Proof. exact (MK_COMB (@lem3175617 m) (@lem3175616)). Qed.
Lemma lem3175619 (m : int) : (term55 m) = (term58 m).
Proof. exact (TRANS (@lem3175613 m) (@lem3175618 m)). Qed.
Lemma lem3175620 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3175621 (m : int) : (term59 m) = (term60 m).
Proof. exact (MK_COMB (@lem3175620) (@lem3175619 m)). Qed.
Lemma lem3175623 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3175624 (n : int) (m : int) : (term33 n m) = (term34 n m).
Proof. exact (@lem3175623 (int_neg n) (int_add n m)). Qed.
Lemma lem3175626 (x : int) : (term35 x) = (term36 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem3175627 (n : int) : (term35 n) = (term36 n).
Proof. exact (@lem3175626 n). Qed.
Lemma lem3175628 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175629 (n : int) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem3175628) (@lem3175627 n)). Qed.
Lemma lem3175631 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3175632 (n : int) (m : int) : (term28 n m) = (term29 n m).
Proof. exact (@lem3175631 n m). Qed.
Lemma lem3175633 (n : int) (m : int) : (term34 n m) = (term39 n m).
Proof. exact (MK_COMB (@lem3175629 n) (@lem3175632 n m)). Qed.
Lemma lem3175634 (n : int) (m : int) : (term33 n m) = (term39 n m).
Proof. exact (TRANS (@lem3175624 n m) (@lem3175633 n m)). Qed.
Lemma lem3175635 (n : int) (m : int) : (term53 n m) = (term61 n m).
Proof. exact (MK_COMB (@lem3175621 m) (@lem3175634 n m)). Qed.
Lemma lem3175636 (n : int) (m : int) : (term52 n m) = (term61 n m).
Proof. exact (TRANS (@lem3175610 n m) (@lem3175635 n m)). Qed.
Lemma lem3175637 (n : int) (m : int) : (term23 n m) = (term62 n m).
Proof. exact (MK_COMB (@lem3175607 n m) (@lem3175636 n m)). Qed.
Lemma lem3175639 (n : int) (m : int) : (term22 n m) = (term62 n m).
Proof. exact (TRANS (@lem3175574 n m) (@lem3175637 n m)). Qed.
Lemma lem3175643 (t : Prop) : (term63 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3175659 (n : int) (m : int) : (term64 n m) = (term62 n m).
Proof. exact (@lem3175643 (term62 n m)). Qed.
Lemma lem3175660 (n : int) (m : int) : (term49 n m) = (term65 n m).
Proof. exact (@lem1988287 (real_of_int m) (term46 n m)). Qed.
Lemma lem3175661 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3175668 (m : int) (n : int) : (term29 n m) = (term29 m n).
Proof. exact (@lem1982761 (real_of_int m) (real_of_int n)). Qed.
Lemma lem3175675 (n : int) : (term36 n) = (term66 n).
Proof. exact (@lem1982785 (real_of_int n)). Qed.
Lemma lem3175676 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175677 (n : int) : (term38 n) = (term67 n).
Proof. exact (MK_COMB (@lem3175676) (@lem3175675 n)). Qed.
Lemma lem3175678 (m : int) (n : int) : (term39 n m) = (term68 m n).
Proof. exact (MK_COMB (@lem3175677 n) (@lem3175668 m n)). Qed.
Lemma lem3175679 (m : int) (n : int) : (term68 m n) = (term69 m n).
Proof. exact (@lem1982757 (real_of_int m) (term66 n) (real_of_int n)). Qed.
Lemma lem3175680 (n : int) : (term70 n) = (term71 n).
Proof. exact (@lem1982713 term72 (real_of_int n)). Qed.
Lemma lem3175682 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3175683 : term44 = term74.
Proof. exact (@lem3175682 term45). Qed.
Lemma lem3175685 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3175686 : term72 = term77.
Proof. exact (@lem3175685 term45). Qed.
Lemma lem3175687 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175688 : term78 = term79.
Proof. exact (MK_COMB (@lem3175687) (@lem3175686)). Qed.
Lemma lem3175689 : term80 = term81.
Proof. exact (MK_COMB (@lem3175688) (@lem3175683)). Qed.
Lemma lem3175690 : term82.
Proof. exact (@lem1981473 term72 term44 term44 term44 term83 term44). Qed.
Lemma lem3175692 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3175693 : term85 = term86.
Proof. exact (@lem3175692 (NUMERAL 0) term45). Qed.
Lemma lem3175694 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3175695 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3175696 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3175695 h1) (fun h1 : term86 = True => @lem3175694)). Qed.
Lemma lem3175697 : term86 = True.
Proof. exact (EQ_MP (@lem3175696) (@lem3175694)). Qed.
Lemma lem3175698 : term85 = True.
Proof. exact (TRANS (@lem3175693) (@lem3175697)). Qed.
Lemma lem3175699 : True = term85.
Proof. exact (SYM (@lem3175698)). Qed.
Lemma lem3175700 : term85.
Proof. exact (EQ_MP (@lem3175699) (@lem0)). Qed.
Lemma lem3175701 : term88.
Proof. exact (@lem3175690 (@lem3175700)). Qed.
Lemma lem3175703 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3175704 : term85 = term86.
Proof. exact (@lem3175703 (NUMERAL 0) term45). Qed.
Lemma lem3175705 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3175706 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3175707 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3175706 h1) (fun h1 : term86 = True => @lem3175705)). Qed.
Lemma lem3175708 : term86 = True.
Proof. exact (EQ_MP (@lem3175707) (@lem3175705)). Qed.
Lemma lem3175709 : term85 = True.
Proof. exact (TRANS (@lem3175704) (@lem3175708)). Qed.
Lemma lem3175710 : True = term85.
Proof. exact (SYM (@lem3175709)). Qed.
Lemma lem3175711 : term85.
Proof. exact (EQ_MP (@lem3175710) (@lem0)). Qed.
Lemma lem3175712 : term89.
Proof. exact (@lem3175701 (@lem3175711)). Qed.
Lemma lem3175714 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3175715 : term85 = term86.
Proof. exact (@lem3175714 (NUMERAL 0) term45). Qed.
Lemma lem3175716 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3175717 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3175718 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3175717 h1) (fun h1 : term86 = True => @lem3175716)). Qed.
Lemma lem3175719 : term86 = True.
Proof. exact (EQ_MP (@lem3175718) (@lem3175716)). Qed.
Lemma lem3175720 : term85 = True.
Proof. exact (TRANS (@lem3175715) (@lem3175719)). Qed.
Lemma lem3175721 : True = term85.
Proof. exact (SYM (@lem3175720)). Qed.
Lemma lem3175722 : term85.
Proof. exact (EQ_MP (@lem3175721) (@lem0)). Qed.
Lemma lem3175723 : term90.
Proof. exact (@lem3175712 (@lem3175722)). Qed.
Lemma lem3175725 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3175726 : term93 = term94.
Proof. exact (@lem3175725 term45 term45). Qed.
Lemma lem3175727 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3175728 : term96 = term45.
Proof. exact (EQ_MP (@lem3175727) (@lem940073)). Qed.
Lemma lem3175729 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3175730 : term94 = term44.
Proof. exact (MK_COMB (@lem3175729) (@lem3175728)). Qed.
Lemma lem3175731 : term93 = term44.
Proof. exact (TRANS (@lem3175726) (@lem3175730)). Qed.
Lemma lem3175733 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3175734 : term99 = term100.
Proof. exact (@lem3175733 term45 term45). Qed.
Lemma lem3175735 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3175736 : term96 = term45.
Proof. exact (EQ_MP (@lem3175735) (@lem940073)). Qed.
Lemma lem3175737 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3175738 : term94 = term44.
Proof. exact (MK_COMB (@lem3175737) (@lem3175736)). Qed.
Lemma lem3175739 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3175740 : term100 = term72.
Proof. exact (MK_COMB (@lem3175739) (@lem3175738)). Qed.
Lemma lem3175741 : term99 = term72.
Proof. exact (TRANS (@lem3175734) (@lem3175740)). Qed.
Lemma lem3175742 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175743 : term101 = term78.
Proof. exact (MK_COMB (@lem3175742) (@lem3175741)). Qed.
Lemma lem3175744 : term102 = term80.
Proof. exact (MK_COMB (@lem3175743) (@lem3175731)). Qed.
Lemma lem3175746 (m : nat) : (term103 m) = term83.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3175747 : term80 = term83.
Proof. exact (@lem3175746 term45). Qed.
Lemma lem3175748 : term102 = term83.
Proof. exact (TRANS (@lem3175744) (@lem3175747)). Qed.
Lemma lem3175749 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3175750 : term104 = term105.
Proof. exact (MK_COMB (@lem3175749) (@lem3175748)). Qed.
Lemma lem3175751 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3175752 : term106 = term107.
Proof. exact (MK_COMB (@lem3175750) (@lem3175751)). Qed.
Lemma lem3175754 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3175755 : term107 = term83.
Proof. exact (@lem3175754 term45). Qed.
Lemma lem3175756 : term106 = term83.
Proof. exact (TRANS (@lem3175752) (@lem3175755)). Qed.
Lemma lem3175758 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3175759 : term93 = term94.
Proof. exact (@lem3175758 term45 term45). Qed.
Lemma lem3175760 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3175761 : term96 = term45.
Proof. exact (EQ_MP (@lem3175760) (@lem940073)). Qed.
Lemma lem3175762 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3175763 : term94 = term44.
Proof. exact (MK_COMB (@lem3175762) (@lem3175761)). Qed.
Lemma lem3175764 : term93 = term44.
Proof. exact (TRANS (@lem3175759) (@lem3175763)). Qed.
Lemma lem3175765 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem3175766 : term109 = term107.
Proof. exact (MK_COMB (@lem3175765) (@lem3175764)). Qed.
Lemma lem3175768 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3175769 : term107 = term83.
Proof. exact (@lem3175768 term45). Qed.
Lemma lem3175770 : term109 = term83.
Proof. exact (TRANS (@lem3175766) (@lem3175769)). Qed.
Lemma lem3175771 : term83 = term109.
Proof. exact (SYM (@lem3175770)). Qed.
Lemma lem3175772 : term106 = term109.
Proof. exact (TRANS (@lem3175756) (@lem3175771)). Qed.
Lemma lem3175773 : term81 = term110.
Proof. exact (@lem3175723 (@lem3175772)). Qed.
Lemma lem3175774 : term80 = term110.
Proof. exact (TRANS (@lem3175689) (@lem3175773)). Qed.
Lemma lem3175776 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3175777 : term110 = term83.
Proof. exact (@lem3175776 term83). Qed.
Lemma lem3175778 : term80 = term83.
Proof. exact (TRANS (@lem3175774) (@lem3175777)). Qed.
Lemma lem3175779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3175780 : term112 = term105.
Proof. exact (MK_COMB (@lem3175779) (@lem3175778)). Qed.
Lemma lem3175781 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3175782 (n : int) : (term71 n) = (term113 n).
Proof. exact (MK_COMB (@lem3175780) (@lem3175781 n)). Qed.
Lemma lem3175783 (n : int) : (term70 n) = (term113 n).
Proof. exact (TRANS (@lem3175680 n) (@lem3175782 n)). Qed.
Lemma lem3175784 (n : int) : (term113 n) = term83.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem3175785 (n : int) : (term70 n) = term83.
Proof. exact (TRANS (@lem3175783 n) (@lem3175784 n)). Qed.
Lemma lem3175786 (m : int) : (term57 m) = (term57 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem3175787 (n : int) (m : int) : (term69 m n) = (term114 m).
Proof. exact (MK_COMB (@lem3175786 m) (@lem3175785 n)). Qed.
Lemma lem3175788 (n : int) (m : int) : (term68 m n) = (term114 m).
Proof. exact (TRANS (@lem3175679 m n) (@lem3175787 n m)). Qed.
Lemma lem3175789 (m : int) : (term114 m) = (real_of_int m).
Proof. exact (@lem1982723 (real_of_int m)). Qed.
Lemma lem3175790 (n : int) (m : int) : (term68 m n) = (real_of_int m).
Proof. exact (TRANS (@lem3175788 n m) (@lem3175789 m)). Qed.
Lemma lem3175791 (n : int) (m : int) : (term39 n m) = (real_of_int m).
Proof. exact (TRANS (@lem3175678 m n) (@lem3175790 n m)). Qed.
Lemma lem3175792 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175793 (n : int) (m : int) : (term41 n m) = (term57 m).
Proof. exact (MK_COMB (@lem3175792) (@lem3175791 n m)). Qed.
Lemma lem3175796 (n : int) (m : int) : (term46 n m) = (term58 m).
Proof. exact (MK_COMB (@lem3175793 n m) (@lem3175661)). Qed.
Lemma lem3175799 (m : int) : (term115 m) = (term115 m).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem3175800 (n : int) (m : int) : (term116 n m) = (term117 m).
Proof. exact (MK_COMB (@lem3175799 m) (@lem3175796 n m)). Qed.
Lemma lem3175801 (m : int) : (term117 m) = (term118 m).
Proof. exact (@lem1982792 (real_of_int m) (term58 m)). Qed.
Lemma lem3175802 (m : int) : (term119 m) = (term120 m).
Proof. exact (@lem1982781 (real_of_int m) term72 term44). Qed.
Lemma lem3175804 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3175805 : term44 = term74.
Proof. exact (@lem3175804 term45). Qed.
Lemma lem3175807 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3175808 : term72 = term77.
Proof. exact (@lem3175807 term45). Qed.
Lemma lem3175809 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3175810 : term121 = term122.
Proof. exact (MK_COMB (@lem3175809) (@lem3175808)). Qed.
Lemma lem3175811 : term99 = term123.
Proof. exact (MK_COMB (@lem3175810) (@lem3175805)). Qed.
Lemma lem3175812 : term123 = term124.
Proof. exact (@lem1981613 term72 term44 term44 term44). Qed.
Lemma lem3175814 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3175815 : term93 = term94.
Proof. exact (@lem3175814 term45 term45). Qed.
Lemma lem3175816 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3175817 : term96 = term45.
Proof. exact (EQ_MP (@lem3175816) (@lem940073)). Qed.
Lemma lem3175818 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3175819 : term94 = term44.
Proof. exact (MK_COMB (@lem3175818) (@lem3175817)). Qed.
Lemma lem3175820 : term93 = term44.
Proof. exact (TRANS (@lem3175815) (@lem3175819)). Qed.
Lemma lem3175822 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3175823 : term99 = term100.
Proof. exact (@lem3175822 term45 term45). Qed.
Lemma lem3175824 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3175825 : term96 = term45.
Proof. exact (EQ_MP (@lem3175824) (@lem940073)). Qed.
Lemma lem3175826 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3175827 : term94 = term44.
Proof. exact (MK_COMB (@lem3175826) (@lem3175825)). Qed.
Lemma lem3175828 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3175829 : term100 = term72.
Proof. exact (MK_COMB (@lem3175828) (@lem3175827)). Qed.
Lemma lem3175830 : term99 = term72.
Proof. exact (TRANS (@lem3175823) (@lem3175829)). Qed.
Lemma lem3175831 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3175832 : term125 = term126.
Proof. exact (MK_COMB (@lem3175831) (@lem3175830)). Qed.
Lemma lem3175833 : term124 = term77.
Proof. exact (MK_COMB (@lem3175832) (@lem3175820)). Qed.
Lemma lem3175834 : term123 = term77.
Proof. exact (TRANS (@lem3175812) (@lem3175833)). Qed.
Lemma lem3175835 : term99 = term77.
Proof. exact (TRANS (@lem3175811) (@lem3175834)). Qed.
Lemma lem3175837 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3175838 : term77 = term72.
Proof. exact (@lem3175837 term72). Qed.
Lemma lem3175839 : term99 = term72.
Proof. exact (TRANS (@lem3175835) (@lem3175838)). Qed.
Lemma lem3175842 (m : int) : (term67 m) = (term67 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem3175843 (m : int) : (term120 m) = (term127 m).
Proof. exact (MK_COMB (@lem3175842 m) (@lem3175839)). Qed.
Lemma lem3175844 (m : int) : (term119 m) = (term127 m).
Proof. exact (TRANS (@lem3175802 m) (@lem3175843 m)). Qed.
Lemma lem3175845 (m : int) : (term57 m) = (term57 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem3175846 (m : int) : (term118 m) = (term128 m).
Proof. exact (MK_COMB (@lem3175845 m) (@lem3175844 m)). Qed.
Lemma lem3175847 (m : int) : (term128 m) = (term129 m).
Proof. exact (@lem1982763 (real_of_int m) (term66 m) term72). Qed.
Lemma lem3175848 (m : int) : (term130 m) = (term71 m).
Proof. exact (@lem1982715 term72 (real_of_int m)). Qed.
Lemma lem3175850 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3175851 : term44 = term74.
Proof. exact (@lem3175850 term45). Qed.
Lemma lem3175853 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3175854 : term72 = term77.
Proof. exact (@lem3175853 term45). Qed.
Lemma lem3175855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175856 : term78 = term79.
Proof. exact (MK_COMB (@lem3175855) (@lem3175854)). Qed.
Lemma lem3175857 : term80 = term81.
Proof. exact (MK_COMB (@lem3175856) (@lem3175851)). Qed.
Lemma lem3175858 : term82.
Proof. exact (@lem1981473 term72 term44 term44 term44 term83 term44). Qed.
Lemma lem3175860 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3175861 : term85 = term86.
Proof. exact (@lem3175860 (NUMERAL 0) term45). Qed.
Lemma lem3175862 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3175863 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3175864 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3175863 h1) (fun h1 : term86 = True => @lem3175862)). Qed.
Lemma lem3175865 : term86 = True.
Proof. exact (EQ_MP (@lem3175864) (@lem3175862)). Qed.
Lemma lem3175866 : term85 = True.
Proof. exact (TRANS (@lem3175861) (@lem3175865)). Qed.
Lemma lem3175867 : True = term85.
Proof. exact (SYM (@lem3175866)). Qed.
Lemma lem3175868 : term85.
Proof. exact (EQ_MP (@lem3175867) (@lem0)). Qed.
Lemma lem3175869 : term88.
Proof. exact (@lem3175858 (@lem3175868)). Qed.
Lemma lem3175871 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3175872 : term85 = term86.
Proof. exact (@lem3175871 (NUMERAL 0) term45). Qed.
Lemma lem3175873 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3175874 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3175875 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3175874 h1) (fun h1 : term86 = True => @lem3175873)). Qed.
Lemma lem3175876 : term86 = True.
Proof. exact (EQ_MP (@lem3175875) (@lem3175873)). Qed.
Lemma lem3175877 : term85 = True.
Proof. exact (TRANS (@lem3175872) (@lem3175876)). Qed.
Lemma lem3175878 : True = term85.
Proof. exact (SYM (@lem3175877)). Qed.
Lemma lem3175879 : term85.
Proof. exact (EQ_MP (@lem3175878) (@lem0)). Qed.
Lemma lem3175880 : term89.
Proof. exact (@lem3175869 (@lem3175879)). Qed.
Lemma lem3175882 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3175883 : term85 = term86.
Proof. exact (@lem3175882 (NUMERAL 0) term45). Qed.
Lemma lem3175884 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3175885 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3175886 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3175885 h1) (fun h1 : term86 = True => @lem3175884)). Qed.
Lemma lem3175887 : term86 = True.
Proof. exact (EQ_MP (@lem3175886) (@lem3175884)). Qed.
Lemma lem3175888 : term85 = True.
Proof. exact (TRANS (@lem3175883) (@lem3175887)). Qed.
Lemma lem3175889 : True = term85.
Proof. exact (SYM (@lem3175888)). Qed.
Lemma lem3175890 : term85.
Proof. exact (EQ_MP (@lem3175889) (@lem0)). Qed.
Lemma lem3175891 : term90.
Proof. exact (@lem3175880 (@lem3175890)). Qed.
Lemma lem3175893 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3175894 : term93 = term94.
Proof. exact (@lem3175893 term45 term45). Qed.
Lemma lem3175895 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3175896 : term96 = term45.
Proof. exact (EQ_MP (@lem3175895) (@lem940073)). Qed.
Lemma lem3175897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3175898 : term94 = term44.
Proof. exact (MK_COMB (@lem3175897) (@lem3175896)). Qed.
Lemma lem3175899 : term93 = term44.
Proof. exact (TRANS (@lem3175894) (@lem3175898)). Qed.
Lemma lem3175901 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3175902 : term99 = term100.
Proof. exact (@lem3175901 term45 term45). Qed.
Lemma lem3175903 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3175904 : term96 = term45.
Proof. exact (EQ_MP (@lem3175903) (@lem940073)). Qed.
Lemma lem3175905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3175906 : term94 = term44.
Proof. exact (MK_COMB (@lem3175905) (@lem3175904)). Qed.
Lemma lem3175907 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3175908 : term100 = term72.
Proof. exact (MK_COMB (@lem3175907) (@lem3175906)). Qed.
Lemma lem3175909 : term99 = term72.
Proof. exact (TRANS (@lem3175902) (@lem3175908)). Qed.
Lemma lem3175910 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175911 : term101 = term78.
Proof. exact (MK_COMB (@lem3175910) (@lem3175909)). Qed.
Lemma lem3175912 : term102 = term80.
Proof. exact (MK_COMB (@lem3175911) (@lem3175899)). Qed.
Lemma lem3175914 (m : nat) : (term103 m) = term83.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3175915 : term80 = term83.
Proof. exact (@lem3175914 term45). Qed.
Lemma lem3175916 : term102 = term83.
Proof. exact (TRANS (@lem3175912) (@lem3175915)). Qed.
Lemma lem3175917 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3175918 : term104 = term105.
Proof. exact (MK_COMB (@lem3175917) (@lem3175916)). Qed.
Lemma lem3175919 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3175920 : term106 = term107.
Proof. exact (MK_COMB (@lem3175918) (@lem3175919)). Qed.
Lemma lem3175922 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3175923 : term107 = term83.
Proof. exact (@lem3175922 term45). Qed.
Lemma lem3175924 : term106 = term83.
Proof. exact (TRANS (@lem3175920) (@lem3175923)). Qed.
Lemma lem3175926 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3175927 : term93 = term94.
Proof. exact (@lem3175926 term45 term45). Qed.
Lemma lem3175928 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3175929 : term96 = term45.
Proof. exact (EQ_MP (@lem3175928) (@lem940073)). Qed.
Lemma lem3175930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3175931 : term94 = term44.
Proof. exact (MK_COMB (@lem3175930) (@lem3175929)). Qed.
Lemma lem3175932 : term93 = term44.
Proof. exact (TRANS (@lem3175927) (@lem3175931)). Qed.
Lemma lem3175933 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem3175934 : term109 = term107.
Proof. exact (MK_COMB (@lem3175933) (@lem3175932)). Qed.
Lemma lem3175936 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3175937 : term107 = term83.
Proof. exact (@lem3175936 term45). Qed.
Lemma lem3175938 : term109 = term83.
Proof. exact (TRANS (@lem3175934) (@lem3175937)). Qed.
Lemma lem3175939 : term83 = term109.
Proof. exact (SYM (@lem3175938)). Qed.
Lemma lem3175940 : term106 = term109.
Proof. exact (TRANS (@lem3175924) (@lem3175939)). Qed.
Lemma lem3175941 : term81 = term110.
Proof. exact (@lem3175891 (@lem3175940)). Qed.
Lemma lem3175942 : term80 = term110.
Proof. exact (TRANS (@lem3175857) (@lem3175941)). Qed.
Lemma lem3175944 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3175945 : term110 = term83.
Proof. exact (@lem3175944 term83). Qed.
Lemma lem3175946 : term80 = term83.
Proof. exact (TRANS (@lem3175942) (@lem3175945)). Qed.
Lemma lem3175947 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3175948 : term112 = term105.
Proof. exact (MK_COMB (@lem3175947) (@lem3175946)). Qed.
Lemma lem3175949 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem3175950 (m : int) : (term71 m) = (term113 m).
Proof. exact (MK_COMB (@lem3175948) (@lem3175949 m)). Qed.
Lemma lem3175951 (m : int) : (term130 m) = (term113 m).
Proof. exact (TRANS (@lem3175848 m) (@lem3175950 m)). Qed.
Lemma lem3175952 (m : int) : (term113 m) = term83.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem3175953 (m : int) : (term130 m) = term83.
Proof. exact (TRANS (@lem3175951 m) (@lem3175952 m)). Qed.
Lemma lem3175954 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175955 (m : int) : (term131 m) = term132.
Proof. exact (MK_COMB (@lem3175954) (@lem3175953 m)). Qed.
Lemma lem3175956 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem3175957 (m : int) : (term129 m) = term133.
Proof. exact (MK_COMB (@lem3175955 m) (@lem3175956)). Qed.
Lemma lem3175958 (m : int) : (term128 m) = term133.
Proof. exact (TRANS (@lem3175847 m) (@lem3175957 m)). Qed.
Lemma lem3175959 : term133 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem3175960 (m : int) : (term128 m) = term72.
Proof. exact (TRANS (@lem3175958 m) (@lem3175959)). Qed.
Lemma lem3175961 (m : int) : (term118 m) = term72.
Proof. exact (TRANS (@lem3175846 m) (@lem3175960 m)). Qed.
Lemma lem3175962 (m : int) : (term117 m) = term72.
Proof. exact (TRANS (@lem3175801 m) (@lem3175961 m)). Qed.
Lemma lem3175963 (n : int) (m : int) : (term116 n m) = term72.
Proof. exact (TRANS (@lem3175800 n m) (@lem3175962 m)). Qed.
Lemma lem3175964 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3175965 (n : int) (m : int) : (term134 n m) = term135.
Proof. exact (MK_COMB (@lem3175964) (@lem3175963 n m)). Qed.
Lemma lem3175966 : term83 = term83.
Proof. exact (eq_refl term83). Qed.
Lemma lem3175967 (n : int) (m : int) : (term65 n m) = term136.
Proof. exact (MK_COMB (@lem3175965 n m) (@lem3175966)). Qed.
Lemma lem3175968 (n : int) (m : int) : (term49 n m) = term136.
Proof. exact (TRANS (@lem3175660 n m) (@lem3175967 n m)). Qed.
Lemma lem3175969 (n : int) (m : int) : (term61 n m) = (term137 n m).
Proof. exact (@lem1988287 (term39 n m) (term58 m)). Qed.
Lemma lem3175976 (m : int) : (term58 m) = (term58 m).
Proof. exact (eq_refl (term58 m)). Qed.
Lemma lem3175983 (m : int) (n : int) : (term29 n m) = (term29 m n).
Proof. exact (@lem1982761 (real_of_int m) (real_of_int n)). Qed.
Lemma lem3175990 (n : int) : (term36 n) = (term66 n).
Proof. exact (@lem1982785 (real_of_int n)). Qed.
Lemma lem3175991 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3175992 (n : int) : (term38 n) = (term67 n).
Proof. exact (MK_COMB (@lem3175991) (@lem3175990 n)). Qed.
Lemma lem3175993 (m : int) (n : int) : (term39 n m) = (term68 m n).
Proof. exact (MK_COMB (@lem3175992 n) (@lem3175983 m n)). Qed.
Lemma lem3175994 (m : int) (n : int) : (term68 m n) = (term69 m n).
Proof. exact (@lem1982757 (real_of_int m) (term66 n) (real_of_int n)). Qed.
Lemma lem3175995 (n : int) : (term70 n) = (term71 n).
Proof. exact (@lem1982713 term72 (real_of_int n)). Qed.
Lemma lem3175997 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3175998 : term44 = term74.
Proof. exact (@lem3175997 term45). Qed.
Lemma lem3176000 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176001 : term72 = term77.
Proof. exact (@lem3176000 term45). Qed.
Lemma lem3176002 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176003 : term78 = term79.
Proof. exact (MK_COMB (@lem3176002) (@lem3176001)). Qed.
Lemma lem3176004 : term80 = term81.
Proof. exact (MK_COMB (@lem3176003) (@lem3175998)). Qed.
Lemma lem3176005 : term82.
Proof. exact (@lem1981473 term72 term44 term44 term44 term83 term44). Qed.
Lemma lem3176007 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176008 : term85 = term86.
Proof. exact (@lem3176007 (NUMERAL 0) term45). Qed.
Lemma lem3176009 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176010 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176011 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176010 h1) (fun h1 : term86 = True => @lem3176009)). Qed.
Lemma lem3176012 : term86 = True.
Proof. exact (EQ_MP (@lem3176011) (@lem3176009)). Qed.
Lemma lem3176013 : term85 = True.
Proof. exact (TRANS (@lem3176008) (@lem3176012)). Qed.
Lemma lem3176014 : True = term85.
Proof. exact (SYM (@lem3176013)). Qed.
Lemma lem3176015 : term85.
Proof. exact (EQ_MP (@lem3176014) (@lem0)). Qed.
Lemma lem3176016 : term88.
Proof. exact (@lem3176005 (@lem3176015)). Qed.
Lemma lem3176018 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176019 : term85 = term86.
Proof. exact (@lem3176018 (NUMERAL 0) term45). Qed.
Lemma lem3176020 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176021 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176022 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176021 h1) (fun h1 : term86 = True => @lem3176020)). Qed.
Lemma lem3176023 : term86 = True.
Proof. exact (EQ_MP (@lem3176022) (@lem3176020)). Qed.
Lemma lem3176024 : term85 = True.
Proof. exact (TRANS (@lem3176019) (@lem3176023)). Qed.
Lemma lem3176025 : True = term85.
Proof. exact (SYM (@lem3176024)). Qed.
Lemma lem3176026 : term85.
Proof. exact (EQ_MP (@lem3176025) (@lem0)). Qed.
Lemma lem3176027 : term89.
Proof. exact (@lem3176016 (@lem3176026)). Qed.
Lemma lem3176029 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176030 : term85 = term86.
Proof. exact (@lem3176029 (NUMERAL 0) term45). Qed.
Lemma lem3176031 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176032 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176033 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176032 h1) (fun h1 : term86 = True => @lem3176031)). Qed.
Lemma lem3176034 : term86 = True.
Proof. exact (EQ_MP (@lem3176033) (@lem3176031)). Qed.
Lemma lem3176035 : term85 = True.
Proof. exact (TRANS (@lem3176030) (@lem3176034)). Qed.
Lemma lem3176036 : True = term85.
Proof. exact (SYM (@lem3176035)). Qed.
Lemma lem3176037 : term85.
Proof. exact (EQ_MP (@lem3176036) (@lem0)). Qed.
Lemma lem3176038 : term90.
Proof. exact (@lem3176027 (@lem3176037)). Qed.
Lemma lem3176040 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176041 : term93 = term94.
Proof. exact (@lem3176040 term45 term45). Qed.
Lemma lem3176042 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176043 : term96 = term45.
Proof. exact (EQ_MP (@lem3176042) (@lem940073)). Qed.
Lemma lem3176044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176045 : term94 = term44.
Proof. exact (MK_COMB (@lem3176044) (@lem3176043)). Qed.
Lemma lem3176046 : term93 = term44.
Proof. exact (TRANS (@lem3176041) (@lem3176045)). Qed.
Lemma lem3176048 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3176049 : term99 = term100.
Proof. exact (@lem3176048 term45 term45). Qed.
Lemma lem3176050 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176051 : term96 = term45.
Proof. exact (EQ_MP (@lem3176050) (@lem940073)). Qed.
Lemma lem3176052 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176053 : term94 = term44.
Proof. exact (MK_COMB (@lem3176052) (@lem3176051)). Qed.
Lemma lem3176054 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176055 : term100 = term72.
Proof. exact (MK_COMB (@lem3176054) (@lem3176053)). Qed.
Lemma lem3176056 : term99 = term72.
Proof. exact (TRANS (@lem3176049) (@lem3176055)). Qed.
Lemma lem3176057 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176058 : term101 = term78.
Proof. exact (MK_COMB (@lem3176057) (@lem3176056)). Qed.
Lemma lem3176059 : term102 = term80.
Proof. exact (MK_COMB (@lem3176058) (@lem3176046)). Qed.
Lemma lem3176061 (m : nat) : (term103 m) = term83.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3176062 : term80 = term83.
Proof. exact (@lem3176061 term45). Qed.
Lemma lem3176063 : term102 = term83.
Proof. exact (TRANS (@lem3176059) (@lem3176062)). Qed.
Lemma lem3176064 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176065 : term104 = term105.
Proof. exact (MK_COMB (@lem3176064) (@lem3176063)). Qed.
Lemma lem3176066 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3176067 : term106 = term107.
Proof. exact (MK_COMB (@lem3176065) (@lem3176066)). Qed.
Lemma lem3176069 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3176070 : term107 = term83.
Proof. exact (@lem3176069 term45). Qed.
Lemma lem3176071 : term106 = term83.
Proof. exact (TRANS (@lem3176067) (@lem3176070)). Qed.
Lemma lem3176073 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176074 : term93 = term94.
Proof. exact (@lem3176073 term45 term45). Qed.
Lemma lem3176075 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176076 : term96 = term45.
Proof. exact (EQ_MP (@lem3176075) (@lem940073)). Qed.
Lemma lem3176077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176078 : term94 = term44.
Proof. exact (MK_COMB (@lem3176077) (@lem3176076)). Qed.
Lemma lem3176079 : term93 = term44.
Proof. exact (TRANS (@lem3176074) (@lem3176078)). Qed.
Lemma lem3176080 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem3176081 : term109 = term107.
Proof. exact (MK_COMB (@lem3176080) (@lem3176079)). Qed.
Lemma lem3176083 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3176084 : term107 = term83.
Proof. exact (@lem3176083 term45). Qed.
Lemma lem3176085 : term109 = term83.
Proof. exact (TRANS (@lem3176081) (@lem3176084)). Qed.
Lemma lem3176086 : term83 = term109.
Proof. exact (SYM (@lem3176085)). Qed.
Lemma lem3176087 : term106 = term109.
Proof. exact (TRANS (@lem3176071) (@lem3176086)). Qed.
Lemma lem3176088 : term81 = term110.
Proof. exact (@lem3176038 (@lem3176087)). Qed.
Lemma lem3176089 : term80 = term110.
Proof. exact (TRANS (@lem3176004) (@lem3176088)). Qed.
Lemma lem3176091 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3176092 : term110 = term83.
Proof. exact (@lem3176091 term83). Qed.
Lemma lem3176093 : term80 = term83.
Proof. exact (TRANS (@lem3176089) (@lem3176092)). Qed.
Lemma lem3176094 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176095 : term112 = term105.
Proof. exact (MK_COMB (@lem3176094) (@lem3176093)). Qed.
Lemma lem3176096 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3176097 (n : int) : (term71 n) = (term113 n).
Proof. exact (MK_COMB (@lem3176095) (@lem3176096 n)). Qed.
Lemma lem3176098 (n : int) : (term70 n) = (term113 n).
Proof. exact (TRANS (@lem3175995 n) (@lem3176097 n)). Qed.
Lemma lem3176099 (n : int) : (term113 n) = term83.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem3176100 (n : int) : (term70 n) = term83.
Proof. exact (TRANS (@lem3176098 n) (@lem3176099 n)). Qed.
Lemma lem3176101 (m : int) : (term57 m) = (term57 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem3176102 (n : int) (m : int) : (term69 m n) = (term114 m).
Proof. exact (MK_COMB (@lem3176101 m) (@lem3176100 n)). Qed.
Lemma lem3176103 (n : int) (m : int) : (term68 m n) = (term114 m).
Proof. exact (TRANS (@lem3175994 m n) (@lem3176102 n m)). Qed.
Lemma lem3176104 (m : int) : (term114 m) = (real_of_int m).
Proof. exact (@lem1982723 (real_of_int m)). Qed.
Lemma lem3176105 (n : int) (m : int) : (term68 m n) = (real_of_int m).
Proof. exact (TRANS (@lem3176103 n m) (@lem3176104 m)). Qed.
Lemma lem3176106 (n : int) (m : int) : (term39 n m) = (real_of_int m).
Proof. exact (TRANS (@lem3175993 m n) (@lem3176105 n m)). Qed.
Lemma lem3176107 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem3176108 (n : int) (m : int) : (term138 n m) = (term115 m).
Proof. exact (MK_COMB (@lem3176107) (@lem3176106 n m)). Qed.
Lemma lem3176109 (n : int) (m : int) : (term139 n m) = (term117 m).
Proof. exact (MK_COMB (@lem3176108 n m) (@lem3175976 m)). Qed.
Lemma lem3176110 (m : int) : (term117 m) = (term118 m).
Proof. exact (@lem1982792 (real_of_int m) (term58 m)). Qed.
Lemma lem3176111 (m : int) : (term119 m) = (term120 m).
Proof. exact (@lem1982781 (real_of_int m) term72 term44). Qed.
Lemma lem3176113 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3176114 : term44 = term74.
Proof. exact (@lem3176113 term45). Qed.
Lemma lem3176116 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176117 : term72 = term77.
Proof. exact (@lem3176116 term45). Qed.
Lemma lem3176118 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176119 : term121 = term122.
Proof. exact (MK_COMB (@lem3176118) (@lem3176117)). Qed.
Lemma lem3176120 : term99 = term123.
Proof. exact (MK_COMB (@lem3176119) (@lem3176114)). Qed.
Lemma lem3176121 : term123 = term124.
Proof. exact (@lem1981613 term72 term44 term44 term44). Qed.
Lemma lem3176123 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176124 : term93 = term94.
Proof. exact (@lem3176123 term45 term45). Qed.
Lemma lem3176125 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176126 : term96 = term45.
Proof. exact (EQ_MP (@lem3176125) (@lem940073)). Qed.
Lemma lem3176127 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176128 : term94 = term44.
Proof. exact (MK_COMB (@lem3176127) (@lem3176126)). Qed.
Lemma lem3176129 : term93 = term44.
Proof. exact (TRANS (@lem3176124) (@lem3176128)). Qed.
Lemma lem3176131 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3176132 : term99 = term100.
Proof. exact (@lem3176131 term45 term45). Qed.
Lemma lem3176133 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176134 : term96 = term45.
Proof. exact (EQ_MP (@lem3176133) (@lem940073)). Qed.
Lemma lem3176135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176136 : term94 = term44.
Proof. exact (MK_COMB (@lem3176135) (@lem3176134)). Qed.
Lemma lem3176137 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176138 : term100 = term72.
Proof. exact (MK_COMB (@lem3176137) (@lem3176136)). Qed.
Lemma lem3176139 : term99 = term72.
Proof. exact (TRANS (@lem3176132) (@lem3176138)). Qed.
Lemma lem3176140 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3176141 : term125 = term126.
Proof. exact (MK_COMB (@lem3176140) (@lem3176139)). Qed.
Lemma lem3176142 : term124 = term77.
Proof. exact (MK_COMB (@lem3176141) (@lem3176129)). Qed.
Lemma lem3176143 : term123 = term77.
Proof. exact (TRANS (@lem3176121) (@lem3176142)). Qed.
Lemma lem3176144 : term99 = term77.
Proof. exact (TRANS (@lem3176120) (@lem3176143)). Qed.
Lemma lem3176146 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3176147 : term77 = term72.
Proof. exact (@lem3176146 term72). Qed.
Lemma lem3176148 : term99 = term72.
Proof. exact (TRANS (@lem3176144) (@lem3176147)). Qed.
Lemma lem3176151 (m : int) : (term67 m) = (term67 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem3176152 (m : int) : (term120 m) = (term127 m).
Proof. exact (MK_COMB (@lem3176151 m) (@lem3176148)). Qed.
Lemma lem3176153 (m : int) : (term119 m) = (term127 m).
Proof. exact (TRANS (@lem3176111 m) (@lem3176152 m)). Qed.
Lemma lem3176154 (m : int) : (term57 m) = (term57 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem3176155 (m : int) : (term118 m) = (term128 m).
Proof. exact (MK_COMB (@lem3176154 m) (@lem3176153 m)). Qed.
Lemma lem3176156 (m : int) : (term128 m) = (term129 m).
Proof. exact (@lem1982763 (real_of_int m) (term66 m) term72). Qed.
Lemma lem3176157 (m : int) : (term130 m) = (term71 m).
Proof. exact (@lem1982715 term72 (real_of_int m)). Qed.
Lemma lem3176159 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3176160 : term44 = term74.
Proof. exact (@lem3176159 term45). Qed.
Lemma lem3176162 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176163 : term72 = term77.
Proof. exact (@lem3176162 term45). Qed.
Lemma lem3176164 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176165 : term78 = term79.
Proof. exact (MK_COMB (@lem3176164) (@lem3176163)). Qed.
Lemma lem3176166 : term80 = term81.
Proof. exact (MK_COMB (@lem3176165) (@lem3176160)). Qed.
Lemma lem3176167 : term82.
Proof. exact (@lem1981473 term72 term44 term44 term44 term83 term44). Qed.
Lemma lem3176169 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176170 : term85 = term86.
Proof. exact (@lem3176169 (NUMERAL 0) term45). Qed.
Lemma lem3176171 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176172 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176173 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176172 h1) (fun h1 : term86 = True => @lem3176171)). Qed.
Lemma lem3176174 : term86 = True.
Proof. exact (EQ_MP (@lem3176173) (@lem3176171)). Qed.
Lemma lem3176175 : term85 = True.
Proof. exact (TRANS (@lem3176170) (@lem3176174)). Qed.
Lemma lem3176176 : True = term85.
Proof. exact (SYM (@lem3176175)). Qed.
Lemma lem3176177 : term85.
Proof. exact (EQ_MP (@lem3176176) (@lem0)). Qed.
Lemma lem3176178 : term88.
Proof. exact (@lem3176167 (@lem3176177)). Qed.
Lemma lem3176180 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176181 : term85 = term86.
Proof. exact (@lem3176180 (NUMERAL 0) term45). Qed.
Lemma lem3176182 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176183 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176184 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176183 h1) (fun h1 : term86 = True => @lem3176182)). Qed.
Lemma lem3176185 : term86 = True.
Proof. exact (EQ_MP (@lem3176184) (@lem3176182)). Qed.
Lemma lem3176186 : term85 = True.
Proof. exact (TRANS (@lem3176181) (@lem3176185)). Qed.
Lemma lem3176187 : True = term85.
Proof. exact (SYM (@lem3176186)). Qed.
Lemma lem3176188 : term85.
Proof. exact (EQ_MP (@lem3176187) (@lem0)). Qed.
Lemma lem3176189 : term89.
Proof. exact (@lem3176178 (@lem3176188)). Qed.
Lemma lem3176191 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176192 : term85 = term86.
Proof. exact (@lem3176191 (NUMERAL 0) term45). Qed.
Lemma lem3176193 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176194 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176195 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176194 h1) (fun h1 : term86 = True => @lem3176193)). Qed.
Lemma lem3176196 : term86 = True.
Proof. exact (EQ_MP (@lem3176195) (@lem3176193)). Qed.
Lemma lem3176197 : term85 = True.
Proof. exact (TRANS (@lem3176192) (@lem3176196)). Qed.
Lemma lem3176198 : True = term85.
Proof. exact (SYM (@lem3176197)). Qed.
Lemma lem3176199 : term85.
Proof. exact (EQ_MP (@lem3176198) (@lem0)). Qed.
Lemma lem3176200 : term90.
Proof. exact (@lem3176189 (@lem3176199)). Qed.
Lemma lem3176202 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176203 : term93 = term94.
Proof. exact (@lem3176202 term45 term45). Qed.
Lemma lem3176204 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176205 : term96 = term45.
Proof. exact (EQ_MP (@lem3176204) (@lem940073)). Qed.
Lemma lem3176206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176207 : term94 = term44.
Proof. exact (MK_COMB (@lem3176206) (@lem3176205)). Qed.
Lemma lem3176208 : term93 = term44.
Proof. exact (TRANS (@lem3176203) (@lem3176207)). Qed.
Lemma lem3176210 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3176211 : term99 = term100.
Proof. exact (@lem3176210 term45 term45). Qed.
Lemma lem3176212 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176213 : term96 = term45.
Proof. exact (EQ_MP (@lem3176212) (@lem940073)). Qed.
Lemma lem3176214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176215 : term94 = term44.
Proof. exact (MK_COMB (@lem3176214) (@lem3176213)). Qed.
Lemma lem3176216 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176217 : term100 = term72.
Proof. exact (MK_COMB (@lem3176216) (@lem3176215)). Qed.
Lemma lem3176218 : term99 = term72.
Proof. exact (TRANS (@lem3176211) (@lem3176217)). Qed.
Lemma lem3176219 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176220 : term101 = term78.
Proof. exact (MK_COMB (@lem3176219) (@lem3176218)). Qed.
Lemma lem3176221 : term102 = term80.
Proof. exact (MK_COMB (@lem3176220) (@lem3176208)). Qed.
Lemma lem3176223 (m : nat) : (term103 m) = term83.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3176224 : term80 = term83.
Proof. exact (@lem3176223 term45). Qed.
Lemma lem3176225 : term102 = term83.
Proof. exact (TRANS (@lem3176221) (@lem3176224)). Qed.
Lemma lem3176226 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176227 : term104 = term105.
Proof. exact (MK_COMB (@lem3176226) (@lem3176225)). Qed.
Lemma lem3176228 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3176229 : term106 = term107.
Proof. exact (MK_COMB (@lem3176227) (@lem3176228)). Qed.
Lemma lem3176231 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3176232 : term107 = term83.
Proof. exact (@lem3176231 term45). Qed.
Lemma lem3176233 : term106 = term83.
Proof. exact (TRANS (@lem3176229) (@lem3176232)). Qed.
Lemma lem3176235 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176236 : term93 = term94.
Proof. exact (@lem3176235 term45 term45). Qed.
Lemma lem3176237 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176238 : term96 = term45.
Proof. exact (EQ_MP (@lem3176237) (@lem940073)). Qed.
Lemma lem3176239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176240 : term94 = term44.
Proof. exact (MK_COMB (@lem3176239) (@lem3176238)). Qed.
Lemma lem3176241 : term93 = term44.
Proof. exact (TRANS (@lem3176236) (@lem3176240)). Qed.
Lemma lem3176242 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem3176243 : term109 = term107.
Proof. exact (MK_COMB (@lem3176242) (@lem3176241)). Qed.
Lemma lem3176245 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3176246 : term107 = term83.
Proof. exact (@lem3176245 term45). Qed.
Lemma lem3176247 : term109 = term83.
Proof. exact (TRANS (@lem3176243) (@lem3176246)). Qed.
Lemma lem3176248 : term83 = term109.
Proof. exact (SYM (@lem3176247)). Qed.
Lemma lem3176249 : term106 = term109.
Proof. exact (TRANS (@lem3176233) (@lem3176248)). Qed.
Lemma lem3176250 : term81 = term110.
Proof. exact (@lem3176200 (@lem3176249)). Qed.
Lemma lem3176251 : term80 = term110.
Proof. exact (TRANS (@lem3176166) (@lem3176250)). Qed.
Lemma lem3176253 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3176254 : term110 = term83.
Proof. exact (@lem3176253 term83). Qed.
Lemma lem3176255 : term80 = term83.
Proof. exact (TRANS (@lem3176251) (@lem3176254)). Qed.
Lemma lem3176256 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176257 : term112 = term105.
Proof. exact (MK_COMB (@lem3176256) (@lem3176255)). Qed.
Lemma lem3176258 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem3176259 (m : int) : (term71 m) = (term113 m).
Proof. exact (MK_COMB (@lem3176257) (@lem3176258 m)). Qed.
Lemma lem3176260 (m : int) : (term130 m) = (term113 m).
Proof. exact (TRANS (@lem3176157 m) (@lem3176259 m)). Qed.
Lemma lem3176261 (m : int) : (term113 m) = term83.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem3176262 (m : int) : (term130 m) = term83.
Proof. exact (TRANS (@lem3176260 m) (@lem3176261 m)). Qed.
Lemma lem3176263 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176264 (m : int) : (term131 m) = term132.
Proof. exact (MK_COMB (@lem3176263) (@lem3176262 m)). Qed.
Lemma lem3176265 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem3176266 (m : int) : (term129 m) = term133.
Proof. exact (MK_COMB (@lem3176264 m) (@lem3176265)). Qed.
Lemma lem3176267 (m : int) : (term128 m) = term133.
Proof. exact (TRANS (@lem3176156 m) (@lem3176266 m)). Qed.
Lemma lem3176268 : term133 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem3176269 (m : int) : (term128 m) = term72.
Proof. exact (TRANS (@lem3176267 m) (@lem3176268)). Qed.
Lemma lem3176270 (m : int) : (term118 m) = term72.
Proof. exact (TRANS (@lem3176155 m) (@lem3176269 m)). Qed.
Lemma lem3176271 (m : int) : (term117 m) = term72.
Proof. exact (TRANS (@lem3176110 m) (@lem3176270 m)). Qed.
Lemma lem3176272 (n : int) (m : int) : (term139 n m) = term72.
Proof. exact (TRANS (@lem3176109 n m) (@lem3176271 m)). Qed.
Lemma lem3176273 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3176274 (n : int) (m : int) : (term140 n m) = term135.
Proof. exact (MK_COMB (@lem3176273) (@lem3176272 n m)). Qed.
Lemma lem3176275 : term83 = term83.
Proof. exact (eq_refl term83). Qed.
Lemma lem3176276 (n : int) (m : int) : (term137 n m) = term136.
Proof. exact (MK_COMB (@lem3176274 n m) (@lem3176275)). Qed.
Lemma lem3176277 (n : int) (m : int) : (term61 n m) = term136.
Proof. exact (TRANS (@lem3175969 n m) (@lem3176276 n m)). Qed.
Lemma lem3176278 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3176279 (n : int) (m : int) : (term51 n m) = term141.
Proof. exact (MK_COMB (@lem3176278) (@lem3175968 n m)). Qed.
Lemma lem3176280 (n : int) (m : int) : (term62 n m) = term142.
Proof. exact (MK_COMB (@lem3176279 n m) (@lem3176277 n m)). Qed.
Lemma lem3176293 (n : int) (m : int) : (term64 n m) = term142.
Proof. exact (TRANS (@lem3175659 n m) (@lem3176280 n m)). Qed.
Lemma lem3176303 (h1 : term142) : term142.
Proof. exact (h1). Qed.
Lemma lem3176304 (h1 : term136) : term136.
Proof. exact (h1). Qed.
Lemma lem3176306 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3176307 : term136 = term143.
Proof. exact (@lem3176306 term83 term72). Qed.
Lemma lem3176309 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176310 : term72 = term77.
Proof. exact (@lem3176309 term45). Qed.
Lemma lem3176312 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3176313 : term83 = term110.
Proof. exact (@lem3176312 (NUMERAL 0)). Qed.
Lemma lem3176314 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3176315 : term144 = term145.
Proof. exact (MK_COMB (@lem3176314) (@lem3176313)). Qed.
Lemma lem3176316 : term143 = term146.
Proof. exact (MK_COMB (@lem3176315) (@lem3176310)). Qed.
Lemma lem3176317 : term147.
Proof. exact (@lem1980026 term83 term44 term72 term44). Qed.
Lemma lem3176319 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176320 : term85 = term86.
Proof. exact (@lem3176319 (NUMERAL 0) term45). Qed.
Lemma lem3176321 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176322 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176323 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176322 h1) (fun h1 : term86 = True => @lem3176321)). Qed.
Lemma lem3176324 : term86 = True.
Proof. exact (EQ_MP (@lem3176323) (@lem3176321)). Qed.
Lemma lem3176325 : term85 = True.
Proof. exact (TRANS (@lem3176320) (@lem3176324)). Qed.
Lemma lem3176326 : True = term85.
Proof. exact (SYM (@lem3176325)). Qed.
Lemma lem3176327 : term85.
Proof. exact (EQ_MP (@lem3176326) (@lem0)). Qed.
Lemma lem3176328 : term148.
Proof. exact (@lem3176317 (@lem3176327)). Qed.
Lemma lem3176330 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176331 : term85 = term86.
Proof. exact (@lem3176330 (NUMERAL 0) term45). Qed.
Lemma lem3176332 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176333 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176334 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176333 h1) (fun h1 : term86 = True => @lem3176332)). Qed.
Lemma lem3176335 : term86 = True.
Proof. exact (EQ_MP (@lem3176334) (@lem3176332)). Qed.
Lemma lem3176336 : term85 = True.
Proof. exact (TRANS (@lem3176331) (@lem3176335)). Qed.
Lemma lem3176337 : True = term85.
Proof. exact (SYM (@lem3176336)). Qed.
Lemma lem3176338 : term85.
Proof. exact (EQ_MP (@lem3176337) (@lem0)). Qed.
Lemma lem3176339 : term146 = term149.
Proof. exact (@lem3176328 (@lem3176338)). Qed.
Lemma lem3176341 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3176342 : term99 = term100.
Proof. exact (@lem3176341 term45 term45). Qed.
Lemma lem3176343 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176344 : term96 = term45.
Proof. exact (EQ_MP (@lem3176343) (@lem940073)). Qed.
Lemma lem3176345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176346 : term94 = term44.
Proof. exact (MK_COMB (@lem3176345) (@lem3176344)). Qed.
Lemma lem3176347 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176348 : term100 = term72.
Proof. exact (MK_COMB (@lem3176347) (@lem3176346)). Qed.
Lemma lem3176349 : term99 = term72.
Proof. exact (TRANS (@lem3176342) (@lem3176348)). Qed.
Lemma lem3176351 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3176352 : term107 = term83.
Proof. exact (@lem3176351 term45). Qed.
Lemma lem3176353 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3176354 : term150 = term144.
Proof. exact (MK_COMB (@lem3176353) (@lem3176352)). Qed.
Lemma lem3176355 : term149 = term143.
Proof. exact (MK_COMB (@lem3176354) (@lem3176349)). Qed.
Lemma lem3176357 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3176358 : term143 = term153.
Proof. exact (@lem3176357 (NUMERAL 0) term45). Qed.
Lemma lem3176359 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176360 (h1 : term87 = (BIT1 0)) : (term45 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3176361 : (term87 = (BIT1 0)) = ((term45 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176360 h1) (fun h1 : (term45 = (NUMERAL 0)) = False => @lem3176359)). Qed.
Lemma lem3176362 : (term45 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3176361) (@lem3176359)). Qed.
Lemma lem3176363 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3176364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3176365 : term154 = (and True).
Proof. exact (MK_COMB (@lem3176364) (@lem3176363)). Qed.
Lemma lem3176366 : term153 = (True /\ False).
Proof. exact (MK_COMB (@lem3176365) (@lem3176362)). Qed.
Lemma lem3176368 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3176369 : term153 = False.
Proof. exact (TRANS (@lem3176366) (@lem3176368)). Qed.
Lemma lem3176370 : term143 = False.
Proof. exact (TRANS (@lem3176358) (@lem3176369)). Qed.
Lemma lem3176371 : term149 = False.
Proof. exact (TRANS (@lem3176355) (@lem3176370)). Qed.
Lemma lem3176372 : term146 = False.
Proof. exact (TRANS (@lem3176339) (@lem3176371)). Qed.
Lemma lem3176373 : term143 = False.
Proof. exact (TRANS (@lem3176316) (@lem3176372)). Qed.
Lemma lem3176374 : term136 = False.
Proof. exact (TRANS (@lem3176307) (@lem3176373)). Qed.
Lemma lem3176375 (h1 : term136) : False.
Proof. exact (EQ_MP (@lem3176374) (@lem3176304 h1)). Qed.
Lemma lem3176376 (h1 : term136) : term136.
Proof. exact (h1). Qed.
Lemma lem3176378 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3176379 : term136 = term143.
Proof. exact (@lem3176378 term83 term72). Qed.
Lemma lem3176381 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176382 : term72 = term77.
Proof. exact (@lem3176381 term45). Qed.
Lemma lem3176384 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3176385 : term83 = term110.
Proof. exact (@lem3176384 (NUMERAL 0)). Qed.
Lemma lem3176386 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3176387 : term144 = term145.
Proof. exact (MK_COMB (@lem3176386) (@lem3176385)). Qed.
Lemma lem3176388 : term143 = term146.
Proof. exact (MK_COMB (@lem3176387) (@lem3176382)). Qed.
Lemma lem3176389 : term147.
Proof. exact (@lem1980026 term83 term44 term72 term44). Qed.
Lemma lem3176391 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176392 : term85 = term86.
Proof. exact (@lem3176391 (NUMERAL 0) term45). Qed.
Lemma lem3176393 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176394 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176395 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176394 h1) (fun h1 : term86 = True => @lem3176393)). Qed.
Lemma lem3176396 : term86 = True.
Proof. exact (EQ_MP (@lem3176395) (@lem3176393)). Qed.
Lemma lem3176397 : term85 = True.
Proof. exact (TRANS (@lem3176392) (@lem3176396)). Qed.
Lemma lem3176398 : True = term85.
Proof. exact (SYM (@lem3176397)). Qed.
Lemma lem3176399 : term85.
Proof. exact (EQ_MP (@lem3176398) (@lem0)). Qed.
Lemma lem3176400 : term148.
Proof. exact (@lem3176389 (@lem3176399)). Qed.
Lemma lem3176402 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176403 : term85 = term86.
Proof. exact (@lem3176402 (NUMERAL 0) term45). Qed.
Lemma lem3176404 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176405 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176406 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176405 h1) (fun h1 : term86 = True => @lem3176404)). Qed.
Lemma lem3176407 : term86 = True.
Proof. exact (EQ_MP (@lem3176406) (@lem3176404)). Qed.
Lemma lem3176408 : term85 = True.
Proof. exact (TRANS (@lem3176403) (@lem3176407)). Qed.
Lemma lem3176409 : True = term85.
Proof. exact (SYM (@lem3176408)). Qed.
Lemma lem3176410 : term85.
Proof. exact (EQ_MP (@lem3176409) (@lem0)). Qed.
Lemma lem3176411 : term146 = term149.
Proof. exact (@lem3176400 (@lem3176410)). Qed.
Lemma lem3176413 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3176414 : term99 = term100.
Proof. exact (@lem3176413 term45 term45). Qed.
Lemma lem3176415 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176416 : term96 = term45.
Proof. exact (EQ_MP (@lem3176415) (@lem940073)). Qed.
Lemma lem3176417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176418 : term94 = term44.
Proof. exact (MK_COMB (@lem3176417) (@lem3176416)). Qed.
Lemma lem3176419 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176420 : term100 = term72.
Proof. exact (MK_COMB (@lem3176419) (@lem3176418)). Qed.
Lemma lem3176421 : term99 = term72.
Proof. exact (TRANS (@lem3176414) (@lem3176420)). Qed.
Lemma lem3176423 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3176424 : term107 = term83.
Proof. exact (@lem3176423 term45). Qed.
Lemma lem3176425 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3176426 : term150 = term144.
Proof. exact (MK_COMB (@lem3176425) (@lem3176424)). Qed.
Lemma lem3176427 : term149 = term143.
Proof. exact (MK_COMB (@lem3176426) (@lem3176421)). Qed.
Lemma lem3176429 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3176430 : term143 = term153.
Proof. exact (@lem3176429 (NUMERAL 0) term45). Qed.
Lemma lem3176431 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176432 (h1 : term87 = (BIT1 0)) : (term45 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3176433 : (term87 = (BIT1 0)) = ((term45 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176432 h1) (fun h1 : (term45 = (NUMERAL 0)) = False => @lem3176431)). Qed.
Lemma lem3176434 : (term45 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3176433) (@lem3176431)). Qed.
Lemma lem3176435 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3176436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3176437 : term154 = (and True).
Proof. exact (MK_COMB (@lem3176436) (@lem3176435)). Qed.
Lemma lem3176438 : term153 = (True /\ False).
Proof. exact (MK_COMB (@lem3176437) (@lem3176434)). Qed.
Lemma lem3176440 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3176441 : term153 = False.
Proof. exact (TRANS (@lem3176438) (@lem3176440)). Qed.
Lemma lem3176442 : term143 = False.
Proof. exact (TRANS (@lem3176430) (@lem3176441)). Qed.
Lemma lem3176443 : term149 = False.
Proof. exact (TRANS (@lem3176427) (@lem3176442)). Qed.
Lemma lem3176444 : term146 = False.
Proof. exact (TRANS (@lem3176411) (@lem3176443)). Qed.
Lemma lem3176445 : term143 = False.
Proof. exact (TRANS (@lem3176388) (@lem3176444)). Qed.
Lemma lem3176446 : term136 = False.
Proof. exact (TRANS (@lem3176379) (@lem3176445)). Qed.
Lemma lem3176447 (h1 : term136) : False.
Proof. exact (EQ_MP (@lem3176446) (@lem3176376 h1)). Qed.
Lemma lem3176448 (h1 : term142) : False.
Proof. exact (or_elim (@lem3176303 h1) (fun h0 : term136 => @lem3176375 h0) (fun h0 : term136 => @lem3176447 h0)). Qed.
Lemma lem3176450 (h1 : term142) : term142.
Proof. exact (h1). Qed.
Lemma lem3176451 (h1 : term142) : term142 = False.
Proof. exact (prop_ext (fun h2 : term142 => @lem3176448 h1) (fun h2 : False => @lem3176450 h1)). Qed.
Lemma lem3176452 (h1 : term142) : False.
Proof. exact (EQ_MP (@lem3176451 h1) (@lem3176450 h1)). Qed.
Lemma lem3176453 (n : int) (m : int) (h1 : term64 n m) : term64 n m.
Proof. exact (h1). Qed.
Lemma lem3176454 (n : int) (m : int) (h1 : term64 n m) : term142.
Proof. exact (EQ_MP (@lem3176293 n m) (@lem3176453 n m h1)). Qed.
Lemma lem3176455 (n : int) (m : int) (h1 : term64 n m) : term142 = False.
Proof. exact (prop_ext (fun h2 : term142 => @lem3176452 h2) (fun h2 : False => @lem3176454 n m h1)). Qed.
Lemma lem3176456 (n : int) (m : int) (h1 : term64 n m) : False.
Proof. exact (EQ_MP (@lem3176455 n m h1) (@lem3176454 n m h1)). Qed.
Lemma lem3176457 (n : int) (m : int) : term155 n m.
Proof. exact (fun h0 : term64 n m => @lem3176456 n m h0). Qed.
Lemma lem3176458 (n : int) (m : int) : term156 n m.
Proof. exact (@lem1386578 (term157 n m)). Qed.
Lemma lem3176461 (n : int) (m : int) : term157 n m.
Proof. exact (@lem3176458 n m (@lem3176457 n m)). Qed.
Lemma lem3176462 (n : int) (m : int) : (term62 n m) = (term22 n m).
Proof. exact (SYM (@lem3175639 n m)). Qed.
Lemma lem3176463 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3176464 (n : int) (m : int) : (term157 n m) = (term18 n m).
Proof. exact (MK_COMB (@lem3176463) (@lem3176462 n m)). Qed.
Lemma lem3176465 (n : int) (m : int) : term18 n m.
Proof. exact (EQ_MP (@lem3176464 n m) (@lem3176461 n m)). Qed.
Lemma lem3176471 (m : nat) (n : nat) (h1 : (term158 m n) = (term159 m n)) : (term158 m n) = (term159 m n).
Proof. exact (h1). Qed.
Lemma lem3176472 (m : nat) (n : nat) (h1 : (term158 m n) = (term159 m n)) : (term159 m n) = (term158 m n).
Proof. exact (SYM (@lem3176471 m n h1)). Qed.
Lemma lem3176473 (m : nat) (n : nat) (h1 : (term159 m n) = (term158 m n)) : (term159 m n) = (term158 m n).
Proof. exact (h1). Qed.
Lemma lem3176474 (m : nat) (n : nat) (h1 : (term159 m n) = (term158 m n)) : (term158 m n) = (term159 m n).
Proof. exact (SYM (@lem3176473 m n h1)). Qed.
Lemma lem3176475 (m : nat) (n : nat) : ((term158 m n) = (term159 m n)) = ((term159 m n) = (term158 m n)).
Proof. exact (prop_ext (fun h1 : (term158 m n) = (term159 m n) => @lem3176472 m n h1) (fun h1 : (term159 m n) = (term158 m n) => @lem3176474 m n h1)). Qed.
Lemma lem3176476 (m : nat) : (term160 m) = (term161 m).
Proof. exact (fun_ext (fun n : nat => @lem3176475 m n)). Qed.
Lemma lem3176477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3176478 (m : nat) : (term162 m) = (term163 m).
Proof. exact (MK_COMB (@lem3176477) (@lem3176476 m)). Qed.
Lemma lem3176479 : term164 = term165.
Proof. exact (fun_ext (fun m : nat => @lem3176478 m)). Qed.
Lemma lem3176480 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3176481 : term166 = term167.
Proof. exact (MK_COMB (@lem3176480) (@lem3176479)). Qed.
Lemma lem3176482 : term167.
Proof. exact (EQ_MP (@lem3176481) (@lem2306816)). Qed.
Lemma lem3176483 (m : nat) : term168 m.
Proof. exact (@lem3176482 m). Qed.
Lemma lem3176484 (m : nat) : (term168 m) = (term163 m).
Proof. exact (eq_refl (term168 m)). Qed.
Lemma lem3176485 (m : nat) : term163 m.
Proof. exact (EQ_MP (@lem3176484 m) (@lem3176483 m)). Qed.
Lemma lem3176486 (m : nat) (n : nat) : term169 m n.
Proof. exact (@lem3176485 m n). Qed.
Lemma lem3176487 (m : nat) (n : nat) : (term169 m n) = ((term159 m n) = (term158 m n)).
Proof. exact (eq_refl (term169 m n)). Qed.
Lemma lem3176489 {A : Type'} (P : A -> Prop) : term170 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem3176490 {A : Type'} (P : A -> Prop) : (term170 A P) = (term171 A P).
Proof. exact (eq_refl (term170 A P)). Qed.
Lemma lem3176491 {A : Type'} (P : A -> Prop) : term171 A P.
Proof. exact (EQ_MP (@lem3176490 A P) (@lem3176489 A P)). Qed.
Lemma lem3176492 {A : Type'} (P : A -> Prop) (Q : Prop) : term172 A P Q.
Proof. exact (@lem3176491 A P Q). Qed.
Lemma lem3176493 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = ((term173 A P Q) = (term174 A P Q)).
Proof. exact (eq_refl (term172 A P Q)). Qed.
Lemma lem3176495 (m : nat) : term175 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem3176496 (m : nat) : (term175 m) = (term176 m).
Proof. exact (eq_refl (term175 m)). Qed.
Lemma lem3176497 (m : nat) : term176 m.
Proof. exact (EQ_MP (@lem3176496 m) (@lem3176495 m)). Qed.
Lemma lem3176498 (m : nat) (n : nat) : term177 m n.
Proof. exact (@lem3176497 m n). Qed.
Lemma lem3176499 (n : nat) (m : nat) : (term177 m n) = ((Peano.le m n) = (term178 n m)).
Proof. exact (eq_refl (term177 m n)). Qed.
Lemma lem3176505 (y : int) (x : int) : (term179 y x) = ((term180 x y) = (term181 y x)).
Proof. exact (@lem2954598 ((term180 x y) = (term181 y x))). Qed.
Lemma lem3176524 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem3176525 (x : int) (y : int) : (term182 y x) = (term183 x y).
Proof. exact (@lem3176524 (term181 y x) (term180 x y)). Qed.
Lemma lem3176527 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3176528 (y : int) (x : int) : (term184 y x) = (term185 y x).
Proof. exact (@lem3176527 (term186 x y) (term181 y x)). Qed.
Lemma lem3176530 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3176531 (x : int) (y : int) : (term187 x y) = (term188 x y).
Proof. exact (@lem3176530 (term180 x y) term32). Qed.
Lemma lem3176533 (x : int) : (term35 x) = (term36 x).
Proof. exact (EQ_MP (@lem2841589 x) (@lem2841588 x)). Qed.
Lemma lem3176534 (x : int) (y : int) : (term189 x y) = (term190 x y).
Proof. exact (@lem3176533 (term181 x y)). Qed.
Lemma lem3176536 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3176537 (x : int) (y : int) : (term191 x y) = (term192 x y).
Proof. exact (@lem3176536 (int_neg x) y). Qed.
Lemma lem3176539 (x : int) : (term35 x) = (term36 x).
Proof. exact (EQ_MP (@lem2841589 x) (@lem2841588 x)). Qed.
Lemma lem3176540 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176541 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem3176540) (@lem3176539 x)). Qed.
Lemma lem3176542 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3176543 (x : int) (y : int) : (term192 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem3176541 x) (@lem3176542 y)). Qed.
Lemma lem3176544 (x : int) (y : int) : (term191 x y) = (term193 x y).
Proof. exact (TRANS (@lem3176537 x y) (@lem3176543 x y)). Qed.
Lemma lem3176545 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176546 (x : int) (y : int) : (term190 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem3176545) (@lem3176544 x y)). Qed.
Lemma lem3176547 (x : int) (y : int) : (term189 x y) = (term194 x y).
Proof. exact (TRANS (@lem3176534 x y) (@lem3176546 x y)). Qed.
Lemma lem3176548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176549 (x : int) (y : int) : (term195 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem3176548) (@lem3176547 x y)). Qed.
Lemma lem3176551 (n : nat) : (term42 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3176552 : term43 = term44.
Proof. exact (@lem3176551 term45). Qed.
Lemma lem3176553 (x : int) (y : int) : (term188 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem3176549 x y) (@lem3176552)). Qed.
Lemma lem3176554 (x : int) (y : int) : (term187 x y) = (term197 x y).
Proof. exact (TRANS (@lem3176531 x y) (@lem3176553 x y)). Qed.
Lemma lem3176555 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3176556 (x : int) (y : int) : (term198 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem3176555) (@lem3176554 x y)). Qed.
Lemma lem3176558 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3176559 (y : int) (x : int) : (term191 y x) = (term192 y x).
Proof. exact (@lem3176558 (int_neg y) x). Qed.
Lemma lem3176561 (x : int) : (term35 x) = (term36 x).
Proof. exact (EQ_MP (@lem2841589 x) (@lem2841588 x)). Qed.
Lemma lem3176562 (y : int) : (term35 y) = (term36 y).
Proof. exact (@lem3176561 y). Qed.
Lemma lem3176563 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176564 (y : int) : (term37 y) = (term38 y).
Proof. exact (MK_COMB (@lem3176563) (@lem3176562 y)). Qed.
Lemma lem3176565 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3176566 (y : int) (x : int) : (term192 y x) = (term193 y x).
Proof. exact (MK_COMB (@lem3176564 y) (@lem3176565 x)). Qed.
Lemma lem3176567 (y : int) (x : int) : (term191 y x) = (term193 y x).
Proof. exact (TRANS (@lem3176559 y x) (@lem3176566 y x)). Qed.
Lemma lem3176568 (y : int) (x : int) : (term185 y x) = (term200 y x).
Proof. exact (MK_COMB (@lem3176556 x y) (@lem3176567 y x)). Qed.
Lemma lem3176569 (y : int) (x : int) : (term184 y x) = (term200 y x).
Proof. exact (TRANS (@lem3176528 y x) (@lem3176568 y x)). Qed.
Lemma lem3176570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3176571 (y : int) (x : int) : (term201 y x) = (term202 y x).
Proof. exact (MK_COMB (@lem3176570) (@lem3176569 y x)). Qed.
Lemma lem3176573 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3176574 (x : int) (y : int) : (term203 x y) = (term204 x y).
Proof. exact (@lem3176573 (term205 y x) (term180 x y)). Qed.
Lemma lem3176576 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3176577 (y : int) (x : int) : (term206 y x) = (term207 y x).
Proof. exact (@lem3176576 (term181 y x) term32). Qed.
Lemma lem3176579 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3176580 (y : int) (x : int) : (term191 y x) = (term192 y x).
Proof. exact (@lem3176579 (int_neg y) x). Qed.
Lemma lem3176582 (x : int) : (term35 x) = (term36 x).
Proof. exact (EQ_MP (@lem2841589 x) (@lem2841588 x)). Qed.
Lemma lem3176583 (y : int) : (term35 y) = (term36 y).
Proof. exact (@lem3176582 y). Qed.
Lemma lem3176584 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176585 (y : int) : (term37 y) = (term38 y).
Proof. exact (MK_COMB (@lem3176584) (@lem3176583 y)). Qed.
Lemma lem3176586 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3176587 (y : int) (x : int) : (term192 y x) = (term193 y x).
Proof. exact (MK_COMB (@lem3176585 y) (@lem3176586 x)). Qed.
Lemma lem3176588 (y : int) (x : int) : (term191 y x) = (term193 y x).
Proof. exact (TRANS (@lem3176580 y x) (@lem3176587 y x)). Qed.
Lemma lem3176589 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176590 (y : int) (x : int) : (term208 y x) = (term209 y x).
Proof. exact (MK_COMB (@lem3176589) (@lem3176588 y x)). Qed.
Lemma lem3176592 (n : nat) : (term42 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3176593 : term43 = term44.
Proof. exact (@lem3176592 term45). Qed.
Lemma lem3176594 (y : int) (x : int) : (term207 y x) = (term210 y x).
Proof. exact (MK_COMB (@lem3176590 y x) (@lem3176593)). Qed.
Lemma lem3176595 (y : int) (x : int) : (term206 y x) = (term210 y x).
Proof. exact (TRANS (@lem3176577 y x) (@lem3176594 y x)). Qed.
Lemma lem3176596 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3176597 (y : int) (x : int) : (term211 y x) = (term212 y x).
Proof. exact (MK_COMB (@lem3176596) (@lem3176595 y x)). Qed.
Lemma lem3176599 (x : int) : (term35 x) = (term36 x).
Proof. exact (EQ_MP (@lem2841589 x) (@lem2841588 x)). Qed.
Lemma lem3176600 (x : int) (y : int) : (term189 x y) = (term190 x y).
Proof. exact (@lem3176599 (term181 x y)). Qed.
Lemma lem3176602 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3176603 (x : int) (y : int) : (term191 x y) = (term192 x y).
Proof. exact (@lem3176602 (int_neg x) y). Qed.
Lemma lem3176605 (x : int) : (term35 x) = (term36 x).
Proof. exact (EQ_MP (@lem2841589 x) (@lem2841588 x)). Qed.
Lemma lem3176606 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176607 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem3176606) (@lem3176605 x)). Qed.
Lemma lem3176608 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3176609 (x : int) (y : int) : (term192 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem3176607 x) (@lem3176608 y)). Qed.
Lemma lem3176610 (x : int) (y : int) : (term191 x y) = (term193 x y).
Proof. exact (TRANS (@lem3176603 x y) (@lem3176609 x y)). Qed.
Lemma lem3176611 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176612 (x : int) (y : int) : (term190 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem3176611) (@lem3176610 x y)). Qed.
Lemma lem3176613 (x : int) (y : int) : (term189 x y) = (term194 x y).
Proof. exact (TRANS (@lem3176600 x y) (@lem3176612 x y)). Qed.
Lemma lem3176614 (x : int) (y : int) : (term204 x y) = (term213 x y).
Proof. exact (MK_COMB (@lem3176597 y x) (@lem3176613 x y)). Qed.
Lemma lem3176615 (x : int) (y : int) : (term203 x y) = (term213 x y).
Proof. exact (TRANS (@lem3176574 x y) (@lem3176614 x y)). Qed.
Lemma lem3176616 (x : int) (y : int) : (term183 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem3176571 y x) (@lem3176615 x y)). Qed.
Lemma lem3176618 (x : int) (y : int) : (term182 y x) = (term214 x y).
Proof. exact (TRANS (@lem3176525 x y) (@lem3176616 x y)). Qed.
Lemma lem3176622 (t : Prop) : (term63 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3176638 (x : int) (y : int) : (term215 x y) = (term214 x y).
Proof. exact (@lem3176622 (term214 x y)). Qed.
Lemma lem3176639 (x : int) (y : int) : (term200 y x) = (term216 x y).
Proof. exact (@lem1988287 (term193 y x) (term197 x y)). Qed.
Lemma lem3176640 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3176641 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3176648 (x : int) : (term36 x) = (term66 x).
Proof. exact (@lem1982785 (real_of_int x)). Qed.
Lemma lem3176649 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176650 (x : int) : (term38 x) = (term67 x).
Proof. exact (MK_COMB (@lem3176649) (@lem3176648 x)). Qed.
Lemma lem3176653 (x : int) (y : int) : (term193 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem3176650 x) (@lem3176641 y)). Qed.
Lemma lem3176654 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176655 (x : int) (y : int) : (term194 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem3176654) (@lem3176653 x y)). Qed.
Lemma lem3176656 (x : int) (y : int) : (term218 x y) = (term219 x y).
Proof. exact (@lem1982785 (term217 x y)). Qed.
Lemma lem3176657 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (@lem1982781 (term66 x) term72 (real_of_int y)). Qed.
Lemma lem3176658 (y : int) : (term66 y) = (term66 y).
Proof. exact (eq_refl (term66 y)). Qed.
Lemma lem3176659 (x : int) : (term221 x) = (term222 x).
Proof. exact (@lem1982749 term72 term72 (real_of_int x)). Qed.
Lemma lem3176661 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176662 : term72 = term77.
Proof. exact (@lem3176661 term45). Qed.
Lemma lem3176664 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176665 : term72 = term77.
Proof. exact (@lem3176664 term45). Qed.
Lemma lem3176666 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176667 : term121 = term122.
Proof. exact (MK_COMB (@lem3176666) (@lem3176665)). Qed.
Lemma lem3176668 : term223 = term224.
Proof. exact (MK_COMB (@lem3176667) (@lem3176662)). Qed.
Lemma lem3176669 : term224 = term225.
Proof. exact (@lem1981613 term72 term72 term44 term44). Qed.
Lemma lem3176671 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176672 : term93 = term94.
Proof. exact (@lem3176671 term45 term45). Qed.
Lemma lem3176673 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176674 : term96 = term45.
Proof. exact (EQ_MP (@lem3176673) (@lem940073)). Qed.
Lemma lem3176675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176676 : term94 = term44.
Proof. exact (MK_COMB (@lem3176675) (@lem3176674)). Qed.
Lemma lem3176677 : term93 = term44.
Proof. exact (TRANS (@lem3176672) (@lem3176676)). Qed.
Lemma lem3176679 (m : nat) (n : nat) : (term226 m n) = (term92 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3176680 : term223 = term94.
Proof. exact (@lem3176679 term45 term45). Qed.
Lemma lem3176681 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176682 : term96 = term45.
Proof. exact (EQ_MP (@lem3176681) (@lem940073)). Qed.
Lemma lem3176683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176684 : term94 = term44.
Proof. exact (MK_COMB (@lem3176683) (@lem3176682)). Qed.
Lemma lem3176685 : term223 = term44.
Proof. exact (TRANS (@lem3176680) (@lem3176684)). Qed.
Lemma lem3176686 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3176687 : term227 = term228.
Proof. exact (MK_COMB (@lem3176686) (@lem3176685)). Qed.
Lemma lem3176688 : term225 = term74.
Proof. exact (MK_COMB (@lem3176687) (@lem3176677)). Qed.
Lemma lem3176689 : term224 = term74.
Proof. exact (TRANS (@lem3176669) (@lem3176688)). Qed.
Lemma lem3176690 : term223 = term74.
Proof. exact (TRANS (@lem3176668) (@lem3176689)). Qed.
Lemma lem3176692 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3176693 : term74 = term44.
Proof. exact (@lem3176692 term44). Qed.
Lemma lem3176694 : term223 = term44.
Proof. exact (TRANS (@lem3176690) (@lem3176693)). Qed.
Lemma lem3176695 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176696 : term229 = term230.
Proof. exact (MK_COMB (@lem3176695) (@lem3176694)). Qed.
Lemma lem3176697 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3176698 (x : int) : (term222 x) = (term231 x).
Proof. exact (MK_COMB (@lem3176696) (@lem3176697 x)). Qed.
Lemma lem3176699 (x : int) : (term221 x) = (term231 x).
Proof. exact (TRANS (@lem3176659 x) (@lem3176698 x)). Qed.
Lemma lem3176700 (x : int) : (term231 x) = (real_of_int x).
Proof. exact (@lem1982709 (real_of_int x)). Qed.
Lemma lem3176701 (x : int) : (term221 x) = (real_of_int x).
Proof. exact (TRANS (@lem3176699 x) (@lem3176700 x)). Qed.
Lemma lem3176702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176703 (x : int) : (term232 x) = (term57 x).
Proof. exact (MK_COMB (@lem3176702) (@lem3176701 x)). Qed.
Lemma lem3176704 (x : int) (y : int) : (term220 x y) = (term233 x y).
Proof. exact (MK_COMB (@lem3176703 x) (@lem3176658 y)). Qed.
Lemma lem3176705 (x : int) (y : int) : (term219 x y) = (term233 x y).
Proof. exact (TRANS (@lem3176657 x y) (@lem3176704 x y)). Qed.
Lemma lem3176706 (x : int) (y : int) : (term218 x y) = (term233 x y).
Proof. exact (TRANS (@lem3176656 x y) (@lem3176705 x y)). Qed.
Lemma lem3176707 (x : int) (y : int) : (term194 x y) = (term233 x y).
Proof. exact (TRANS (@lem3176655 x y) (@lem3176706 x y)). Qed.
Lemma lem3176708 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176709 (x : int) (y : int) : (term196 x y) = (term234 x y).
Proof. exact (MK_COMB (@lem3176708) (@lem3176707 x y)). Qed.
Lemma lem3176710 (x : int) (y : int) : (term197 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem3176709 x y) (@lem3176640)). Qed.
Lemma lem3176715 (x : int) (y : int) : (term235 x y) = (term236 x y).
Proof. exact (@lem1982755 (real_of_int x) (term66 y) term44). Qed.
Lemma lem3176716 (x : int) (y : int) : (term197 x y) = (term236 x y).
Proof. exact (TRANS (@lem3176710 x y) (@lem3176715 x y)). Qed.
Lemma lem3176717 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3176724 (y : int) : (term36 y) = (term66 y).
Proof. exact (@lem1982785 (real_of_int y)). Qed.
Lemma lem3176725 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176726 (y : int) : (term38 y) = (term67 y).
Proof. exact (MK_COMB (@lem3176725) (@lem3176724 y)). Qed.
Lemma lem3176727 (y : int) (x : int) : (term193 y x) = (term217 y x).
Proof. exact (MK_COMB (@lem3176726 y) (@lem3176717 x)). Qed.
Lemma lem3176728 (x : int) (y : int) : (term217 y x) = (term233 x y).
Proof. exact (@lem1982761 (real_of_int x) (term66 y)). Qed.
Lemma lem3176729 (x : int) (y : int) : (term193 y x) = (term233 x y).
Proof. exact (TRANS (@lem3176727 y x) (@lem3176728 x y)). Qed.
Lemma lem3176730 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem3176731 (x : int) (y : int) : (term237 y x) = (term238 x y).
Proof. exact (MK_COMB (@lem3176730) (@lem3176729 x y)). Qed.
Lemma lem3176732 (x : int) (y : int) : (term239 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem3176731 x y) (@lem3176716 x y)). Qed.
Lemma lem3176733 (x : int) (y : int) : (term240 x y) = (term241 x y).
Proof. exact (@lem1982792 (term233 x y) (term236 x y)). Qed.
Lemma lem3176734 (x : int) (y : int) : (term242 x y) = (term243 x y).
Proof. exact (@lem1982781 (real_of_int x) term72 (term244 y)). Qed.
Lemma lem3176735 (y : int) : (term245 y) = (term246 y).
Proof. exact (@lem1982781 (term66 y) term72 term44). Qed.
Lemma lem3176737 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3176738 : term44 = term74.
Proof. exact (@lem3176737 term45). Qed.
Lemma lem3176740 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176741 : term72 = term77.
Proof. exact (@lem3176740 term45). Qed.
Lemma lem3176742 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176743 : term121 = term122.
Proof. exact (MK_COMB (@lem3176742) (@lem3176741)). Qed.
Lemma lem3176744 : term99 = term123.
Proof. exact (MK_COMB (@lem3176743) (@lem3176738)). Qed.
Lemma lem3176745 : term123 = term124.
Proof. exact (@lem1981613 term72 term44 term44 term44). Qed.
Lemma lem3176747 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176748 : term93 = term94.
Proof. exact (@lem3176747 term45 term45). Qed.
Lemma lem3176749 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176750 : term96 = term45.
Proof. exact (EQ_MP (@lem3176749) (@lem940073)). Qed.
Lemma lem3176751 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176752 : term94 = term44.
Proof. exact (MK_COMB (@lem3176751) (@lem3176750)). Qed.
Lemma lem3176753 : term93 = term44.
Proof. exact (TRANS (@lem3176748) (@lem3176752)). Qed.
Lemma lem3176755 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3176756 : term99 = term100.
Proof. exact (@lem3176755 term45 term45). Qed.
Lemma lem3176757 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176758 : term96 = term45.
Proof. exact (EQ_MP (@lem3176757) (@lem940073)). Qed.
Lemma lem3176759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176760 : term94 = term44.
Proof. exact (MK_COMB (@lem3176759) (@lem3176758)). Qed.
Lemma lem3176761 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176762 : term100 = term72.
Proof. exact (MK_COMB (@lem3176761) (@lem3176760)). Qed.
Lemma lem3176763 : term99 = term72.
Proof. exact (TRANS (@lem3176756) (@lem3176762)). Qed.
Lemma lem3176764 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3176765 : term125 = term126.
Proof. exact (MK_COMB (@lem3176764) (@lem3176763)). Qed.
Lemma lem3176766 : term124 = term77.
Proof. exact (MK_COMB (@lem3176765) (@lem3176753)). Qed.
Lemma lem3176767 : term123 = term77.
Proof. exact (TRANS (@lem3176745) (@lem3176766)). Qed.
Lemma lem3176768 : term99 = term77.
Proof. exact (TRANS (@lem3176744) (@lem3176767)). Qed.
Lemma lem3176770 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3176771 : term77 = term72.
Proof. exact (@lem3176770 term72). Qed.
Lemma lem3176772 : term99 = term72.
Proof. exact (TRANS (@lem3176768) (@lem3176771)). Qed.
Lemma lem3176773 (y : int) : (term221 y) = (term222 y).
Proof. exact (@lem1982749 term72 term72 (real_of_int y)). Qed.
Lemma lem3176775 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176776 : term72 = term77.
Proof. exact (@lem3176775 term45). Qed.
Lemma lem3176778 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176779 : term72 = term77.
Proof. exact (@lem3176778 term45). Qed.
Lemma lem3176780 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176781 : term121 = term122.
Proof. exact (MK_COMB (@lem3176780) (@lem3176779)). Qed.
Lemma lem3176782 : term223 = term224.
Proof. exact (MK_COMB (@lem3176781) (@lem3176776)). Qed.
Lemma lem3176783 : term224 = term225.
Proof. exact (@lem1981613 term72 term72 term44 term44). Qed.
Lemma lem3176785 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176786 : term93 = term94.
Proof. exact (@lem3176785 term45 term45). Qed.
Lemma lem3176787 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176788 : term96 = term45.
Proof. exact (EQ_MP (@lem3176787) (@lem940073)). Qed.
Lemma lem3176789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176790 : term94 = term44.
Proof. exact (MK_COMB (@lem3176789) (@lem3176788)). Qed.
Lemma lem3176791 : term93 = term44.
Proof. exact (TRANS (@lem3176786) (@lem3176790)). Qed.
Lemma lem3176793 (m : nat) (n : nat) : (term226 m n) = (term92 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3176794 : term223 = term94.
Proof. exact (@lem3176793 term45 term45). Qed.
Lemma lem3176795 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176796 : term96 = term45.
Proof. exact (EQ_MP (@lem3176795) (@lem940073)). Qed.
Lemma lem3176797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176798 : term94 = term44.
Proof. exact (MK_COMB (@lem3176797) (@lem3176796)). Qed.
Lemma lem3176799 : term223 = term44.
Proof. exact (TRANS (@lem3176794) (@lem3176798)). Qed.
Lemma lem3176800 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3176801 : term227 = term228.
Proof. exact (MK_COMB (@lem3176800) (@lem3176799)). Qed.
Lemma lem3176802 : term225 = term74.
Proof. exact (MK_COMB (@lem3176801) (@lem3176791)). Qed.
Lemma lem3176803 : term224 = term74.
Proof. exact (TRANS (@lem3176783) (@lem3176802)). Qed.
Lemma lem3176804 : term223 = term74.
Proof. exact (TRANS (@lem3176782) (@lem3176803)). Qed.
Lemma lem3176806 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3176807 : term74 = term44.
Proof. exact (@lem3176806 term44). Qed.
Lemma lem3176808 : term223 = term44.
Proof. exact (TRANS (@lem3176804) (@lem3176807)). Qed.
Lemma lem3176809 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176810 : term229 = term230.
Proof. exact (MK_COMB (@lem3176809) (@lem3176808)). Qed.
Lemma lem3176811 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3176812 (y : int) : (term222 y) = (term231 y).
Proof. exact (MK_COMB (@lem3176810) (@lem3176811 y)). Qed.
Lemma lem3176813 (y : int) : (term221 y) = (term231 y).
Proof. exact (TRANS (@lem3176773 y) (@lem3176812 y)). Qed.
Lemma lem3176814 (y : int) : (term231 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem3176815 (y : int) : (term221 y) = (real_of_int y).
Proof. exact (TRANS (@lem3176813 y) (@lem3176814 y)). Qed.
Lemma lem3176816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176817 (y : int) : (term232 y) = (term57 y).
Proof. exact (MK_COMB (@lem3176816) (@lem3176815 y)). Qed.
Lemma lem3176818 (y : int) : (term246 y) = (term247 y).
Proof. exact (MK_COMB (@lem3176817 y) (@lem3176772)). Qed.
Lemma lem3176819 (y : int) : (term245 y) = (term247 y).
Proof. exact (TRANS (@lem3176735 y) (@lem3176818 y)). Qed.
Lemma lem3176822 (x : int) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem3176823 (x : int) (y : int) : (term243 x y) = (term248 x y).
Proof. exact (MK_COMB (@lem3176822 x) (@lem3176819 y)). Qed.
Lemma lem3176824 (x : int) (y : int) : (term242 x y) = (term248 x y).
Proof. exact (TRANS (@lem3176734 x y) (@lem3176823 x y)). Qed.
Lemma lem3176825 (x : int) (y : int) : (term234 x y) = (term234 x y).
Proof. exact (eq_refl (term234 x y)). Qed.
Lemma lem3176826 (x : int) (y : int) : (term241 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem3176825 x y) (@lem3176824 x y)). Qed.
Lemma lem3176827 (x : int) (y : int) : (term249 x y) = (term250 x y).
Proof. exact (@lem1982753 (real_of_int x) (term66 x) (term66 y) (term247 y)). Qed.
Lemma lem3176828 (x : int) : (term130 x) = (term71 x).
Proof. exact (@lem1982715 term72 (real_of_int x)). Qed.
Lemma lem3176830 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3176831 : term44 = term74.
Proof. exact (@lem3176830 term45). Qed.
Lemma lem3176833 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176834 : term72 = term77.
Proof. exact (@lem3176833 term45). Qed.
Lemma lem3176835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176836 : term78 = term79.
Proof. exact (MK_COMB (@lem3176835) (@lem3176834)). Qed.
Lemma lem3176837 : term80 = term81.
Proof. exact (MK_COMB (@lem3176836) (@lem3176831)). Qed.
Lemma lem3176838 : term82.
Proof. exact (@lem1981473 term72 term44 term44 term44 term83 term44). Qed.
Lemma lem3176840 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176841 : term85 = term86.
Proof. exact (@lem3176840 (NUMERAL 0) term45). Qed.
Lemma lem3176842 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176843 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176844 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176843 h1) (fun h1 : term86 = True => @lem3176842)). Qed.
Lemma lem3176845 : term86 = True.
Proof. exact (EQ_MP (@lem3176844) (@lem3176842)). Qed.
Lemma lem3176846 : term85 = True.
Proof. exact (TRANS (@lem3176841) (@lem3176845)). Qed.
Lemma lem3176847 : True = term85.
Proof. exact (SYM (@lem3176846)). Qed.
Lemma lem3176848 : term85.
Proof. exact (EQ_MP (@lem3176847) (@lem0)). Qed.
Lemma lem3176849 : term88.
Proof. exact (@lem3176838 (@lem3176848)). Qed.
Lemma lem3176851 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176852 : term85 = term86.
Proof. exact (@lem3176851 (NUMERAL 0) term45). Qed.
Lemma lem3176853 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176854 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176855 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176854 h1) (fun h1 : term86 = True => @lem3176853)). Qed.
Lemma lem3176856 : term86 = True.
Proof. exact (EQ_MP (@lem3176855) (@lem3176853)). Qed.
Lemma lem3176857 : term85 = True.
Proof. exact (TRANS (@lem3176852) (@lem3176856)). Qed.
Lemma lem3176858 : True = term85.
Proof. exact (SYM (@lem3176857)). Qed.
Lemma lem3176859 : term85.
Proof. exact (EQ_MP (@lem3176858) (@lem0)). Qed.
Lemma lem3176860 : term89.
Proof. exact (@lem3176849 (@lem3176859)). Qed.
Lemma lem3176862 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176863 : term85 = term86.
Proof. exact (@lem3176862 (NUMERAL 0) term45). Qed.
Lemma lem3176864 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176865 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176866 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176865 h1) (fun h1 : term86 = True => @lem3176864)). Qed.
Lemma lem3176867 : term86 = True.
Proof. exact (EQ_MP (@lem3176866) (@lem3176864)). Qed.
Lemma lem3176868 : term85 = True.
Proof. exact (TRANS (@lem3176863) (@lem3176867)). Qed.
Lemma lem3176869 : True = term85.
Proof. exact (SYM (@lem3176868)). Qed.
Lemma lem3176870 : term85.
Proof. exact (EQ_MP (@lem3176869) (@lem0)). Qed.
Lemma lem3176871 : term90.
Proof. exact (@lem3176860 (@lem3176870)). Qed.
Lemma lem3176873 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176874 : term93 = term94.
Proof. exact (@lem3176873 term45 term45). Qed.
Lemma lem3176875 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176876 : term96 = term45.
Proof. exact (EQ_MP (@lem3176875) (@lem940073)). Qed.
Lemma lem3176877 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176878 : term94 = term44.
Proof. exact (MK_COMB (@lem3176877) (@lem3176876)). Qed.
Lemma lem3176879 : term93 = term44.
Proof. exact (TRANS (@lem3176874) (@lem3176878)). Qed.
Lemma lem3176881 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3176882 : term99 = term100.
Proof. exact (@lem3176881 term45 term45). Qed.
Lemma lem3176883 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176884 : term96 = term45.
Proof. exact (EQ_MP (@lem3176883) (@lem940073)). Qed.
Lemma lem3176885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176886 : term94 = term44.
Proof. exact (MK_COMB (@lem3176885) (@lem3176884)). Qed.
Lemma lem3176887 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176888 : term100 = term72.
Proof. exact (MK_COMB (@lem3176887) (@lem3176886)). Qed.
Lemma lem3176889 : term99 = term72.
Proof. exact (TRANS (@lem3176882) (@lem3176888)). Qed.
Lemma lem3176890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176891 : term101 = term78.
Proof. exact (MK_COMB (@lem3176890) (@lem3176889)). Qed.
Lemma lem3176892 : term102 = term80.
Proof. exact (MK_COMB (@lem3176891) (@lem3176879)). Qed.
Lemma lem3176894 (m : nat) : (term103 m) = term83.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3176895 : term80 = term83.
Proof. exact (@lem3176894 term45). Qed.
Lemma lem3176896 : term102 = term83.
Proof. exact (TRANS (@lem3176892) (@lem3176895)). Qed.
Lemma lem3176897 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176898 : term104 = term105.
Proof. exact (MK_COMB (@lem3176897) (@lem3176896)). Qed.
Lemma lem3176899 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3176900 : term106 = term107.
Proof. exact (MK_COMB (@lem3176898) (@lem3176899)). Qed.
Lemma lem3176902 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3176903 : term107 = term83.
Proof. exact (@lem3176902 term45). Qed.
Lemma lem3176904 : term106 = term83.
Proof. exact (TRANS (@lem3176900) (@lem3176903)). Qed.
Lemma lem3176906 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176907 : term93 = term94.
Proof. exact (@lem3176906 term45 term45). Qed.
Lemma lem3176908 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176909 : term96 = term45.
Proof. exact (EQ_MP (@lem3176908) (@lem940073)). Qed.
Lemma lem3176910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176911 : term94 = term44.
Proof. exact (MK_COMB (@lem3176910) (@lem3176909)). Qed.
Lemma lem3176912 : term93 = term44.
Proof. exact (TRANS (@lem3176907) (@lem3176911)). Qed.
Lemma lem3176913 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem3176914 : term109 = term107.
Proof. exact (MK_COMB (@lem3176913) (@lem3176912)). Qed.
Lemma lem3176916 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3176917 : term107 = term83.
Proof. exact (@lem3176916 term45). Qed.
Lemma lem3176918 : term109 = term83.
Proof. exact (TRANS (@lem3176914) (@lem3176917)). Qed.
Lemma lem3176919 : term83 = term109.
Proof. exact (SYM (@lem3176918)). Qed.
Lemma lem3176920 : term106 = term109.
Proof. exact (TRANS (@lem3176904) (@lem3176919)). Qed.
Lemma lem3176921 : term81 = term110.
Proof. exact (@lem3176871 (@lem3176920)). Qed.
Lemma lem3176922 : term80 = term110.
Proof. exact (TRANS (@lem3176837) (@lem3176921)). Qed.
Lemma lem3176924 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3176925 : term110 = term83.
Proof. exact (@lem3176924 term83). Qed.
Lemma lem3176926 : term80 = term83.
Proof. exact (TRANS (@lem3176922) (@lem3176925)). Qed.
Lemma lem3176927 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3176928 : term112 = term105.
Proof. exact (MK_COMB (@lem3176927) (@lem3176926)). Qed.
Lemma lem3176929 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3176930 (x : int) : (term71 x) = (term113 x).
Proof. exact (MK_COMB (@lem3176928) (@lem3176929 x)). Qed.
Lemma lem3176931 (x : int) : (term130 x) = (term113 x).
Proof. exact (TRANS (@lem3176828 x) (@lem3176930 x)). Qed.
Lemma lem3176932 (x : int) : (term113 x) = term83.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem3176933 (x : int) : (term130 x) = term83.
Proof. exact (TRANS (@lem3176931 x) (@lem3176932 x)). Qed.
Lemma lem3176934 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176935 (x : int) : (term131 x) = term132.
Proof. exact (MK_COMB (@lem3176934) (@lem3176933 x)). Qed.
Lemma lem3176936 (y : int) : (term251 y) = (term252 y).
Proof. exact (@lem1982763 (term66 y) (real_of_int y) term72). Qed.
Lemma lem3176937 (y : int) : (term70 y) = (term71 y).
Proof. exact (@lem1982713 term72 (real_of_int y)). Qed.
Lemma lem3176939 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3176940 : term44 = term74.
Proof. exact (@lem3176939 term45). Qed.
Lemma lem3176942 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3176943 : term72 = term77.
Proof. exact (@lem3176942 term45). Qed.
Lemma lem3176944 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3176945 : term78 = term79.
Proof. exact (MK_COMB (@lem3176944) (@lem3176943)). Qed.
Lemma lem3176946 : term80 = term81.
Proof. exact (MK_COMB (@lem3176945) (@lem3176940)). Qed.
Lemma lem3176947 : term82.
Proof. exact (@lem1981473 term72 term44 term44 term44 term83 term44). Qed.
Lemma lem3176949 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176950 : term85 = term86.
Proof. exact (@lem3176949 (NUMERAL 0) term45). Qed.
Lemma lem3176951 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176952 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176953 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176952 h1) (fun h1 : term86 = True => @lem3176951)). Qed.
Lemma lem3176954 : term86 = True.
Proof. exact (EQ_MP (@lem3176953) (@lem3176951)). Qed.
Lemma lem3176955 : term85 = True.
Proof. exact (TRANS (@lem3176950) (@lem3176954)). Qed.
Lemma lem3176956 : True = term85.
Proof. exact (SYM (@lem3176955)). Qed.
Lemma lem3176957 : term85.
Proof. exact (EQ_MP (@lem3176956) (@lem0)). Qed.
Lemma lem3176958 : term88.
Proof. exact (@lem3176947 (@lem3176957)). Qed.
Lemma lem3176960 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176961 : term85 = term86.
Proof. exact (@lem3176960 (NUMERAL 0) term45). Qed.
Lemma lem3176962 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176963 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176964 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176963 h1) (fun h1 : term86 = True => @lem3176962)). Qed.
Lemma lem3176965 : term86 = True.
Proof. exact (EQ_MP (@lem3176964) (@lem3176962)). Qed.
Lemma lem3176966 : term85 = True.
Proof. exact (TRANS (@lem3176961) (@lem3176965)). Qed.
Lemma lem3176967 : True = term85.
Proof. exact (SYM (@lem3176966)). Qed.
Lemma lem3176968 : term85.
Proof. exact (EQ_MP (@lem3176967) (@lem0)). Qed.
Lemma lem3176969 : term89.
Proof. exact (@lem3176958 (@lem3176968)). Qed.
Lemma lem3176971 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3176972 : term85 = term86.
Proof. exact (@lem3176971 (NUMERAL 0) term45). Qed.
Lemma lem3176973 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3176974 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3176975 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3176974 h1) (fun h1 : term86 = True => @lem3176973)). Qed.
Lemma lem3176976 : term86 = True.
Proof. exact (EQ_MP (@lem3176975) (@lem3176973)). Qed.
Lemma lem3176977 : term85 = True.
Proof. exact (TRANS (@lem3176972) (@lem3176976)). Qed.
Lemma lem3176978 : True = term85.
Proof. exact (SYM (@lem3176977)). Qed.
Lemma lem3176979 : term85.
Proof. exact (EQ_MP (@lem3176978) (@lem0)). Qed.
Lemma lem3176980 : term90.
Proof. exact (@lem3176969 (@lem3176979)). Qed.
Lemma lem3176982 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3176983 : term93 = term94.
Proof. exact (@lem3176982 term45 term45). Qed.
Lemma lem3176984 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176985 : term96 = term45.
Proof. exact (EQ_MP (@lem3176984) (@lem940073)). Qed.
Lemma lem3176986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176987 : term94 = term44.
Proof. exact (MK_COMB (@lem3176986) (@lem3176985)). Qed.
Lemma lem3176988 : term93 = term44.
Proof. exact (TRANS (@lem3176983) (@lem3176987)). Qed.
Lemma lem3176990 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3176991 : term99 = term100.
Proof. exact (@lem3176990 term45 term45). Qed.
Lemma lem3176992 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3176993 : term96 = term45.
Proof. exact (EQ_MP (@lem3176992) (@lem940073)). Qed.
Lemma lem3176994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3176995 : term94 = term44.
Proof. exact (MK_COMB (@lem3176994) (@lem3176993)). Qed.
Lemma lem3176996 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3176997 : term100 = term72.
Proof. exact (MK_COMB (@lem3176996) (@lem3176995)). Qed.
Lemma lem3176998 : term99 = term72.
Proof. exact (TRANS (@lem3176991) (@lem3176997)). Qed.
Lemma lem3176999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177000 : term101 = term78.
Proof. exact (MK_COMB (@lem3176999) (@lem3176998)). Qed.
Lemma lem3177001 : term102 = term80.
Proof. exact (MK_COMB (@lem3177000) (@lem3176988)). Qed.
Lemma lem3177003 (m : nat) : (term103 m) = term83.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3177004 : term80 = term83.
Proof. exact (@lem3177003 term45). Qed.
Lemma lem3177005 : term102 = term83.
Proof. exact (TRANS (@lem3177001) (@lem3177004)). Qed.
Lemma lem3177006 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177007 : term104 = term105.
Proof. exact (MK_COMB (@lem3177006) (@lem3177005)). Qed.
Lemma lem3177008 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3177009 : term106 = term107.
Proof. exact (MK_COMB (@lem3177007) (@lem3177008)). Qed.
Lemma lem3177011 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3177012 : term107 = term83.
Proof. exact (@lem3177011 term45). Qed.
Lemma lem3177013 : term106 = term83.
Proof. exact (TRANS (@lem3177009) (@lem3177012)). Qed.
Lemma lem3177015 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3177016 : term93 = term94.
Proof. exact (@lem3177015 term45 term45). Qed.
Lemma lem3177017 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177018 : term96 = term45.
Proof. exact (EQ_MP (@lem3177017) (@lem940073)). Qed.
Lemma lem3177019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177020 : term94 = term44.
Proof. exact (MK_COMB (@lem3177019) (@lem3177018)). Qed.
Lemma lem3177021 : term93 = term44.
Proof. exact (TRANS (@lem3177016) (@lem3177020)). Qed.
Lemma lem3177022 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem3177023 : term109 = term107.
Proof. exact (MK_COMB (@lem3177022) (@lem3177021)). Qed.
Lemma lem3177025 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3177026 : term107 = term83.
Proof. exact (@lem3177025 term45). Qed.
Lemma lem3177027 : term109 = term83.
Proof. exact (TRANS (@lem3177023) (@lem3177026)). Qed.
Lemma lem3177028 : term83 = term109.
Proof. exact (SYM (@lem3177027)). Qed.
Lemma lem3177029 : term106 = term109.
Proof. exact (TRANS (@lem3177013) (@lem3177028)). Qed.
Lemma lem3177030 : term81 = term110.
Proof. exact (@lem3176980 (@lem3177029)). Qed.
Lemma lem3177031 : term80 = term110.
Proof. exact (TRANS (@lem3176946) (@lem3177030)). Qed.
Lemma lem3177033 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3177034 : term110 = term83.
Proof. exact (@lem3177033 term83). Qed.
Lemma lem3177035 : term80 = term83.
Proof. exact (TRANS (@lem3177031) (@lem3177034)). Qed.
Lemma lem3177036 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177037 : term112 = term105.
Proof. exact (MK_COMB (@lem3177036) (@lem3177035)). Qed.
Lemma lem3177038 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3177039 (y : int) : (term71 y) = (term113 y).
Proof. exact (MK_COMB (@lem3177037) (@lem3177038 y)). Qed.
Lemma lem3177040 (y : int) : (term70 y) = (term113 y).
Proof. exact (TRANS (@lem3176937 y) (@lem3177039 y)). Qed.
Lemma lem3177041 (y : int) : (term113 y) = term83.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem3177042 (y : int) : (term70 y) = term83.
Proof. exact (TRANS (@lem3177040 y) (@lem3177041 y)). Qed.
Lemma lem3177043 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177044 (y : int) : (term253 y) = term132.
Proof. exact (MK_COMB (@lem3177043) (@lem3177042 y)). Qed.
Lemma lem3177045 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem3177046 (y : int) : (term252 y) = term133.
Proof. exact (MK_COMB (@lem3177044 y) (@lem3177045)). Qed.
Lemma lem3177047 (y : int) : (term251 y) = term133.
Proof. exact (TRANS (@lem3176936 y) (@lem3177046 y)). Qed.
Lemma lem3177048 : term133 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem3177049 (y : int) : (term251 y) = term72.
Proof. exact (TRANS (@lem3177047 y) (@lem3177048)). Qed.
Lemma lem3177050 (x : int) (y : int) : (term250 x y) = term133.
Proof. exact (MK_COMB (@lem3176935 x) (@lem3177049 y)). Qed.
Lemma lem3177051 (x : int) (y : int) : (term249 x y) = term133.
Proof. exact (TRANS (@lem3176827 x y) (@lem3177050 x y)). Qed.
Lemma lem3177052 : term133 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem3177053 (x : int) (y : int) : (term249 x y) = term72.
Proof. exact (TRANS (@lem3177051 x y) (@lem3177052)). Qed.
Lemma lem3177054 (x : int) (y : int) : (term241 x y) = term72.
Proof. exact (TRANS (@lem3176826 x y) (@lem3177053 x y)). Qed.
Lemma lem3177055 (x : int) (y : int) : (term240 x y) = term72.
Proof. exact (TRANS (@lem3176733 x y) (@lem3177054 x y)). Qed.
Lemma lem3177056 (x : int) (y : int) : (term239 x y) = term72.
Proof. exact (TRANS (@lem3176732 x y) (@lem3177055 x y)). Qed.
Lemma lem3177057 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3177058 (x : int) (y : int) : (term254 x y) = term135.
Proof. exact (MK_COMB (@lem3177057) (@lem3177056 x y)). Qed.
Lemma lem3177059 : term83 = term83.
Proof. exact (eq_refl term83). Qed.
Lemma lem3177060 (x : int) (y : int) : (term216 x y) = term136.
Proof. exact (MK_COMB (@lem3177058 x y) (@lem3177059)). Qed.
Lemma lem3177061 (y : int) (x : int) : (term200 y x) = term136.
Proof. exact (TRANS (@lem3176639 x y) (@lem3177060 x y)). Qed.
Lemma lem3177062 (y : int) (x : int) : (term213 x y) = (term255 y x).
Proof. exact (@lem1988287 (term194 x y) (term210 y x)). Qed.
Lemma lem3177063 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3177064 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3177071 (y : int) : (term36 y) = (term66 y).
Proof. exact (@lem1982785 (real_of_int y)). Qed.
Lemma lem3177072 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177073 (y : int) : (term38 y) = (term67 y).
Proof. exact (MK_COMB (@lem3177072) (@lem3177071 y)). Qed.
Lemma lem3177074 (y : int) (x : int) : (term193 y x) = (term217 y x).
Proof. exact (MK_COMB (@lem3177073 y) (@lem3177064 x)). Qed.
Lemma lem3177075 (x : int) (y : int) : (term217 y x) = (term233 x y).
Proof. exact (@lem1982761 (real_of_int x) (term66 y)). Qed.
Lemma lem3177076 (x : int) (y : int) : (term193 y x) = (term233 x y).
Proof. exact (TRANS (@lem3177074 y x) (@lem3177075 x y)). Qed.
Lemma lem3177077 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177078 (x : int) (y : int) : (term209 y x) = (term234 x y).
Proof. exact (MK_COMB (@lem3177077) (@lem3177076 x y)). Qed.
Lemma lem3177079 (x : int) (y : int) : (term210 y x) = (term235 x y).
Proof. exact (MK_COMB (@lem3177078 x y) (@lem3177063)). Qed.
Lemma lem3177084 (x : int) (y : int) : (term235 x y) = (term236 x y).
Proof. exact (@lem1982755 (real_of_int x) (term66 y) term44). Qed.
Lemma lem3177085 (x : int) (y : int) : (term210 y x) = (term236 x y).
Proof. exact (TRANS (@lem3177079 x y) (@lem3177084 x y)). Qed.
Lemma lem3177086 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3177093 (x : int) : (term36 x) = (term66 x).
Proof. exact (@lem1982785 (real_of_int x)). Qed.
Lemma lem3177094 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177095 (x : int) : (term38 x) = (term67 x).
Proof. exact (MK_COMB (@lem3177094) (@lem3177093 x)). Qed.
Lemma lem3177098 (x : int) (y : int) : (term193 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem3177095 x) (@lem3177086 y)). Qed.
Lemma lem3177099 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3177100 (x : int) (y : int) : (term194 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem3177099) (@lem3177098 x y)). Qed.
Lemma lem3177101 (x : int) (y : int) : (term218 x y) = (term219 x y).
Proof. exact (@lem1982785 (term217 x y)). Qed.
Lemma lem3177102 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (@lem1982781 (term66 x) term72 (real_of_int y)). Qed.
Lemma lem3177103 (y : int) : (term66 y) = (term66 y).
Proof. exact (eq_refl (term66 y)). Qed.
Lemma lem3177104 (x : int) : (term221 x) = (term222 x).
Proof. exact (@lem1982749 term72 term72 (real_of_int x)). Qed.
Lemma lem3177106 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177107 : term72 = term77.
Proof. exact (@lem3177106 term45). Qed.
Lemma lem3177109 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177110 : term72 = term77.
Proof. exact (@lem3177109 term45). Qed.
Lemma lem3177111 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177112 : term121 = term122.
Proof. exact (MK_COMB (@lem3177111) (@lem3177110)). Qed.
Lemma lem3177113 : term223 = term224.
Proof. exact (MK_COMB (@lem3177112) (@lem3177107)). Qed.
Lemma lem3177114 : term224 = term225.
Proof. exact (@lem1981613 term72 term72 term44 term44). Qed.
Lemma lem3177116 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3177117 : term93 = term94.
Proof. exact (@lem3177116 term45 term45). Qed.
Lemma lem3177118 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177119 : term96 = term45.
Proof. exact (EQ_MP (@lem3177118) (@lem940073)). Qed.
Lemma lem3177120 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177121 : term94 = term44.
Proof. exact (MK_COMB (@lem3177120) (@lem3177119)). Qed.
Lemma lem3177122 : term93 = term44.
Proof. exact (TRANS (@lem3177117) (@lem3177121)). Qed.
Lemma lem3177124 (m : nat) (n : nat) : (term226 m n) = (term92 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3177125 : term223 = term94.
Proof. exact (@lem3177124 term45 term45). Qed.
Lemma lem3177126 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177127 : term96 = term45.
Proof. exact (EQ_MP (@lem3177126) (@lem940073)). Qed.
Lemma lem3177128 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177129 : term94 = term44.
Proof. exact (MK_COMB (@lem3177128) (@lem3177127)). Qed.
Lemma lem3177130 : term223 = term44.
Proof. exact (TRANS (@lem3177125) (@lem3177129)). Qed.
Lemma lem3177131 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3177132 : term227 = term228.
Proof. exact (MK_COMB (@lem3177131) (@lem3177130)). Qed.
Lemma lem3177133 : term225 = term74.
Proof. exact (MK_COMB (@lem3177132) (@lem3177122)). Qed.
Lemma lem3177134 : term224 = term74.
Proof. exact (TRANS (@lem3177114) (@lem3177133)). Qed.
Lemma lem3177135 : term223 = term74.
Proof. exact (TRANS (@lem3177113) (@lem3177134)). Qed.
Lemma lem3177137 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3177138 : term74 = term44.
Proof. exact (@lem3177137 term44). Qed.
Lemma lem3177139 : term223 = term44.
Proof. exact (TRANS (@lem3177135) (@lem3177138)). Qed.
Lemma lem3177140 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177141 : term229 = term230.
Proof. exact (MK_COMB (@lem3177140) (@lem3177139)). Qed.
Lemma lem3177142 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3177143 (x : int) : (term222 x) = (term231 x).
Proof. exact (MK_COMB (@lem3177141) (@lem3177142 x)). Qed.
Lemma lem3177144 (x : int) : (term221 x) = (term231 x).
Proof. exact (TRANS (@lem3177104 x) (@lem3177143 x)). Qed.
Lemma lem3177145 (x : int) : (term231 x) = (real_of_int x).
Proof. exact (@lem1982709 (real_of_int x)). Qed.
Lemma lem3177146 (x : int) : (term221 x) = (real_of_int x).
Proof. exact (TRANS (@lem3177144 x) (@lem3177145 x)). Qed.
Lemma lem3177147 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177148 (x : int) : (term232 x) = (term57 x).
Proof. exact (MK_COMB (@lem3177147) (@lem3177146 x)). Qed.
Lemma lem3177149 (x : int) (y : int) : (term220 x y) = (term233 x y).
Proof. exact (MK_COMB (@lem3177148 x) (@lem3177103 y)). Qed.
Lemma lem3177150 (x : int) (y : int) : (term219 x y) = (term233 x y).
Proof. exact (TRANS (@lem3177102 x y) (@lem3177149 x y)). Qed.
Lemma lem3177151 (x : int) (y : int) : (term218 x y) = (term233 x y).
Proof. exact (TRANS (@lem3177101 x y) (@lem3177150 x y)). Qed.
Lemma lem3177152 (x : int) (y : int) : (term194 x y) = (term233 x y).
Proof. exact (TRANS (@lem3177100 x y) (@lem3177151 x y)). Qed.
Lemma lem3177153 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem3177154 (x : int) (y : int) : (term256 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem3177153) (@lem3177152 x y)). Qed.
Lemma lem3177155 (x : int) (y : int) : (term257 y x) = (term240 x y).
Proof. exact (MK_COMB (@lem3177154 x y) (@lem3177085 x y)). Qed.
Lemma lem3177156 (x : int) (y : int) : (term240 x y) = (term241 x y).
Proof. exact (@lem1982792 (term233 x y) (term236 x y)). Qed.
Lemma lem3177157 (x : int) (y : int) : (term242 x y) = (term243 x y).
Proof. exact (@lem1982781 (real_of_int x) term72 (term244 y)). Qed.
Lemma lem3177158 (y : int) : (term245 y) = (term246 y).
Proof. exact (@lem1982781 (term66 y) term72 term44). Qed.
Lemma lem3177160 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3177161 : term44 = term74.
Proof. exact (@lem3177160 term45). Qed.
Lemma lem3177163 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177164 : term72 = term77.
Proof. exact (@lem3177163 term45). Qed.
Lemma lem3177165 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177166 : term121 = term122.
Proof. exact (MK_COMB (@lem3177165) (@lem3177164)). Qed.
Lemma lem3177167 : term99 = term123.
Proof. exact (MK_COMB (@lem3177166) (@lem3177161)). Qed.
Lemma lem3177168 : term123 = term124.
Proof. exact (@lem1981613 term72 term44 term44 term44). Qed.
Lemma lem3177170 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3177171 : term93 = term94.
Proof. exact (@lem3177170 term45 term45). Qed.
Lemma lem3177172 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177173 : term96 = term45.
Proof. exact (EQ_MP (@lem3177172) (@lem940073)). Qed.
Lemma lem3177174 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177175 : term94 = term44.
Proof. exact (MK_COMB (@lem3177174) (@lem3177173)). Qed.
Lemma lem3177176 : term93 = term44.
Proof. exact (TRANS (@lem3177171) (@lem3177175)). Qed.
Lemma lem3177178 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3177179 : term99 = term100.
Proof. exact (@lem3177178 term45 term45). Qed.
Lemma lem3177180 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177181 : term96 = term45.
Proof. exact (EQ_MP (@lem3177180) (@lem940073)). Qed.
Lemma lem3177182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177183 : term94 = term44.
Proof. exact (MK_COMB (@lem3177182) (@lem3177181)). Qed.
Lemma lem3177184 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3177185 : term100 = term72.
Proof. exact (MK_COMB (@lem3177184) (@lem3177183)). Qed.
Lemma lem3177186 : term99 = term72.
Proof. exact (TRANS (@lem3177179) (@lem3177185)). Qed.
Lemma lem3177187 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3177188 : term125 = term126.
Proof. exact (MK_COMB (@lem3177187) (@lem3177186)). Qed.
Lemma lem3177189 : term124 = term77.
Proof. exact (MK_COMB (@lem3177188) (@lem3177176)). Qed.
Lemma lem3177190 : term123 = term77.
Proof. exact (TRANS (@lem3177168) (@lem3177189)). Qed.
Lemma lem3177191 : term99 = term77.
Proof. exact (TRANS (@lem3177167) (@lem3177190)). Qed.
Lemma lem3177193 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3177194 : term77 = term72.
Proof. exact (@lem3177193 term72). Qed.
Lemma lem3177195 : term99 = term72.
Proof. exact (TRANS (@lem3177191) (@lem3177194)). Qed.
Lemma lem3177196 (y : int) : (term221 y) = (term222 y).
Proof. exact (@lem1982749 term72 term72 (real_of_int y)). Qed.
Lemma lem3177198 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177199 : term72 = term77.
Proof. exact (@lem3177198 term45). Qed.
Lemma lem3177201 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177202 : term72 = term77.
Proof. exact (@lem3177201 term45). Qed.
Lemma lem3177203 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177204 : term121 = term122.
Proof. exact (MK_COMB (@lem3177203) (@lem3177202)). Qed.
Lemma lem3177205 : term223 = term224.
Proof. exact (MK_COMB (@lem3177204) (@lem3177199)). Qed.
Lemma lem3177206 : term224 = term225.
Proof. exact (@lem1981613 term72 term72 term44 term44). Qed.
Lemma lem3177208 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3177209 : term93 = term94.
Proof. exact (@lem3177208 term45 term45). Qed.
Lemma lem3177210 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177211 : term96 = term45.
Proof. exact (EQ_MP (@lem3177210) (@lem940073)). Qed.
Lemma lem3177212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177213 : term94 = term44.
Proof. exact (MK_COMB (@lem3177212) (@lem3177211)). Qed.
Lemma lem3177214 : term93 = term44.
Proof. exact (TRANS (@lem3177209) (@lem3177213)). Qed.
Lemma lem3177216 (m : nat) (n : nat) : (term226 m n) = (term92 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3177217 : term223 = term94.
Proof. exact (@lem3177216 term45 term45). Qed.
Lemma lem3177218 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177219 : term96 = term45.
Proof. exact (EQ_MP (@lem3177218) (@lem940073)). Qed.
Lemma lem3177220 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177221 : term94 = term44.
Proof. exact (MK_COMB (@lem3177220) (@lem3177219)). Qed.
Lemma lem3177222 : term223 = term44.
Proof. exact (TRANS (@lem3177217) (@lem3177221)). Qed.
Lemma lem3177223 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3177224 : term227 = term228.
Proof. exact (MK_COMB (@lem3177223) (@lem3177222)). Qed.
Lemma lem3177225 : term225 = term74.
Proof. exact (MK_COMB (@lem3177224) (@lem3177214)). Qed.
Lemma lem3177226 : term224 = term74.
Proof. exact (TRANS (@lem3177206) (@lem3177225)). Qed.
Lemma lem3177227 : term223 = term74.
Proof. exact (TRANS (@lem3177205) (@lem3177226)). Qed.
Lemma lem3177229 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3177230 : term74 = term44.
Proof. exact (@lem3177229 term44). Qed.
Lemma lem3177231 : term223 = term44.
Proof. exact (TRANS (@lem3177227) (@lem3177230)). Qed.
Lemma lem3177232 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177233 : term229 = term230.
Proof. exact (MK_COMB (@lem3177232) (@lem3177231)). Qed.
Lemma lem3177234 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3177235 (y : int) : (term222 y) = (term231 y).
Proof. exact (MK_COMB (@lem3177233) (@lem3177234 y)). Qed.
Lemma lem3177236 (y : int) : (term221 y) = (term231 y).
Proof. exact (TRANS (@lem3177196 y) (@lem3177235 y)). Qed.
Lemma lem3177237 (y : int) : (term231 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem3177238 (y : int) : (term221 y) = (real_of_int y).
Proof. exact (TRANS (@lem3177236 y) (@lem3177237 y)). Qed.
Lemma lem3177239 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177240 (y : int) : (term232 y) = (term57 y).
Proof. exact (MK_COMB (@lem3177239) (@lem3177238 y)). Qed.
Lemma lem3177241 (y : int) : (term246 y) = (term247 y).
Proof. exact (MK_COMB (@lem3177240 y) (@lem3177195)). Qed.
Lemma lem3177242 (y : int) : (term245 y) = (term247 y).
Proof. exact (TRANS (@lem3177158 y) (@lem3177241 y)). Qed.
Lemma lem3177245 (x : int) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem3177246 (x : int) (y : int) : (term243 x y) = (term248 x y).
Proof. exact (MK_COMB (@lem3177245 x) (@lem3177242 y)). Qed.
Lemma lem3177247 (x : int) (y : int) : (term242 x y) = (term248 x y).
Proof. exact (TRANS (@lem3177157 x y) (@lem3177246 x y)). Qed.
Lemma lem3177248 (x : int) (y : int) : (term234 x y) = (term234 x y).
Proof. exact (eq_refl (term234 x y)). Qed.
Lemma lem3177249 (x : int) (y : int) : (term241 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem3177248 x y) (@lem3177247 x y)). Qed.
Lemma lem3177250 (x : int) (y : int) : (term249 x y) = (term250 x y).
Proof. exact (@lem1982753 (real_of_int x) (term66 x) (term66 y) (term247 y)). Qed.
Lemma lem3177251 (x : int) : (term130 x) = (term71 x).
Proof. exact (@lem1982715 term72 (real_of_int x)). Qed.
Lemma lem3177253 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3177254 : term44 = term74.
Proof. exact (@lem3177253 term45). Qed.
Lemma lem3177256 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177257 : term72 = term77.
Proof. exact (@lem3177256 term45). Qed.
Lemma lem3177258 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177259 : term78 = term79.
Proof. exact (MK_COMB (@lem3177258) (@lem3177257)). Qed.
Lemma lem3177260 : term80 = term81.
Proof. exact (MK_COMB (@lem3177259) (@lem3177254)). Qed.
Lemma lem3177261 : term82.
Proof. exact (@lem1981473 term72 term44 term44 term44 term83 term44). Qed.
Lemma lem3177263 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177264 : term85 = term86.
Proof. exact (@lem3177263 (NUMERAL 0) term45). Qed.
Lemma lem3177265 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177266 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177267 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177266 h1) (fun h1 : term86 = True => @lem3177265)). Qed.
Lemma lem3177268 : term86 = True.
Proof. exact (EQ_MP (@lem3177267) (@lem3177265)). Qed.
Lemma lem3177269 : term85 = True.
Proof. exact (TRANS (@lem3177264) (@lem3177268)). Qed.
Lemma lem3177270 : True = term85.
Proof. exact (SYM (@lem3177269)). Qed.
Lemma lem3177271 : term85.
Proof. exact (EQ_MP (@lem3177270) (@lem0)). Qed.
Lemma lem3177272 : term88.
Proof. exact (@lem3177261 (@lem3177271)). Qed.
Lemma lem3177274 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177275 : term85 = term86.
Proof. exact (@lem3177274 (NUMERAL 0) term45). Qed.
Lemma lem3177276 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177277 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177278 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177277 h1) (fun h1 : term86 = True => @lem3177276)). Qed.
Lemma lem3177279 : term86 = True.
Proof. exact (EQ_MP (@lem3177278) (@lem3177276)). Qed.
Lemma lem3177280 : term85 = True.
Proof. exact (TRANS (@lem3177275) (@lem3177279)). Qed.
Lemma lem3177281 : True = term85.
Proof. exact (SYM (@lem3177280)). Qed.
Lemma lem3177282 : term85.
Proof. exact (EQ_MP (@lem3177281) (@lem0)). Qed.
Lemma lem3177283 : term89.
Proof. exact (@lem3177272 (@lem3177282)). Qed.
Lemma lem3177285 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177286 : term85 = term86.
Proof. exact (@lem3177285 (NUMERAL 0) term45). Qed.
Lemma lem3177287 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177288 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177289 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177288 h1) (fun h1 : term86 = True => @lem3177287)). Qed.
Lemma lem3177290 : term86 = True.
Proof. exact (EQ_MP (@lem3177289) (@lem3177287)). Qed.
Lemma lem3177291 : term85 = True.
Proof. exact (TRANS (@lem3177286) (@lem3177290)). Qed.
Lemma lem3177292 : True = term85.
Proof. exact (SYM (@lem3177291)). Qed.
Lemma lem3177293 : term85.
Proof. exact (EQ_MP (@lem3177292) (@lem0)). Qed.
Lemma lem3177294 : term90.
Proof. exact (@lem3177283 (@lem3177293)). Qed.
Lemma lem3177296 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3177297 : term93 = term94.
Proof. exact (@lem3177296 term45 term45). Qed.
Lemma lem3177298 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177299 : term96 = term45.
Proof. exact (EQ_MP (@lem3177298) (@lem940073)). Qed.
Lemma lem3177300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177301 : term94 = term44.
Proof. exact (MK_COMB (@lem3177300) (@lem3177299)). Qed.
Lemma lem3177302 : term93 = term44.
Proof. exact (TRANS (@lem3177297) (@lem3177301)). Qed.
Lemma lem3177304 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3177305 : term99 = term100.
Proof. exact (@lem3177304 term45 term45). Qed.
Lemma lem3177306 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177307 : term96 = term45.
Proof. exact (EQ_MP (@lem3177306) (@lem940073)). Qed.
Lemma lem3177308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177309 : term94 = term44.
Proof. exact (MK_COMB (@lem3177308) (@lem3177307)). Qed.
Lemma lem3177310 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3177311 : term100 = term72.
Proof. exact (MK_COMB (@lem3177310) (@lem3177309)). Qed.
Lemma lem3177312 : term99 = term72.
Proof. exact (TRANS (@lem3177305) (@lem3177311)). Qed.
Lemma lem3177313 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177314 : term101 = term78.
Proof. exact (MK_COMB (@lem3177313) (@lem3177312)). Qed.
Lemma lem3177315 : term102 = term80.
Proof. exact (MK_COMB (@lem3177314) (@lem3177302)). Qed.
Lemma lem3177317 (m : nat) : (term103 m) = term83.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3177318 : term80 = term83.
Proof. exact (@lem3177317 term45). Qed.
Lemma lem3177319 : term102 = term83.
Proof. exact (TRANS (@lem3177315) (@lem3177318)). Qed.
Lemma lem3177320 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177321 : term104 = term105.
Proof. exact (MK_COMB (@lem3177320) (@lem3177319)). Qed.
Lemma lem3177322 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3177323 : term106 = term107.
Proof. exact (MK_COMB (@lem3177321) (@lem3177322)). Qed.
Lemma lem3177325 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3177326 : term107 = term83.
Proof. exact (@lem3177325 term45). Qed.
Lemma lem3177327 : term106 = term83.
Proof. exact (TRANS (@lem3177323) (@lem3177326)). Qed.
Lemma lem3177329 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3177330 : term93 = term94.
Proof. exact (@lem3177329 term45 term45). Qed.
Lemma lem3177331 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177332 : term96 = term45.
Proof. exact (EQ_MP (@lem3177331) (@lem940073)). Qed.
Lemma lem3177333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177334 : term94 = term44.
Proof. exact (MK_COMB (@lem3177333) (@lem3177332)). Qed.
Lemma lem3177335 : term93 = term44.
Proof. exact (TRANS (@lem3177330) (@lem3177334)). Qed.
Lemma lem3177336 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem3177337 : term109 = term107.
Proof. exact (MK_COMB (@lem3177336) (@lem3177335)). Qed.
Lemma lem3177339 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3177340 : term107 = term83.
Proof. exact (@lem3177339 term45). Qed.
Lemma lem3177341 : term109 = term83.
Proof. exact (TRANS (@lem3177337) (@lem3177340)). Qed.
Lemma lem3177342 : term83 = term109.
Proof. exact (SYM (@lem3177341)). Qed.
Lemma lem3177343 : term106 = term109.
Proof. exact (TRANS (@lem3177327) (@lem3177342)). Qed.
Lemma lem3177344 : term81 = term110.
Proof. exact (@lem3177294 (@lem3177343)). Qed.
Lemma lem3177345 : term80 = term110.
Proof. exact (TRANS (@lem3177260) (@lem3177344)). Qed.
Lemma lem3177347 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3177348 : term110 = term83.
Proof. exact (@lem3177347 term83). Qed.
Lemma lem3177349 : term80 = term83.
Proof. exact (TRANS (@lem3177345) (@lem3177348)). Qed.
Lemma lem3177350 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177351 : term112 = term105.
Proof. exact (MK_COMB (@lem3177350) (@lem3177349)). Qed.
Lemma lem3177352 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3177353 (x : int) : (term71 x) = (term113 x).
Proof. exact (MK_COMB (@lem3177351) (@lem3177352 x)). Qed.
Lemma lem3177354 (x : int) : (term130 x) = (term113 x).
Proof. exact (TRANS (@lem3177251 x) (@lem3177353 x)). Qed.
Lemma lem3177355 (x : int) : (term113 x) = term83.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem3177356 (x : int) : (term130 x) = term83.
Proof. exact (TRANS (@lem3177354 x) (@lem3177355 x)). Qed.
Lemma lem3177357 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177358 (x : int) : (term131 x) = term132.
Proof. exact (MK_COMB (@lem3177357) (@lem3177356 x)). Qed.
Lemma lem3177359 (y : int) : (term251 y) = (term252 y).
Proof. exact (@lem1982763 (term66 y) (real_of_int y) term72). Qed.
Lemma lem3177360 (y : int) : (term70 y) = (term71 y).
Proof. exact (@lem1982713 term72 (real_of_int y)). Qed.
Lemma lem3177362 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3177363 : term44 = term74.
Proof. exact (@lem3177362 term45). Qed.
Lemma lem3177365 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177366 : term72 = term77.
Proof. exact (@lem3177365 term45). Qed.
Lemma lem3177367 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177368 : term78 = term79.
Proof. exact (MK_COMB (@lem3177367) (@lem3177366)). Qed.
Lemma lem3177369 : term80 = term81.
Proof. exact (MK_COMB (@lem3177368) (@lem3177363)). Qed.
Lemma lem3177370 : term82.
Proof. exact (@lem1981473 term72 term44 term44 term44 term83 term44). Qed.
Lemma lem3177372 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177373 : term85 = term86.
Proof. exact (@lem3177372 (NUMERAL 0) term45). Qed.
Lemma lem3177374 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177375 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177376 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177375 h1) (fun h1 : term86 = True => @lem3177374)). Qed.
Lemma lem3177377 : term86 = True.
Proof. exact (EQ_MP (@lem3177376) (@lem3177374)). Qed.
Lemma lem3177378 : term85 = True.
Proof. exact (TRANS (@lem3177373) (@lem3177377)). Qed.
Lemma lem3177379 : True = term85.
Proof. exact (SYM (@lem3177378)). Qed.
Lemma lem3177380 : term85.
Proof. exact (EQ_MP (@lem3177379) (@lem0)). Qed.
Lemma lem3177381 : term88.
Proof. exact (@lem3177370 (@lem3177380)). Qed.
Lemma lem3177383 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177384 : term85 = term86.
Proof. exact (@lem3177383 (NUMERAL 0) term45). Qed.
Lemma lem3177385 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177386 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177387 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177386 h1) (fun h1 : term86 = True => @lem3177385)). Qed.
Lemma lem3177388 : term86 = True.
Proof. exact (EQ_MP (@lem3177387) (@lem3177385)). Qed.
Lemma lem3177389 : term85 = True.
Proof. exact (TRANS (@lem3177384) (@lem3177388)). Qed.
Lemma lem3177390 : True = term85.
Proof. exact (SYM (@lem3177389)). Qed.
Lemma lem3177391 : term85.
Proof. exact (EQ_MP (@lem3177390) (@lem0)). Qed.
Lemma lem3177392 : term89.
Proof. exact (@lem3177381 (@lem3177391)). Qed.
Lemma lem3177394 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177395 : term85 = term86.
Proof. exact (@lem3177394 (NUMERAL 0) term45). Qed.
Lemma lem3177396 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177397 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177398 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177397 h1) (fun h1 : term86 = True => @lem3177396)). Qed.
Lemma lem3177399 : term86 = True.
Proof. exact (EQ_MP (@lem3177398) (@lem3177396)). Qed.
Lemma lem3177400 : term85 = True.
Proof. exact (TRANS (@lem3177395) (@lem3177399)). Qed.
Lemma lem3177401 : True = term85.
Proof. exact (SYM (@lem3177400)). Qed.
Lemma lem3177402 : term85.
Proof. exact (EQ_MP (@lem3177401) (@lem0)). Qed.
Lemma lem3177403 : term90.
Proof. exact (@lem3177392 (@lem3177402)). Qed.
Lemma lem3177405 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3177406 : term93 = term94.
Proof. exact (@lem3177405 term45 term45). Qed.
Lemma lem3177407 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177408 : term96 = term45.
Proof. exact (EQ_MP (@lem3177407) (@lem940073)). Qed.
Lemma lem3177409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177410 : term94 = term44.
Proof. exact (MK_COMB (@lem3177409) (@lem3177408)). Qed.
Lemma lem3177411 : term93 = term44.
Proof. exact (TRANS (@lem3177406) (@lem3177410)). Qed.
Lemma lem3177413 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3177414 : term99 = term100.
Proof. exact (@lem3177413 term45 term45). Qed.
Lemma lem3177415 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177416 : term96 = term45.
Proof. exact (EQ_MP (@lem3177415) (@lem940073)). Qed.
Lemma lem3177417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177418 : term94 = term44.
Proof. exact (MK_COMB (@lem3177417) (@lem3177416)). Qed.
Lemma lem3177419 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3177420 : term100 = term72.
Proof. exact (MK_COMB (@lem3177419) (@lem3177418)). Qed.
Lemma lem3177421 : term99 = term72.
Proof. exact (TRANS (@lem3177414) (@lem3177420)). Qed.
Lemma lem3177422 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177423 : term101 = term78.
Proof. exact (MK_COMB (@lem3177422) (@lem3177421)). Qed.
Lemma lem3177424 : term102 = term80.
Proof. exact (MK_COMB (@lem3177423) (@lem3177411)). Qed.
Lemma lem3177426 (m : nat) : (term103 m) = term83.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3177427 : term80 = term83.
Proof. exact (@lem3177426 term45). Qed.
Lemma lem3177428 : term102 = term83.
Proof. exact (TRANS (@lem3177424) (@lem3177427)). Qed.
Lemma lem3177429 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177430 : term104 = term105.
Proof. exact (MK_COMB (@lem3177429) (@lem3177428)). Qed.
Lemma lem3177431 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem3177432 : term106 = term107.
Proof. exact (MK_COMB (@lem3177430) (@lem3177431)). Qed.
Lemma lem3177434 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3177435 : term107 = term83.
Proof. exact (@lem3177434 term45). Qed.
Lemma lem3177436 : term106 = term83.
Proof. exact (TRANS (@lem3177432) (@lem3177435)). Qed.
Lemma lem3177438 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3177439 : term93 = term94.
Proof. exact (@lem3177438 term45 term45). Qed.
Lemma lem3177440 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177441 : term96 = term45.
Proof. exact (EQ_MP (@lem3177440) (@lem940073)). Qed.
Lemma lem3177442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177443 : term94 = term44.
Proof. exact (MK_COMB (@lem3177442) (@lem3177441)). Qed.
Lemma lem3177444 : term93 = term44.
Proof. exact (TRANS (@lem3177439) (@lem3177443)). Qed.
Lemma lem3177445 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem3177446 : term109 = term107.
Proof. exact (MK_COMB (@lem3177445) (@lem3177444)). Qed.
Lemma lem3177448 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3177449 : term107 = term83.
Proof. exact (@lem3177448 term45). Qed.
Lemma lem3177450 : term109 = term83.
Proof. exact (TRANS (@lem3177446) (@lem3177449)). Qed.
Lemma lem3177451 : term83 = term109.
Proof. exact (SYM (@lem3177450)). Qed.
Lemma lem3177452 : term106 = term109.
Proof. exact (TRANS (@lem3177436) (@lem3177451)). Qed.
Lemma lem3177453 : term81 = term110.
Proof. exact (@lem3177403 (@lem3177452)). Qed.
Lemma lem3177454 : term80 = term110.
Proof. exact (TRANS (@lem3177369) (@lem3177453)). Qed.
Lemma lem3177456 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3177457 : term110 = term83.
Proof. exact (@lem3177456 term83). Qed.
Lemma lem3177458 : term80 = term83.
Proof. exact (TRANS (@lem3177454) (@lem3177457)). Qed.
Lemma lem3177459 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3177460 : term112 = term105.
Proof. exact (MK_COMB (@lem3177459) (@lem3177458)). Qed.
Lemma lem3177461 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3177462 (y : int) : (term71 y) = (term113 y).
Proof. exact (MK_COMB (@lem3177460) (@lem3177461 y)). Qed.
Lemma lem3177463 (y : int) : (term70 y) = (term113 y).
Proof. exact (TRANS (@lem3177360 y) (@lem3177462 y)). Qed.
Lemma lem3177464 (y : int) : (term113 y) = term83.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem3177465 (y : int) : (term70 y) = term83.
Proof. exact (TRANS (@lem3177463 y) (@lem3177464 y)). Qed.
Lemma lem3177466 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3177467 (y : int) : (term253 y) = term132.
Proof. exact (MK_COMB (@lem3177466) (@lem3177465 y)). Qed.
Lemma lem3177468 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem3177469 (y : int) : (term252 y) = term133.
Proof. exact (MK_COMB (@lem3177467 y) (@lem3177468)). Qed.
Lemma lem3177470 (y : int) : (term251 y) = term133.
Proof. exact (TRANS (@lem3177359 y) (@lem3177469 y)). Qed.
Lemma lem3177471 : term133 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem3177472 (y : int) : (term251 y) = term72.
Proof. exact (TRANS (@lem3177470 y) (@lem3177471)). Qed.
Lemma lem3177473 (x : int) (y : int) : (term250 x y) = term133.
Proof. exact (MK_COMB (@lem3177358 x) (@lem3177472 y)). Qed.
Lemma lem3177474 (x : int) (y : int) : (term249 x y) = term133.
Proof. exact (TRANS (@lem3177250 x y) (@lem3177473 x y)). Qed.
Lemma lem3177475 : term133 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem3177476 (x : int) (y : int) : (term249 x y) = term72.
Proof. exact (TRANS (@lem3177474 x y) (@lem3177475)). Qed.
Lemma lem3177477 (x : int) (y : int) : (term241 x y) = term72.
Proof. exact (TRANS (@lem3177249 x y) (@lem3177476 x y)). Qed.
Lemma lem3177478 (x : int) (y : int) : (term240 x y) = term72.
Proof. exact (TRANS (@lem3177156 x y) (@lem3177477 x y)). Qed.
Lemma lem3177479 (y : int) (x : int) : (term257 y x) = term72.
Proof. exact (TRANS (@lem3177155 x y) (@lem3177478 x y)). Qed.
Lemma lem3177480 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3177481 (y : int) (x : int) : (term258 y x) = term135.
Proof. exact (MK_COMB (@lem3177480) (@lem3177479 y x)). Qed.
Lemma lem3177482 : term83 = term83.
Proof. exact (eq_refl term83). Qed.
Lemma lem3177483 (y : int) (x : int) : (term255 y x) = term136.
Proof. exact (MK_COMB (@lem3177481 y x) (@lem3177482)). Qed.
Lemma lem3177484 (x : int) (y : int) : (term213 x y) = term136.
Proof. exact (TRANS (@lem3177062 y x) (@lem3177483 y x)). Qed.
Lemma lem3177485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3177486 (y : int) (x : int) : (term202 y x) = term141.
Proof. exact (MK_COMB (@lem3177485) (@lem3177061 y x)). Qed.
Lemma lem3177487 (x : int) (y : int) : (term214 x y) = term142.
Proof. exact (MK_COMB (@lem3177486 y x) (@lem3177484 x y)). Qed.
Lemma lem3177500 (x : int) (y : int) : (term215 x y) = term142.
Proof. exact (TRANS (@lem3176638 x y) (@lem3177487 x y)). Qed.
Lemma lem3177510 (h1 : term142) : term142.
Proof. exact (h1). Qed.
Lemma lem3177511 (h1 : term136) : term136.
Proof. exact (h1). Qed.
Lemma lem3177513 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3177514 : term136 = term143.
Proof. exact (@lem3177513 term83 term72). Qed.
Lemma lem3177516 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177517 : term72 = term77.
Proof. exact (@lem3177516 term45). Qed.
Lemma lem3177519 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3177520 : term83 = term110.
Proof. exact (@lem3177519 (NUMERAL 0)). Qed.
Lemma lem3177521 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3177522 : term144 = term145.
Proof. exact (MK_COMB (@lem3177521) (@lem3177520)). Qed.
Lemma lem3177523 : term143 = term146.
Proof. exact (MK_COMB (@lem3177522) (@lem3177517)). Qed.
Lemma lem3177524 : term147.
Proof. exact (@lem1980026 term83 term44 term72 term44). Qed.
Lemma lem3177526 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177527 : term85 = term86.
Proof. exact (@lem3177526 (NUMERAL 0) term45). Qed.
Lemma lem3177528 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177529 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177530 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177529 h1) (fun h1 : term86 = True => @lem3177528)). Qed.
Lemma lem3177531 : term86 = True.
Proof. exact (EQ_MP (@lem3177530) (@lem3177528)). Qed.
Lemma lem3177532 : term85 = True.
Proof. exact (TRANS (@lem3177527) (@lem3177531)). Qed.
Lemma lem3177533 : True = term85.
Proof. exact (SYM (@lem3177532)). Qed.
Lemma lem3177534 : term85.
Proof. exact (EQ_MP (@lem3177533) (@lem0)). Qed.
Lemma lem3177535 : term148.
Proof. exact (@lem3177524 (@lem3177534)). Qed.
Lemma lem3177537 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177538 : term85 = term86.
Proof. exact (@lem3177537 (NUMERAL 0) term45). Qed.
Lemma lem3177539 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177540 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177541 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177540 h1) (fun h1 : term86 = True => @lem3177539)). Qed.
Lemma lem3177542 : term86 = True.
Proof. exact (EQ_MP (@lem3177541) (@lem3177539)). Qed.
Lemma lem3177543 : term85 = True.
Proof. exact (TRANS (@lem3177538) (@lem3177542)). Qed.
Lemma lem3177544 : True = term85.
Proof. exact (SYM (@lem3177543)). Qed.
Lemma lem3177545 : term85.
Proof. exact (EQ_MP (@lem3177544) (@lem0)). Qed.
Lemma lem3177546 : term146 = term149.
Proof. exact (@lem3177535 (@lem3177545)). Qed.
Lemma lem3177548 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3177549 : term99 = term100.
Proof. exact (@lem3177548 term45 term45). Qed.
Lemma lem3177550 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177551 : term96 = term45.
Proof. exact (EQ_MP (@lem3177550) (@lem940073)). Qed.
Lemma lem3177552 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177553 : term94 = term44.
Proof. exact (MK_COMB (@lem3177552) (@lem3177551)). Qed.
Lemma lem3177554 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3177555 : term100 = term72.
Proof. exact (MK_COMB (@lem3177554) (@lem3177553)). Qed.
Lemma lem3177556 : term99 = term72.
Proof. exact (TRANS (@lem3177549) (@lem3177555)). Qed.
Lemma lem3177558 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3177559 : term107 = term83.
Proof. exact (@lem3177558 term45). Qed.
Lemma lem3177560 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3177561 : term150 = term144.
Proof. exact (MK_COMB (@lem3177560) (@lem3177559)). Qed.
Lemma lem3177562 : term149 = term143.
Proof. exact (MK_COMB (@lem3177561) (@lem3177556)). Qed.
Lemma lem3177564 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3177565 : term143 = term153.
Proof. exact (@lem3177564 (NUMERAL 0) term45). Qed.
Lemma lem3177566 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177567 (h1 : term87 = (BIT1 0)) : (term45 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3177568 : (term87 = (BIT1 0)) = ((term45 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177567 h1) (fun h1 : (term45 = (NUMERAL 0)) = False => @lem3177566)). Qed.
Lemma lem3177569 : (term45 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3177568) (@lem3177566)). Qed.
Lemma lem3177570 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3177571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3177572 : term154 = (and True).
Proof. exact (MK_COMB (@lem3177571) (@lem3177570)). Qed.
Lemma lem3177573 : term153 = (True /\ False).
Proof. exact (MK_COMB (@lem3177572) (@lem3177569)). Qed.
Lemma lem3177575 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3177576 : term153 = False.
Proof. exact (TRANS (@lem3177573) (@lem3177575)). Qed.
Lemma lem3177577 : term143 = False.
Proof. exact (TRANS (@lem3177565) (@lem3177576)). Qed.
Lemma lem3177578 : term149 = False.
Proof. exact (TRANS (@lem3177562) (@lem3177577)). Qed.
Lemma lem3177579 : term146 = False.
Proof. exact (TRANS (@lem3177546) (@lem3177578)). Qed.
Lemma lem3177580 : term143 = False.
Proof. exact (TRANS (@lem3177523) (@lem3177579)). Qed.
Lemma lem3177581 : term136 = False.
Proof. exact (TRANS (@lem3177514) (@lem3177580)). Qed.
Lemma lem3177582 (h1 : term136) : False.
Proof. exact (EQ_MP (@lem3177581) (@lem3177511 h1)). Qed.
Lemma lem3177583 (h1 : term136) : term136.
Proof. exact (h1). Qed.
Lemma lem3177585 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3177586 : term136 = term143.
Proof. exact (@lem3177585 term83 term72). Qed.
Lemma lem3177588 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3177589 : term72 = term77.
Proof. exact (@lem3177588 term45). Qed.
Lemma lem3177591 (x : nat) : (real_of_num x) = (term73 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3177592 : term83 = term110.
Proof. exact (@lem3177591 (NUMERAL 0)). Qed.
Lemma lem3177593 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3177594 : term144 = term145.
Proof. exact (MK_COMB (@lem3177593) (@lem3177592)). Qed.
Lemma lem3177595 : term143 = term146.
Proof. exact (MK_COMB (@lem3177594) (@lem3177589)). Qed.
Lemma lem3177596 : term147.
Proof. exact (@lem1980026 term83 term44 term72 term44). Qed.
Lemma lem3177598 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177599 : term85 = term86.
Proof. exact (@lem3177598 (NUMERAL 0) term45). Qed.
Lemma lem3177600 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177601 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177602 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177601 h1) (fun h1 : term86 = True => @lem3177600)). Qed.
Lemma lem3177603 : term86 = True.
Proof. exact (EQ_MP (@lem3177602) (@lem3177600)). Qed.
Lemma lem3177604 : term85 = True.
Proof. exact (TRANS (@lem3177599) (@lem3177603)). Qed.
Lemma lem3177605 : True = term85.
Proof. exact (SYM (@lem3177604)). Qed.
Lemma lem3177606 : term85.
Proof. exact (EQ_MP (@lem3177605) (@lem0)). Qed.
Lemma lem3177607 : term148.
Proof. exact (@lem3177596 (@lem3177606)). Qed.
Lemma lem3177609 (m : nat) (n : nat) : (term84 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3177610 : term85 = term86.
Proof. exact (@lem3177609 (NUMERAL 0) term45). Qed.
Lemma lem3177611 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177612 (h1 : term87 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3177613 : (term87 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177612 h1) (fun h1 : term86 = True => @lem3177611)). Qed.
Lemma lem3177614 : term86 = True.
Proof. exact (EQ_MP (@lem3177613) (@lem3177611)). Qed.
Lemma lem3177615 : term85 = True.
Proof. exact (TRANS (@lem3177610) (@lem3177614)). Qed.
Lemma lem3177616 : True = term85.
Proof. exact (SYM (@lem3177615)). Qed.
Lemma lem3177617 : term85.
Proof. exact (EQ_MP (@lem3177616) (@lem0)). Qed.
Lemma lem3177618 : term146 = term149.
Proof. exact (@lem3177607 (@lem3177617)). Qed.
Lemma lem3177620 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3177621 : term99 = term100.
Proof. exact (@lem3177620 term45 term45). Qed.
Lemma lem3177622 : (term95 = (BIT1 0)) = (term96 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3177623 : term96 = term45.
Proof. exact (EQ_MP (@lem3177622) (@lem940073)). Qed.
Lemma lem3177624 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3177625 : term94 = term44.
Proof. exact (MK_COMB (@lem3177624) (@lem3177623)). Qed.
Lemma lem3177626 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3177627 : term100 = term72.
Proof. exact (MK_COMB (@lem3177626) (@lem3177625)). Qed.
Lemma lem3177628 : term99 = term72.
Proof. exact (TRANS (@lem3177621) (@lem3177627)). Qed.
Lemma lem3177630 (x : nat) : (term108 x) = term83.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3177631 : term107 = term83.
Proof. exact (@lem3177630 term45). Qed.
Lemma lem3177632 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3177633 : term150 = term144.
Proof. exact (MK_COMB (@lem3177632) (@lem3177631)). Qed.
Lemma lem3177634 : term149 = term143.
Proof. exact (MK_COMB (@lem3177633) (@lem3177628)). Qed.
Lemma lem3177636 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3177637 : term143 = term153.
Proof. exact (@lem3177636 (NUMERAL 0) term45). Qed.
Lemma lem3177638 : term87 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3177639 (h1 : term87 = (BIT1 0)) : (term45 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3177640 : (term87 = (BIT1 0)) = ((term45 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term87 = (BIT1 0) => @lem3177639 h1) (fun h1 : (term45 = (NUMERAL 0)) = False => @lem3177638)). Qed.
Lemma lem3177641 : (term45 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3177640) (@lem3177638)). Qed.
Lemma lem3177642 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3177643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3177644 : term154 = (and True).
Proof. exact (MK_COMB (@lem3177643) (@lem3177642)). Qed.
Lemma lem3177645 : term153 = (True /\ False).
Proof. exact (MK_COMB (@lem3177644) (@lem3177641)). Qed.
Lemma lem3177647 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3177648 : term153 = False.
Proof. exact (TRANS (@lem3177645) (@lem3177647)). Qed.
Lemma lem3177649 : term143 = False.
Proof. exact (TRANS (@lem3177637) (@lem3177648)). Qed.
Lemma lem3177650 : term149 = False.
Proof. exact (TRANS (@lem3177634) (@lem3177649)). Qed.
Lemma lem3177651 : term146 = False.
Proof. exact (TRANS (@lem3177618) (@lem3177650)). Qed.
Lemma lem3177652 : term143 = False.
Proof. exact (TRANS (@lem3177595) (@lem3177651)). Qed.
Lemma lem3177653 : term136 = False.
Proof. exact (TRANS (@lem3177586) (@lem3177652)). Qed.
Lemma lem3177654 (h1 : term136) : False.
Proof. exact (EQ_MP (@lem3177653) (@lem3177583 h1)). Qed.
Lemma lem3177655 (h1 : term142) : False.
Proof. exact (or_elim (@lem3177510 h1) (fun h0 : term136 => @lem3177582 h0) (fun h0 : term136 => @lem3177654 h0)). Qed.
Lemma lem3177657 (h1 : term142) : term142.
Proof. exact (h1). Qed.
Lemma lem3177658 (h1 : term142) : term142 = False.
Proof. exact (prop_ext (fun h2 : term142 => @lem3177655 h1) (fun h2 : False => @lem3177657 h1)). Qed.
Lemma lem3177659 (h1 : term142) : False.
Proof. exact (EQ_MP (@lem3177658 h1) (@lem3177657 h1)). Qed.
Lemma lem3177660 (x : int) (y : int) (h1 : term215 x y) : term215 x y.
Proof. exact (h1). Qed.
Lemma lem3177661 (x : int) (y : int) (h1 : term215 x y) : term142.
Proof. exact (EQ_MP (@lem3177500 x y) (@lem3177660 x y h1)). Qed.
Lemma lem3177662 (x : int) (y : int) (h1 : term215 x y) : term142 = False.
Proof. exact (prop_ext (fun h2 : term142 => @lem3177659 h2) (fun h2 : False => @lem3177661 x y h1)). Qed.
Lemma lem3177663 (x : int) (y : int) (h1 : term215 x y) : False.
Proof. exact (EQ_MP (@lem3177662 x y h1) (@lem3177661 x y h1)). Qed.
Lemma lem3177664 (x : int) (y : int) : term259 x y.
Proof. exact (fun h0 : term215 x y => @lem3177663 x y h0). Qed.
Lemma lem3177665 (x : int) (y : int) : term260 x y.
Proof. exact (@lem1386578 (term261 x y)). Qed.
Lemma lem3177668 (x : int) (y : int) : term261 x y.
Proof. exact (@lem3177665 x y (@lem3177664 x y)). Qed.
Lemma lem3177669 (y : int) (x : int) : (term214 x y) = (term182 y x).
Proof. exact (SYM (@lem3176618 x y)). Qed.
Lemma lem3177670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3177671 (y : int) (x : int) : (term261 x y) = (term179 y x).
Proof. exact (MK_COMB (@lem3177670) (@lem3177669 y x)). Qed.
Lemma lem3177672 (y : int) (x : int) : term179 y x.
Proof. exact (EQ_MP (@lem3177671 y x) (@lem3177668 x y)). Qed.
Lemma lem3177676 (x : real) (n : int) (h1 : (term262 x n) = (term263 x n)) : (term262 x n) = (term263 x n).
Proof. exact (h1). Qed.
Lemma lem3177677 (x : real) (n : int) (h1 : (term262 x n) = (term263 x n)) : (term263 x n) = (term262 x n).
Proof. exact (SYM (@lem3177676 x n h1)). Qed.
Lemma lem3177678 (x : real) (n : int) (h1 : (term263 x n) = (term262 x n)) : (term263 x n) = (term262 x n).
Proof. exact (h1). Qed.
Lemma lem3177679 (x : real) (n : int) (h1 : (term263 x n) = (term262 x n)) : (term262 x n) = (term263 x n).
Proof. exact (SYM (@lem3177678 x n h1)). Qed.
Lemma lem3177680 (x : real) (n : int) : ((term262 x n) = (term263 x n)) = ((term263 x n) = (term262 x n)).
Proof. exact (prop_ext (fun h1 : (term262 x n) = (term263 x n) => @lem3177677 x n h1) (fun h1 : (term263 x n) = (term262 x n) => @lem3177679 x n h1)). Qed.
Lemma lem3177681 (x : real) : (term264 x) = (term265 x).
Proof. exact (fun_ext (fun n : int => @lem3177680 x n)). Qed.
Lemma lem3177682 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3177683 (x : real) : (term266 x) = (term267 x).
Proof. exact (MK_COMB (@lem3177682) (@lem3177681 x)). Qed.
Lemma lem3177684 : term268 = term269.
Proof. exact (fun_ext (fun x : real => @lem3177683 x)). Qed.
Lemma lem3177685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3177686 : term270 = term271.
Proof. exact (MK_COMB (@lem3177685) (@lem3177684)). Qed.
Lemma lem3177687 : term271.
Proof. exact (EQ_MP (@lem3177686) (@lem3173052)). Qed.
Lemma lem3177688 (x : real) : term272 x.
Proof. exact (@lem3177687 x). Qed.
Lemma lem3177689 (x : real) : (term272 x) = (term267 x).
Proof. exact (eq_refl (term272 x)). Qed.
Lemma lem3177690 (x : real) : term267 x.
Proof. exact (EQ_MP (@lem3177689 x) (@lem3177688 x)). Qed.
Lemma lem3177691 (x : real) (n : int) : term273 x n.
Proof. exact (@lem3177690 x n). Qed.
Lemma lem3177692 (x : real) (n : int) : (term273 x n) = ((term263 x n) = (term262 x n)).
Proof. exact (eq_refl (term273 x n)). Qed.
Lemma lem3177694 (x : real) : term274 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem3177695 (x : real) : (term274 x) = ((term275 x) = x).
Proof. exact (eq_refl (term274 x)). Qed.
Lemma lem3177697 (x : real) : term276 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem3177698 (x : real) : (term276 x) = (term277 x).
Proof. exact (eq_refl (term276 x)). Qed.
Lemma lem3177699 (x : real) : term277 x.
Proof. exact (EQ_MP (@lem3177698 x) (@lem3177697 x)). Qed.
Lemma lem3177700 (x : real) (y : real) : term278 x y.
Proof. exact (@lem3177699 x y). Qed.
Lemma lem3177701 (x : real) (y : real) : (term278 x y) = ((term279 x y) = (term280 x y)).
Proof. exact (eq_refl (term278 x y)). Qed.
Lemma lem3177705 (x : real) (y : real) (h1 : ((real_inv x) = (real_inv y)) = (x = y)) : ((real_inv x) = (real_inv y)) = (x = y).
Proof. exact (h1). Qed.
Lemma lem3177706 (x : real) (y : real) (h1 : ((real_inv x) = (real_inv y)) = (x = y)) : (x = y) = ((real_inv x) = (real_inv y)).
Proof. exact (SYM (@lem3177705 x y h1)). Qed.
Lemma lem3177707 (x : real) (y : real) (h1 : (x = y) = ((real_inv x) = (real_inv y))) : (x = y) = ((real_inv x) = (real_inv y)).
Proof. exact (h1). Qed.
Lemma lem3177708 (x : real) (y : real) (h1 : (x = y) = ((real_inv x) = (real_inv y))) : ((real_inv x) = (real_inv y)) = (x = y).
Proof. exact (SYM (@lem3177707 x y h1)). Qed.
Lemma lem3177709 (x : real) (y : real) : (((real_inv x) = (real_inv y)) = (x = y)) = ((x = y) = ((real_inv x) = (real_inv y))).
Proof. exact (prop_ext (fun h1 : ((real_inv x) = (real_inv y)) = (x = y) => @lem3177706 x y h1) (fun h1 : (x = y) = ((real_inv x) = (real_inv y)) => @lem3177708 x y h1)). Qed.
Lemma lem3177710 (x : real) : (term281 x) = (term282 x).
Proof. exact (fun_ext (fun y : real => @lem3177709 x y)). Qed.
Lemma lem3177711 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3177712 (x : real) : (term283 x) = (term284 x).
Proof. exact (MK_COMB (@lem3177711) (@lem3177710 x)). Qed.
Lemma lem3177713 : term285 = term286.
Proof. exact (fun_ext (fun x : real => @lem3177712 x)). Qed.
Lemma lem3177714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3177715 : term287 = term288.
Proof. exact (MK_COMB (@lem3177714) (@lem3177713)). Qed.
Lemma lem3177716 : term288.
Proof. exact (EQ_MP (@lem3177715) (@lem1588850)). Qed.
Lemma lem3177717 (x : real) : term289 x.
Proof. exact (@lem3177716 x). Qed.
Lemma lem3177718 (x : real) : (term289 x) = (term284 x).
Proof. exact (eq_refl (term289 x)). Qed.
Lemma lem3177719 (x : real) : term284 x.
Proof. exact (EQ_MP (@lem3177718 x) (@lem3177717 x)). Qed.
Lemma lem3177720 (x : real) (y : real) : term290 x y.
Proof. exact (@lem3177719 x y). Qed.
Lemma lem3177721 (x : real) (y : real) : (term290 x y) = ((x = y) = ((real_inv x) = (real_inv y))).
Proof. exact (eq_refl (term290 x y)). Qed.
Lemma lem3177723 (P : type1605) (h1 : term291 P) : term291 P.
Proof. exact (h1). Qed.
Lemma lem3177724 (P : type1605) (h1 : term292 P) : term292 P.
Proof. exact (h1). Qed.
Lemma lem3177725 (P : type1605) (h1 : term292 P) (h2 : term291 P) : term293 P.
Proof. exact (@lem3177723 P h2 (@lem3177724 P h1)). Qed.
Lemma lem3177726 (P : type1605) (h1 : term292 P) : term294 P.
Proof. exact (fun h0 : term291 P => @lem3177725 P h1 h0). Qed.
Lemma lem3177727 (P : type1605) (h1 : term291 P) : term291 P.
Proof. exact (h1). Qed.
Lemma lem3177728 (P : type1605) (h1 : term292 P) (h2 : term291 P) : term293 P.
Proof. exact (@lem3177726 P h1 (@lem3177727 P h2)). Qed.
Lemma lem3177729 (P : type1605) (h1 : term291 P) : term291 P.
Proof. exact (fun h0 : term292 P => @lem3177728 P h0 h1). Qed.
Lemma lem3177730 (P : type1605) : term295 P.
Proof. exact (fun h0 : term291 P => @lem3177729 P h0). Qed.
Lemma lem3177732 {A : Type'} (P : Prop) : term296 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem3177733 {A : Type'} (P : Prop) : (term296 A P) = (term297 A P).
Proof. exact (eq_refl (term296 A P)). Qed.
Lemma lem3177734 {A : Type'} (P : Prop) : term297 A P.
Proof. exact (EQ_MP (@lem3177733 A P) (@lem3177732 A P)). Qed.
Lemma lem3177735 {A : Type'} (P : Prop) (Q : A -> Prop) : term298 A P Q.
Proof. exact (@lem3177734 A P Q). Qed.
Lemma lem3177736 {A : Type'} (P : Prop) (Q : A -> Prop) : (term298 A P Q) = ((term299 A P Q) = (term300 A P Q)).
Proof. exact (eq_refl (term298 A P Q)). Qed.
Lemma lem3177738 (x : int) : term301 x.
Proof. exact (@lem2301320 x). Qed.
Lemma lem3177739 (x : int) : (term301 x) = (term302 x).
Proof. exact (eq_refl (term301 x)). Qed.
Lemma lem3177740 (x : int) : term302 x.
Proof. exact (EQ_MP (@lem3177739 x) (@lem3177738 x)). Qed.
Lemma lem3177741 (x : int) (y : int) : term303 x y.
Proof. exact (@lem3177740 x y). Qed.
Lemma lem3177742 (y : int) (x : int) : (term303 x y) = ((int_add x y) = (int_add y x)).
Proof. exact (eq_refl (term303 x y)). Qed.
Lemma lem3177744 (x : real) : term304 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem3177745 (x : real) : (term304 x) = (term305 x).
Proof. exact (eq_refl (term304 x)). Qed.
Lemma lem3177746 (x : real) : term305 x.
Proof. exact (EQ_MP (@lem3177745 x) (@lem3177744 x)). Qed.
Lemma lem3177747 (x : real) (y : real) : term306 x y.
Proof. exact (@lem3177746 x y). Qed.
Lemma lem3177748 (y : real) (x : real) : (term306 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term306 x y)). Qed.
Lemma lem3177750 {A B : Type'} (P : type1413 A B) : term307 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem3177751 {A B : Type'} (P : type1413 A B) : (term307 A B P) = ((term308 A B P) = (term309 A B P)).
Proof. exact (eq_refl (term307 A B P)). Qed.
Lemma lem3177753 (x : real) : term276 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem3177754 (x : real) : (term276 x) = (term277 x).
Proof. exact (eq_refl (term276 x)). Qed.
Lemma lem3177755 (x : real) : term277 x.
Proof. exact (EQ_MP (@lem3177754 x) (@lem3177753 x)). Qed.
Lemma lem3177756 (x : real) (y : real) : term278 x y.
Proof. exact (@lem3177755 x y). Qed.
Lemma lem3177757 (x : real) (y : real) : (term278 x y) = ((term279 x y) = (term280 x y)).
Proof. exact (eq_refl (term278 x y)). Qed.
Lemma lem3177759 (x : real) : term11 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem3177760 (x : real) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem3177761 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem3177760 x) (@lem3177759 x)). Qed.
Lemma lem3177762 (x : real) (m : nat) : term13 x m.
Proof. exact (@lem3177761 x m). Qed.
Lemma lem3177763 (m : nat) (x : real) : (term13 x m) = (term14 m x).
Proof. exact (eq_refl (term13 x m)). Qed.
Lemma lem3177764 (m : nat) (x : real) : term14 m x.
Proof. exact (EQ_MP (@lem3177763 m x) (@lem3177762 x m)). Qed.
Lemma lem3177765 (m : nat) (x : real) (n : nat) : term15 m x n.
Proof. exact (@lem3177764 m x n). Qed.
Lemma lem3177766 (m : nat) (x : real) (n : nat) : (term15 m x n) = ((term16 x m n) = (term17 m x n)).
Proof. exact (eq_refl (term15 m x n)). Qed.
Lemma lem3177768 : term310.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3177769 (x : real) : term311 x.
Proof. exact (@lem3177768 x). Qed.
Lemma lem3177770 (x : real) : (term311 x) = (term312 x).
Proof. exact (eq_refl (term311 x)). Qed.
Lemma lem3177771 (x : real) : term312 x.
Proof. exact (EQ_MP (@lem3177770 x) (@lem3177769 x)). Qed.
Lemma lem3177772 (x : real) (n : nat) : term313 x n.
Proof. exact (@lem3177771 x n). Qed.
Lemma lem3177773 (x : real) (n : nat) : (term313 x n) = ((term314 x n) = (term315 x n)).
Proof. exact (eq_refl (term313 x n)). Qed.
Lemma lem3177775 : term316.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3177776 (x : real) : term7 x.
Proof. exact (@lem3177775 x). Qed.
Lemma lem3177777 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem3177778 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem3177777 x) (@lem3177776 x)). Qed.
Lemma lem3177779 (x : real) (n : nat) : term9 x n.
Proof. exact (@lem3177778 x n). Qed.
Lemma lem3177780 (x : real) (n : nat) : (term9 x n) = ((term10 x n) = (real_pow x n)).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem3177784 (x : int) (y : int) (h1 : (term317 x y) = (term318 x y)) : (term317 x y) = (term318 x y).
Proof. exact (h1). Qed.
Lemma lem3177785 (x : int) (y : int) (h1 : (term317 x y) = (term318 x y)) : (term318 x y) = (term317 x y).
Proof. exact (SYM (@lem3177784 x y h1)). Qed.
Lemma lem3177786 (x : int) (y : int) (h1 : (term318 x y) = (term317 x y)) : (term318 x y) = (term317 x y).
Proof. exact (h1). Qed.
Lemma lem3177787 (x : int) (y : int) (h1 : (term318 x y) = (term317 x y)) : (term317 x y) = (term318 x y).
Proof. exact (SYM (@lem3177786 x y h1)). Qed.
Lemma lem3177788 (x : int) (y : int) : ((term317 x y) = (term318 x y)) = ((term318 x y) = (term317 x y)).
Proof. exact (prop_ext (fun h1 : (term317 x y) = (term318 x y) => @lem3177785 x y h1) (fun h1 : (term318 x y) = (term317 x y) => @lem3177787 x y h1)). Qed.
Lemma lem3177789 (x : int) : (term319 x) = (term320 x).
Proof. exact (fun_ext (fun y : int => @lem3177788 x y)). Qed.
Lemma lem3177790 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3177791 (x : int) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem3177790) (@lem3177789 x)). Qed.
Lemma lem3177792 : term323 = term324.
Proof. exact (fun_ext (fun x : int => @lem3177791 x)). Qed.
Lemma lem3177793 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3177794 : term325 = term326.
Proof. exact (MK_COMB (@lem3177793) (@lem3177792)). Qed.
Lemma lem3177795 : term326.
Proof. exact (EQ_MP (@lem3177794) (@lem2306367)). Qed.
Lemma lem3177796 (m : nat) : term327 m.
Proof. exact (@lem2306816 m). Qed.
Lemma lem3177797 (m : nat) : (term327 m) = (term162 m).
Proof. exact (eq_refl (term327 m)). Qed.
Lemma lem3177798 (m : nat) : term162 m.
Proof. exact (EQ_MP (@lem3177797 m) (@lem3177796 m)). Qed.
Lemma lem3177799 (m : nat) (n : nat) : term328 m n.
Proof. exact (@lem3177798 m n). Qed.
Lemma lem3177800 (m : nat) (n : nat) : (term328 m n) = ((term158 m n) = (term159 m n)).
Proof. exact (eq_refl (term328 m n)). Qed.
Lemma lem3177802 (x : int) : term329 x.
Proof. exact (@lem3177795 x). Qed.
Lemma lem3177803 (x : int) : (term329 x) = (term322 x).
Proof. exact (eq_refl (term329 x)). Qed.
Lemma lem3177804 (x : int) : term322 x.
Proof. exact (EQ_MP (@lem3177803 x) (@lem3177802 x)). Qed.
Lemma lem3177805 (x : int) (y : int) : term330 x y.
Proof. exact (@lem3177804 x y). Qed.
Lemma lem3177806 (x : int) (y : int) : (term330 x y) = ((term318 x y) = (term317 x y)).
Proof. exact (eq_refl (term330 x y)). Qed.
Lemma lem3177808 (P : int -> Prop) : term331 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3177809 (P : int -> Prop) : (term331 P) = ((term332 P) = (term333 P)).
Proof. exact (eq_refl (term331 P)). Qed.
Lemma lem3177822 (P : int -> Prop) : (term332 P) = (term333 P).
Proof. exact (EQ_MP (@lem3177809 P) (@lem3177808 P)). Qed.
Lemma lem3177823 (x : real) : (term334 x) = (term335 x).
Proof. exact (@lem3177822 (term336 x)). Qed.
Lemma lem3177824 (m : int) (x : real) : (term337 x m) = (term338 m x).
Proof. exact (eq_refl (term337 x m)). Qed.
Lemma lem3177825 (x : real) : (term339 x) = (term336 x).
Proof. exact (fun_ext (fun m : int => @lem3177824 m x)). Qed.
Lemma lem3177826 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3177827 (x : real) : (term334 x) = (term340 x).
Proof. exact (MK_COMB (@lem3177826) (@lem3177825 x)). Qed.
Lemma lem3177828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3177829 (x : real) : (term341 x) = (term342 x).
Proof. exact (MK_COMB (@lem3177828) (@lem3177827 x)). Qed.
Lemma lem3177830 (n : nat) (x : real) : (term343 x n) = (term344 n x).
Proof. exact (eq_refl (term343 x n)). Qed.
Lemma lem3177831 (x : real) : (term345 x) = (term346 x).
Proof. exact (fun_ext (fun n : nat => @lem3177830 n x)). Qed.
Lemma lem3177832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3177833 (x : real) : (term347 x) = (term348 x).
Proof. exact (MK_COMB (@lem3177832) (@lem3177831 x)). Qed.
Lemma lem3177834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3177835 (x : real) : (term349 x) = (term350 x).
Proof. exact (MK_COMB (@lem3177834) (@lem3177833 x)). Qed.
Lemma lem3177836 (n : nat) (x : real) : (term351 x n) = (term352 n x).
Proof. exact (eq_refl (term351 x n)). Qed.
Lemma lem3177837 (x : real) : (term353 x) = (term354 x).
Proof. exact (fun_ext (fun n : nat => @lem3177836 n x)). Qed.
Lemma lem3177838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3177839 (x : real) : (term355 x) = (term356 x).
Proof. exact (MK_COMB (@lem3177838) (@lem3177837 x)). Qed.
Lemma lem3177840 (x : real) : (term335 x) = (term357 x).
Proof. exact (MK_COMB (@lem3177835 x) (@lem3177839 x)). Qed.
Lemma lem3177841 (x : real) : ((term334 x) = (term335 x)) = ((term340 x) = (term357 x)).
Proof. exact (MK_COMB (@lem3177829 x) (@lem3177840 x)). Qed.
Lemma lem3177842 (x : real) : (term340 x) = (term357 x).
Proof. exact (EQ_MP (@lem3177841 x) (@lem3177823 x)). Qed.
Lemma lem3177856 (P : int -> Prop) : (term332 P) = (term333 P).
Proof. exact (EQ_MP (@lem3177809 P) (@lem3177808 P)). Qed.
Lemma lem3177857 (n : nat) (x : real) : (term358 n x) = (term359 n x).
Proof. exact (@lem3177856 (term360 n x)). Qed.
Lemma lem3177858 (n : nat) (x : real) (n' : int) : (term361 n x n') = (term362 n x n').
Proof. exact (eq_refl (term361 n x n')). Qed.
Lemma lem3177859 (n : nat) (x : real) : (term363 n x) = (term360 n x).
Proof. exact (fun_ext (fun n' : int => @lem3177858 n x n')). Qed.
Lemma lem3177860 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3177861 (n : nat) (x : real) : (term358 n x) = (term344 n x).
Proof. exact (MK_COMB (@lem3177860) (@lem3177859 n x)). Qed.
Lemma lem3177862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3177863 (n : nat) (x : real) : (term364 n x) = (term365 n x).
Proof. exact (MK_COMB (@lem3177862) (@lem3177861 n x)). Qed.
Lemma lem3177864 (n : nat) (x : real) (n' : nat) : (term366 n x n') = (term367 n x n').
Proof. exact (eq_refl (term366 n x n')). Qed.
Lemma lem3177865 (n : nat) (x : real) : (term368 n x) = (term369 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3177864 n x n')). Qed.
Lemma lem3177866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3177867 (n : nat) (x : real) : (term370 n x) = (term371 n x).
Proof. exact (MK_COMB (@lem3177866) (@lem3177865 n x)). Qed.
Lemma lem3177868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3177869 (n : nat) (x : real) : (term372 n x) = (term373 n x).
Proof. exact (MK_COMB (@lem3177868) (@lem3177867 n x)). Qed.
Lemma lem3177870 (n : nat) (x : real) (n' : nat) : (term374 n x n') = (term375 n x n').
Proof. exact (eq_refl (term374 n x n')). Qed.
Lemma lem3177871 (n : nat) (x : real) : (term376 n x) = (term377 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3177870 n x n')). Qed.
Lemma lem3177872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3177873 (n : nat) (x : real) : (term378 n x) = (term379 n x).
Proof. exact (MK_COMB (@lem3177872) (@lem3177871 n x)). Qed.
Lemma lem3177874 (n : nat) (x : real) : (term359 n x) = (term380 n x).
Proof. exact (MK_COMB (@lem3177869 n x) (@lem3177873 n x)). Qed.
Lemma lem3177875 (n : nat) (x : real) : ((term358 n x) = (term359 n x)) = ((term344 n x) = (term380 n x)).
Proof. exact (MK_COMB (@lem3177863 n x) (@lem3177874 n x)). Qed.
Lemma lem3177876 (n : nat) (x : real) : (term344 n x) = (term380 n x).
Proof. exact (EQ_MP (@lem3177875 n x) (@lem3177857 n x)). Qed.
Lemma lem3177892 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (EQ_MP (@lem3177800 m n) (@lem3177799 m n)). Qed.
Lemma lem3177893 (n : nat) (n' : nat) : (term158 n n') = (term159 n n').
Proof. exact (@lem3177892 n n'). Qed.
Lemma lem3177894 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3177895 (x : real) (n : nat) (n' : nat) : (term381 x n n') = (term382 x n n').
Proof. exact (MK_COMB (@lem3177894 x) (@lem3177893 n n')). Qed.
Lemma lem3177896 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3177897 (x : real) (n : nat) (n' : nat) : (term383 x n n') = (term384 x n n').
Proof. exact (MK_COMB (@lem3177896) (@lem3177895 x n n')). Qed.
Lemma lem3177898 (n : nat) (x : real) (n' : nat) : (term385 n x n') = (term385 n x n').
Proof. exact (eq_refl (term385 n x n')). Qed.
Lemma lem3177899 (n : nat) (x : real) (n' : nat) : ((term381 x n n') = (term385 n x n')) = ((term382 x n n') = (term385 n x n')).
Proof. exact (MK_COMB (@lem3177897 x n n') (@lem3177898 n x n')). Qed.
Lemma lem3177902 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3177903 (n : nat) (x : real) (n' : nat) : (term367 n x n') = (term387 n x n').
Proof. exact (MK_COMB (@lem3177902 x) (@lem3177899 n x n')). Qed.
Lemma lem3177906 (n : nat) (x : real) : (term369 n x) = (term388 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3177903 n x n')). Qed.
Lemma lem3177907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3177908 (n : nat) (x : real) : (term371 n x) = (term389 n x).
Proof. exact (MK_COMB (@lem3177907) (@lem3177906 n x)). Qed.
Lemma lem3177915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3177916 (n : nat) (x : real) : (term373 n x) = (term390 n x).
Proof. exact (MK_COMB (@lem3177915) (@lem3177908 n x)). Qed.
Lemma lem3177929 (n : nat) (x : real) : (term379 n x) = (term379 n x).
Proof. exact (eq_refl (term379 n x)). Qed.
Lemma lem3177930 (n : nat) (x : real) : (term380 n x) = (term391 n x).
Proof. exact (MK_COMB (@lem3177916 n x) (@lem3177929 n x)). Qed.
Lemma lem3177933 (n : nat) (x : real) : (term344 n x) = (term391 n x).
Proof. exact (TRANS (@lem3177876 n x) (@lem3177930 n x)). Qed.
Lemma lem3177934 (x : real) : (term346 x) = (term392 x).
Proof. exact (fun_ext (fun n : nat => @lem3177933 n x)). Qed.
Lemma lem3177935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3177936 (x : real) : (term348 x) = (term393 x).
Proof. exact (MK_COMB (@lem3177935) (@lem3177934 x)). Qed.
Lemma lem3177943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3177944 (x : real) : (term350 x) = (term394 x).
Proof. exact (MK_COMB (@lem3177943) (@lem3177936 x)). Qed.
Lemma lem3177956 (P : int -> Prop) : (term332 P) = (term333 P).
Proof. exact (EQ_MP (@lem3177809 P) (@lem3177808 P)). Qed.
Lemma lem3177957 (n : nat) (x : real) : (term395 n x) = (term396 n x).
Proof. exact (@lem3177956 (term397 n x)). Qed.
Lemma lem3177958 (n : nat) (x : real) (n' : int) : (term398 n x n') = (term399 n x n').
Proof. exact (eq_refl (term398 n x n')). Qed.
Lemma lem3177959 (n : nat) (x : real) : (term400 n x) = (term397 n x).
Proof. exact (fun_ext (fun n' : int => @lem3177958 n x n')). Qed.
Lemma lem3177960 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3177961 (n : nat) (x : real) : (term395 n x) = (term352 n x).
Proof. exact (MK_COMB (@lem3177960) (@lem3177959 n x)). Qed.
Lemma lem3177962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3177963 (n : nat) (x : real) : (term401 n x) = (term402 n x).
Proof. exact (MK_COMB (@lem3177962) (@lem3177961 n x)). Qed.
Lemma lem3177964 (n : nat) (x : real) (n' : nat) : (term403 n x n') = (term404 n x n').
Proof. exact (eq_refl (term403 n x n')). Qed.
Lemma lem3177965 (n : nat) (x : real) : (term405 n x) = (term406 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3177964 n x n')). Qed.
Lemma lem3177966 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3177967 (n : nat) (x : real) : (term407 n x) = (term408 n x).
Proof. exact (MK_COMB (@lem3177966) (@lem3177965 n x)). Qed.
Lemma lem3177968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3177969 (n : nat) (x : real) : (term409 n x) = (term410 n x).
Proof. exact (MK_COMB (@lem3177968) (@lem3177967 n x)). Qed.
Lemma lem3177970 (n : nat) (x : real) (n' : nat) : (term411 n x n') = (term412 n x n').
Proof. exact (eq_refl (term411 n x n')). Qed.
Lemma lem3177971 (n : nat) (x : real) : (term413 n x) = (term414 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3177970 n x n')). Qed.
Lemma lem3177972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3177973 (n : nat) (x : real) : (term415 n x) = (term416 n x).
Proof. exact (MK_COMB (@lem3177972) (@lem3177971 n x)). Qed.
Lemma lem3177974 (n : nat) (x : real) : (term396 n x) = (term417 n x).
Proof. exact (MK_COMB (@lem3177969 n x) (@lem3177973 n x)). Qed.
Lemma lem3177975 (n : nat) (x : real) : ((term395 n x) = (term396 n x)) = ((term352 n x) = (term417 n x)).
Proof. exact (MK_COMB (@lem3177963 n x) (@lem3177974 n x)). Qed.
Lemma lem3177976 (n : nat) (x : real) : (term352 n x) = (term417 n x).
Proof. exact (EQ_MP (@lem3177975 n x) (@lem3177957 n x)). Qed.
Lemma lem3178004 (x : int) (y : int) : (term318 x y) = (term317 x y).
Proof. exact (EQ_MP (@lem3177806 x y) (@lem3177805 x y)). Qed.
Lemma lem3178005 (n : nat) (n' : nat) : (term418 n n') = (term419 n n').
Proof. exact (@lem3178004 (int_of_num n) (int_of_num n')). Qed.
Lemma lem3178007 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (EQ_MP (@lem3177800 m n) (@lem3177799 m n)). Qed.
Lemma lem3178008 (n : nat) (n' : nat) : (term158 n n') = (term159 n n').
Proof. exact (@lem3178007 n n'). Qed.
Lemma lem3178009 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem3178010 (n : nat) (n' : nat) : (term419 n n') = (term420 n n').
Proof. exact (MK_COMB (@lem3178009) (@lem3178008 n n')). Qed.
Lemma lem3178011 (n : nat) (n' : nat) : (term418 n n') = (term420 n n').
Proof. exact (TRANS (@lem3178005 n n') (@lem3178010 n n')). Qed.
Lemma lem3178012 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3178013 (x : real) (n : nat) (n' : nat) : (term421 x n n') = (term422 x n n').
Proof. exact (MK_COMB (@lem3178012 x) (@lem3178011 n n')). Qed.
Lemma lem3178014 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3178015 (x : real) (n : nat) (n' : nat) : (term423 x n n') = (term424 x n n').
Proof. exact (MK_COMB (@lem3178014) (@lem3178013 x n n')). Qed.
Lemma lem3178016 (n : nat) (x : real) (n' : nat) : (term425 n x n') = (term425 n x n').
Proof. exact (eq_refl (term425 n x n')). Qed.
Lemma lem3178017 (n : nat) (x : real) (n' : nat) : ((term421 x n n') = (term425 n x n')) = ((term422 x n n') = (term425 n x n')).
Proof. exact (MK_COMB (@lem3178015 x n n') (@lem3178016 n x n')). Qed.
Lemma lem3178020 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178021 (n : nat) (x : real) (n' : nat) : (term412 n x n') = (term426 n x n').
Proof. exact (MK_COMB (@lem3178020 x) (@lem3178017 n x n')). Qed.
Lemma lem3178024 (n : nat) (x : real) : (term414 n x) = (term427 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3178021 n x n')). Qed.
Lemma lem3178025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178026 (n : nat) (x : real) : (term416 n x) = (term428 n x).
Proof. exact (MK_COMB (@lem3178025) (@lem3178024 n x)). Qed.
Lemma lem3178033 (n : nat) (x : real) : (term410 n x) = (term410 n x).
Proof. exact (eq_refl (term410 n x)). Qed.
Lemma lem3178034 (n : nat) (x : real) : (term417 n x) = (term429 n x).
Proof. exact (MK_COMB (@lem3178033 n x) (@lem3178026 n x)). Qed.
Lemma lem3178037 (n : nat) (x : real) : (term352 n x) = (term429 n x).
Proof. exact (TRANS (@lem3177976 n x) (@lem3178034 n x)). Qed.
Lemma lem3178038 (x : real) : (term354 x) = (term430 x).
Proof. exact (fun_ext (fun n : nat => @lem3178037 n x)). Qed.
Lemma lem3178039 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178040 (x : real) : (term356 x) = (term431 x).
Proof. exact (MK_COMB (@lem3178039) (@lem3178038 x)). Qed.
Lemma lem3178047 (x : real) : (term357 x) = (term432 x).
Proof. exact (MK_COMB (@lem3177944 x) (@lem3178040 x)). Qed.
Lemma lem3178050 (x : real) : (term340 x) = (term432 x).
Proof. exact (TRANS (@lem3177842 x) (@lem3178047 x)). Qed.
Lemma lem3178051 : term433 = term434.
Proof. exact (fun_ext (fun x : real => @lem3178050 x)). Qed.
Lemma lem3178052 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3178053 : term435 = term436.
Proof. exact (MK_COMB (@lem3178052) (@lem3178051)). Qed.
Lemma lem3178060 : term436 = term435.
Proof. exact (SYM (@lem3178053)). Qed.
Lemma lem3178084 (x : real) (n : nat) : (term10 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3177780 x n) (@lem3177779 x n)). Qed.
Lemma lem3178085 (x : real) (n : nat) (n' : nat) : (term382 x n n') = (term16 x n n').
Proof. exact (@lem3178084 x (Nat.add n n')). Qed.
Lemma lem3178087 (m : nat) (x : real) (n : nat) : (term16 x m n) = (term17 m x n).
Proof. exact (EQ_MP (@lem3177766 m x n) (@lem3177765 m x n)). Qed.
Lemma lem3178088 (n : nat) (x : real) (n' : nat) : (term16 x n n') = (term17 n x n').
Proof. exact (@lem3178087 n x n'). Qed.
Lemma lem3178089 (n : nat) (x : real) (n' : nat) : (term382 x n n') = (term17 n x n').
Proof. exact (TRANS (@lem3178085 x n n') (@lem3178088 n x n')). Qed.
Lemma lem3178090 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3178091 (n : nat) (x : real) (n' : nat) : (term384 x n n') = (term437 n x n').
Proof. exact (MK_COMB (@lem3178090) (@lem3178089 n x n')). Qed.
Lemma lem3178093 (x : real) (n : nat) : (term10 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3177780 x n) (@lem3177779 x n)). Qed.
Lemma lem3178094 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3178095 (x : real) (n : nat) : (term438 x n) = (term439 x n).
Proof. exact (MK_COMB (@lem3178094) (@lem3178093 x n)). Qed.
Lemma lem3178097 (x : real) (n : nat) : (term10 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3177780 x n) (@lem3177779 x n)). Qed.
Lemma lem3178098 (x : real) (n' : nat) : (term10 x n') = (real_pow x n').
Proof. exact (@lem3178097 x n'). Qed.
Lemma lem3178099 (n : nat) (x : real) (n' : nat) : (term385 n x n') = (term17 n x n').
Proof. exact (MK_COMB (@lem3178095 x n) (@lem3178098 x n')). Qed.
Lemma lem3178100 (n : nat) (x : real) (n' : nat) : ((term382 x n n') = (term385 n x n')) = ((term17 n x n') = (term17 n x n')).
Proof. exact (MK_COMB (@lem3178091 n x n') (@lem3178099 n x n')). Qed.
Lemma lem3178102 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3178103 (x : real) : (x = x) = True.
Proof. exact (@lem3178102 real x). Qed.
Lemma lem3178104 (n : nat) (x : real) (n' : nat) : ((term17 n x n') = (term17 n x n')) = True.
Proof. exact (@lem3178103 (term17 n x n')). Qed.
Lemma lem3178105 (n : nat) (x : real) (n' : nat) : ((term382 x n n') = (term385 n x n')) = True.
Proof. exact (TRANS (@lem3178100 n x n') (@lem3178104 n x n')). Qed.
Lemma lem3178106 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178107 (n : nat) (n' : nat) (x : real) : (term387 n x n') = (term440 x).
Proof. exact (MK_COMB (@lem3178106 x) (@lem3178105 n x n')). Qed.
Lemma lem3178109 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3178110 (x : real) : (term440 x) = True.
Proof. exact (@lem3178109 (term441 x)). Qed.
Lemma lem3178111 (n : nat) (x : real) (n' : nat) : (term387 n x n') = True.
Proof. exact (TRANS (@lem3178107 n n' x) (@lem3178110 x)). Qed.
Lemma lem3178112 (n : nat) (x : real) : (term388 n x) = term442.
Proof. exact (fun_ext (fun n' : nat => @lem3178111 n x n')). Qed.
Lemma lem3178113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178114 (n : nat) (x : real) : (term389 n x) = term443.
Proof. exact (MK_COMB (@lem3178113) (@lem3178112 n x)). Qed.
Lemma lem3178116 {A : Type'} (t : Prop) : (term444 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3178117 (t : Prop) : (term445 t) = t.
Proof. exact (@lem3178116 nat t). Qed.
Lemma lem3178118 : term443 = True.
Proof. exact (@lem3178117 True). Qed.
Lemma lem3178119 (n : nat) (x : real) : (term389 n x) = True.
Proof. exact (TRANS (@lem3178114 n x) (@lem3178118)). Qed.
Lemma lem3178120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3178121 (n : nat) (x : real) : (term390 n x) = (and True).
Proof. exact (MK_COMB (@lem3178120) (@lem3178119 n x)). Qed.
Lemma lem3178133 (x : real) (n : nat) : (term10 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3177780 x n) (@lem3177779 x n)). Qed.
Lemma lem3178134 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3178135 (x : real) (n : nat) : (term438 x n) = (term439 x n).
Proof. exact (MK_COMB (@lem3178134) (@lem3178133 x n)). Qed.
Lemma lem3178137 (x : real) (n : nat) : (term314 x n) = (term315 x n).
Proof. exact (EQ_MP (@lem3177773 x n) (@lem3177772 x n)). Qed.
Lemma lem3178138 (x : real) (n' : nat) : (term314 x n') = (term315 x n').
Proof. exact (@lem3178137 x n'). Qed.
Lemma lem3178139 (n : nat) (x : real) (n' : nat) : (term446 n x n') = (term447 n x n').
Proof. exact (MK_COMB (@lem3178135 x n) (@lem3178138 x n')). Qed.
Lemma lem3178140 (x : real) (n : nat) (n' : nat) : (term448 x n n') = (term448 x n n').
Proof. exact (eq_refl (term448 x n n')). Qed.
Lemma lem3178141 (n : nat) (x : real) (n' : nat) : ((term449 x n n') = (term446 n x n')) = ((term449 x n n') = (term447 n x n')).
Proof. exact (MK_COMB (@lem3178140 x n n') (@lem3178139 n x n')). Qed.
Lemma lem3178144 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178145 (n : nat) (x : real) (n' : nat) : (term375 n x n') = (term450 n x n').
Proof. exact (MK_COMB (@lem3178144 x) (@lem3178141 n x n')). Qed.
Lemma lem3178148 (n : nat) (x : real) : (term377 n x) = (term451 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3178145 n x n')). Qed.
Lemma lem3178149 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178150 (n : nat) (x : real) : (term379 n x) = (term452 n x).
Proof. exact (MK_COMB (@lem3178149) (@lem3178148 n x)). Qed.
Lemma lem3178155 (n : nat) (x : real) : (term391 n x) = (term453 n x).
Proof. exact (MK_COMB (@lem3178121 n x) (@lem3178150 n x)). Qed.
Lemma lem3178157 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3178158 (n : nat) (x : real) : (term453 n x) = (term452 n x).
Proof. exact (@lem3178157 (term452 n x)). Qed.
Lemma lem3178169 (n : nat) (x : real) : (term391 n x) = (term452 n x).
Proof. exact (TRANS (@lem3178155 n x) (@lem3178158 n x)). Qed.
Lemma lem3178170 (x : real) : (term392 x) = (term454 x).
Proof. exact (fun_ext (fun n : nat => @lem3178169 n x)). Qed.
Lemma lem3178171 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178172 (x : real) : (term393 x) = (term455 x).
Proof. exact (MK_COMB (@lem3178171) (@lem3178170 x)). Qed.
Lemma lem3178177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3178178 (x : real) : (term394 x) = (term456 x).
Proof. exact (MK_COMB (@lem3178177) (@lem3178172 x)). Qed.
Lemma lem3178196 (x : real) (n : nat) : (term314 x n) = (term315 x n).
Proof. exact (EQ_MP (@lem3177773 x n) (@lem3177772 x n)). Qed.
Lemma lem3178197 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3178198 (x : real) (n : nat) : (term457 x n) = (term458 x n).
Proof. exact (MK_COMB (@lem3178197) (@lem3178196 x n)). Qed.
Lemma lem3178200 (x : real) (n : nat) : (term10 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3177780 x n) (@lem3177779 x n)). Qed.
Lemma lem3178201 (x : real) (n' : nat) : (term10 x n') = (real_pow x n').
Proof. exact (@lem3178200 x n'). Qed.
Lemma lem3178202 (n : nat) (x : real) (n' : nat) : (term459 n x n') = (term460 n x n').
Proof. exact (MK_COMB (@lem3178198 x n) (@lem3178201 x n')). Qed.
Lemma lem3178203 (x : real) (n : nat) (n' : nat) : (term461 x n n') = (term461 x n n').
Proof. exact (eq_refl (term461 x n n')). Qed.
Lemma lem3178204 (n : nat) (x : real) (n' : nat) : ((term462 x n n') = (term459 n x n')) = ((term462 x n n') = (term460 n x n')).
Proof. exact (MK_COMB (@lem3178203 x n n') (@lem3178202 n x n')). Qed.
Lemma lem3178207 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178208 (n : nat) (x : real) (n' : nat) : (term404 n x n') = (term463 n x n').
Proof. exact (MK_COMB (@lem3178207 x) (@lem3178204 n x n')). Qed.
Lemma lem3178211 (n : nat) (x : real) : (term406 n x) = (term464 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3178208 n x n')). Qed.
Lemma lem3178212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178213 (n : nat) (x : real) : (term408 n x) = (term465 n x).
Proof. exact (MK_COMB (@lem3178212) (@lem3178211 n x)). Qed.
Lemma lem3178218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3178219 (n : nat) (x : real) : (term410 n x) = (term466 n x).
Proof. exact (MK_COMB (@lem3178218) (@lem3178213 n x)). Qed.
Lemma lem3178231 (x : real) (n : nat) : (term314 x n) = (term315 x n).
Proof. exact (EQ_MP (@lem3177773 x n) (@lem3177772 x n)). Qed.
Lemma lem3178232 (x : real) (n : nat) (n' : nat) : (term422 x n n') = (term467 x n n').
Proof. exact (@lem3178231 x (Nat.add n n')). Qed.
Lemma lem3178234 (m : nat) (x : real) (n : nat) : (term16 x m n) = (term17 m x n).
Proof. exact (EQ_MP (@lem3177766 m x n) (@lem3177765 m x n)). Qed.
Lemma lem3178235 (n : nat) (x : real) (n' : nat) : (term16 x n n') = (term17 n x n').
Proof. exact (@lem3178234 n x n'). Qed.
Lemma lem3178236 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3178237 (n : nat) (x : real) (n' : nat) : (term467 x n n') = (term468 n x n').
Proof. exact (MK_COMB (@lem3178236) (@lem3178235 n x n')). Qed.
Lemma lem3178239 (x : real) (y : real) : (term279 x y) = (term280 x y).
Proof. exact (EQ_MP (@lem3177757 x y) (@lem3177756 x y)). Qed.
Lemma lem3178240 (n : nat) (x : real) (n' : nat) : (term468 n x n') = (term469 n x n').
Proof. exact (@lem3178239 (real_pow x n) (real_pow x n')). Qed.
Lemma lem3178241 (n : nat) (x : real) (n' : nat) : (term467 x n n') = (term469 n x n').
Proof. exact (TRANS (@lem3178237 n x n') (@lem3178240 n x n')). Qed.
Lemma lem3178242 (n : nat) (x : real) (n' : nat) : (term422 x n n') = (term469 n x n').
Proof. exact (TRANS (@lem3178232 x n n') (@lem3178241 n x n')). Qed.
Lemma lem3178243 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3178244 (n : nat) (x : real) (n' : nat) : (term424 x n n') = (term470 n x n').
Proof. exact (MK_COMB (@lem3178243) (@lem3178242 n x n')). Qed.
Lemma lem3178246 (x : real) (n : nat) : (term314 x n) = (term315 x n).
Proof. exact (EQ_MP (@lem3177773 x n) (@lem3177772 x n)). Qed.
Lemma lem3178247 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3178248 (x : real) (n : nat) : (term457 x n) = (term458 x n).
Proof. exact (MK_COMB (@lem3178247) (@lem3178246 x n)). Qed.
Lemma lem3178250 (x : real) (n : nat) : (term314 x n) = (term315 x n).
Proof. exact (EQ_MP (@lem3177773 x n) (@lem3177772 x n)). Qed.
Lemma lem3178251 (x : real) (n' : nat) : (term314 x n') = (term315 x n').
Proof. exact (@lem3178250 x n'). Qed.
Lemma lem3178252 (n : nat) (x : real) (n' : nat) : (term425 n x n') = (term469 n x n').
Proof. exact (MK_COMB (@lem3178248 x n) (@lem3178251 x n')). Qed.
Lemma lem3178253 (n : nat) (x : real) (n' : nat) : ((term422 x n n') = (term425 n x n')) = ((term469 n x n') = (term469 n x n')).
Proof. exact (MK_COMB (@lem3178244 n x n') (@lem3178252 n x n')). Qed.
Lemma lem3178255 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3178256 (x : real) : (x = x) = True.
Proof. exact (@lem3178255 real x). Qed.
Lemma lem3178257 (n : nat) (x : real) (n' : nat) : ((term469 n x n') = (term469 n x n')) = True.
Proof. exact (@lem3178256 (term469 n x n')). Qed.
Lemma lem3178258 (n : nat) (x : real) (n' : nat) : ((term422 x n n') = (term425 n x n')) = True.
Proof. exact (TRANS (@lem3178253 n x n') (@lem3178257 n x n')). Qed.
Lemma lem3178259 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178260 (n : nat) (n' : nat) (x : real) : (term426 n x n') = (term440 x).
Proof. exact (MK_COMB (@lem3178259 x) (@lem3178258 n x n')). Qed.
Lemma lem3178262 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3178263 (x : real) : (term440 x) = True.
Proof. exact (@lem3178262 (term441 x)). Qed.
Lemma lem3178264 (n : nat) (x : real) (n' : nat) : (term426 n x n') = True.
Proof. exact (TRANS (@lem3178260 n n' x) (@lem3178263 x)). Qed.
Lemma lem3178265 (n : nat) (x : real) : (term427 n x) = term442.
Proof. exact (fun_ext (fun n' : nat => @lem3178264 n x n')). Qed.
Lemma lem3178266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178267 (n : nat) (x : real) : (term428 n x) = term443.
Proof. exact (MK_COMB (@lem3178266) (@lem3178265 n x)). Qed.
Lemma lem3178269 {A : Type'} (t : Prop) : (term444 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3178270 (t : Prop) : (term445 t) = t.
Proof. exact (@lem3178269 nat t). Qed.
Lemma lem3178271 : term443 = True.
Proof. exact (@lem3178270 True). Qed.
Lemma lem3178272 (n : nat) (x : real) : (term428 n x) = True.
Proof. exact (TRANS (@lem3178267 n x) (@lem3178271)). Qed.
Lemma lem3178273 (n : nat) (x : real) : (term429 n x) = (term471 n x).
Proof. exact (MK_COMB (@lem3178219 n x) (@lem3178272 n x)). Qed.
Lemma lem3178275 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3178276 (n : nat) (x : real) : (term471 n x) = (term465 n x).
Proof. exact (@lem3178275 (term465 n x)). Qed.
Lemma lem3178287 (n : nat) (x : real) : (term429 n x) = (term465 n x).
Proof. exact (TRANS (@lem3178273 n x) (@lem3178276 n x)). Qed.
Lemma lem3178288 (x : real) : (term430 x) = (term472 x).
Proof. exact (fun_ext (fun n : nat => @lem3178287 n x)). Qed.
Lemma lem3178289 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178290 (x : real) : (term431 x) = (term473 x).
Proof. exact (MK_COMB (@lem3178289) (@lem3178288 x)). Qed.
Lemma lem3178295 (x : real) : (term432 x) = (term474 x).
Proof. exact (MK_COMB (@lem3178178 x) (@lem3178290 x)). Qed.
Lemma lem3178298 : term434 = term475.
Proof. exact (fun_ext (fun x : real => @lem3178295 x)). Qed.
Lemma lem3178299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3178300 : term436 = term476.
Proof. exact (MK_COMB (@lem3178299) (@lem3178298)). Qed.
Lemma lem3178305 : term476 = term436.
Proof. exact (SYM (@lem3178300)). Qed.
Lemma lem3178307 {A B : Type'} (P : type1413 A B) : (term308 A B P) = (term309 A B P).
Proof. exact (EQ_MP (@lem3177751 A B P) (@lem3177750 A B P)). Qed.
Lemma lem3178308 (P : type1605) : (term293 P) = (term477 P).
Proof. exact (@lem3178307 nat nat P). Qed.
Lemma lem3178309 (x : real) : (term478 x) = (term479 x).
Proof. exact (@lem3178308 (term480 x)). Qed.
Lemma lem3178310 (n : nat) (x : real) : (term481 x n) = (term451 n x).
Proof. exact (eq_refl (term481 x n)). Qed.
Lemma lem3178311 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem3178312 (n : nat) (x : real) (n' : nat) : (term482 x n n') = (term483 n x n').
Proof. exact (MK_COMB (@lem3178310 n x) (@lem3178311 n')). Qed.
Lemma lem3178313 (n : nat) (x : real) (n' : nat) : (term483 n x n') = (term450 n x n').
Proof. exact (eq_refl (term483 n x n')). Qed.
Lemma lem3178314 (n : nat) (x : real) (n' : nat) : (term482 x n n') = (term450 n x n').
Proof. exact (TRANS (@lem3178312 n x n') (@lem3178313 n x n')). Qed.
Lemma lem3178315 (n : nat) (x : real) : (term484 x n) = (term451 n x).
Proof. exact (fun_ext (fun n' : nat => @lem3178314 n x n')). Qed.
Lemma lem3178316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178317 (n : nat) (x : real) : (term485 x n) = (term452 n x).
Proof. exact (MK_COMB (@lem3178316) (@lem3178315 n x)). Qed.
Lemma lem3178318 (x : real) : (term486 x) = (term454 x).
Proof. exact (fun_ext (fun n : nat => @lem3178317 n x)). Qed.
Lemma lem3178319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178320 (x : real) : (term478 x) = (term455 x).
Proof. exact (MK_COMB (@lem3178319) (@lem3178318 x)). Qed.
Lemma lem3178321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178322 (x : real) : (term487 x) = (term488 x).
Proof. exact (MK_COMB (@lem3178321) (@lem3178320 x)). Qed.
Lemma lem3178323 (n : nat) (x : real) : (term481 x n) = (term451 n x).
Proof. exact (eq_refl (term481 x n)). Qed.
Lemma lem3178324 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem3178325 (n : nat) (x : real) (n' : nat) : (term482 x n n') = (term483 n x n').
Proof. exact (MK_COMB (@lem3178323 n x) (@lem3178324 n')). Qed.
Lemma lem3178326 (n : nat) (x : real) (n' : nat) : (term483 n x n') = (term450 n x n').
Proof. exact (eq_refl (term483 n x n')). Qed.
Lemma lem3178327 (n : nat) (x : real) (n' : nat) : (term482 x n n') = (term450 n x n').
Proof. exact (TRANS (@lem3178325 n x n') (@lem3178326 n x n')). Qed.
Lemma lem3178328 (x : real) (n' : nat) : (term489 x n') = (term490 x n').
Proof. exact (fun_ext (fun n : nat => @lem3178327 n x n')). Qed.
Lemma lem3178329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178330 (x : real) (n' : nat) : (term491 x n') = (term492 x n').
Proof. exact (MK_COMB (@lem3178329) (@lem3178328 x n')). Qed.
Lemma lem3178331 (x : real) : (term493 x) = (term494 x).
Proof. exact (fun_ext (fun n' : nat => @lem3178330 x n')). Qed.
Lemma lem3178332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178333 (x : real) : (term479 x) = (term495 x).
Proof. exact (MK_COMB (@lem3178332) (@lem3178331 x)). Qed.
Lemma lem3178334 (x : real) : ((term478 x) = (term479 x)) = ((term455 x) = (term495 x)).
Proof. exact (MK_COMB (@lem3178322 x) (@lem3178333 x)). Qed.
Lemma lem3178335 (x : real) : (term455 x) = (term495 x).
Proof. exact (EQ_MP (@lem3178334 x) (@lem3178309 x)). Qed.
Lemma lem3178336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3178337 (x : real) : (term456 x) = (term496 x).
Proof. exact (MK_COMB (@lem3178336) (@lem3178335 x)). Qed.
Lemma lem3178338 (x : real) : (term473 x) = (term473 x).
Proof. exact (eq_refl (term473 x)). Qed.
Lemma lem3178339 (x : real) : (term474 x) = (term497 x).
Proof. exact (MK_COMB (@lem3178337 x) (@lem3178338 x)). Qed.
Lemma lem3178340 (x : real) : (term497 x) = (term474 x).
Proof. exact (SYM (@lem3178339 x)). Qed.
Lemma lem3178342 (y : int) (x : int) : (int_add x y) = (int_add y x).
Proof. exact (EQ_MP (@lem3177742 y x) (@lem3177741 x y)). Qed.
Lemma lem3178343 (n' : nat) (n : nat) : (term498 n n') = (term499 n' n).
Proof. exact (@lem3178342 (term500 n') (int_of_num n)). Qed.
Lemma lem3178344 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3178345 (x : real) (n' : nat) (n : nat) : (term449 x n n') = (term462 x n' n).
Proof. exact (MK_COMB (@lem3178344 x) (@lem3178343 n' n)). Qed.
Lemma lem3178346 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3178347 (x : real) (n' : nat) (n : nat) : (term448 x n n') = (term461 x n' n).
Proof. exact (MK_COMB (@lem3178346) (@lem3178345 x n' n)). Qed.
Lemma lem3178349 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem3177748 y x) (@lem3177747 x y)). Qed.
Lemma lem3178350 (n' : nat) (x : real) (n : nat) : (term447 n x n') = (term460 n' x n).
Proof. exact (@lem3178349 (term315 x n') (real_pow x n)). Qed.
Lemma lem3178351 (n' : nat) (x : real) (n : nat) : ((term449 x n n') = (term447 n x n')) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (MK_COMB (@lem3178347 x n' n) (@lem3178350 n' x n)). Qed.
Lemma lem3178352 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178353 (n' : nat) (x : real) (n : nat) : (term450 n x n') = (term463 n' x n).
Proof. exact (MK_COMB (@lem3178352 x) (@lem3178351 n' x n)). Qed.
Lemma lem3178354 (n' : nat) (x : real) : (term490 x n') = (term464 n' x).
Proof. exact (fun_ext (fun n : nat => @lem3178353 n' x n)). Qed.
Lemma lem3178355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178356 (n' : nat) (x : real) : (term492 x n') = (term465 n' x).
Proof. exact (MK_COMB (@lem3178355) (@lem3178354 n' x)). Qed.
Lemma lem3178357 (x : real) : (term494 x) = (term472 x).
Proof. exact (fun_ext (fun n' : nat => @lem3178356 n' x)). Qed.
Lemma lem3178358 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178359 (x : real) : (term495 x) = (term473 x).
Proof. exact (MK_COMB (@lem3178358) (@lem3178357 x)). Qed.
Lemma lem3178360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3178361 (x : real) : (term496 x) = (term501 x).
Proof. exact (MK_COMB (@lem3178360) (@lem3178359 x)). Qed.
Lemma lem3178362 (x : real) : (term473 x) = (term473 x).
Proof. exact (eq_refl (term473 x)). Qed.
Lemma lem3178363 (x : real) : (term497 x) = (term502 x).
Proof. exact (MK_COMB (@lem3178361 x) (@lem3178362 x)). Qed.
Lemma lem3178364 (x : real) : (term502 x) = (term497 x).
Proof. exact (SYM (@lem3178363 x)). Qed.
Lemma lem3178366 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem3178367 (x : real) : (term502 x) = (term473 x).
Proof. exact (@lem3178366 (term473 x)). Qed.
Lemma lem3178370 (x : real) : (term503 x) = (term503 x).
Proof. exact (eq_refl (term503 x)). Qed.
Lemma lem3178371 (x : real) : (term503 x) = ((term502 x) = (term473 x)).
Proof. exact (eq_refl (term503 x)). Qed.
Lemma lem3178372 (x : real) : (term504 x) = (term504 x).
Proof. exact (eq_refl (term504 x)). Qed.
Lemma lem3178373 (x : real) : ((term503 x) = (term503 x)) = ((term503 x) = ((term502 x) = (term473 x))).
Proof. exact (MK_COMB (@lem3178372 x) (@lem3178371 x)). Qed.
Lemma lem3178374 (x : real) : (term503 x) = ((term502 x) = (term473 x)).
Proof. exact (eq_refl (term503 x)). Qed.
Lemma lem3178375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178376 (x : real) : (term504 x) = (term505 x).
Proof. exact (MK_COMB (@lem3178375) (@lem3178374 x)). Qed.
Lemma lem3178377 (x : real) : ((term502 x) = (term473 x)) = ((term502 x) = (term473 x)).
Proof. exact (eq_refl ((term502 x) = (term473 x))). Qed.
Lemma lem3178378 (x : real) : ((term503 x) = ((term502 x) = (term473 x))) = (((term502 x) = (term473 x)) = ((term502 x) = (term473 x))).
Proof. exact (MK_COMB (@lem3178376 x) (@lem3178377 x)). Qed.
Lemma lem3178379 (x : real) : ((term503 x) = (term503 x)) = (((term502 x) = (term473 x)) = ((term502 x) = (term473 x))).
Proof. exact (TRANS (@lem3178373 x) (@lem3178378 x)). Qed.
Lemma lem3178380 (x : real) : ((term502 x) = (term473 x)) = ((term502 x) = (term473 x)).
Proof. exact (EQ_MP (@lem3178379 x) (@lem3178370 x)). Qed.
Lemma lem3178381 (x : real) : (term502 x) = (term473 x).
Proof. exact (EQ_MP (@lem3178380 x) (@lem3178367 x)). Qed.
Lemma lem3178387 {A : Type'} (P : Prop) (Q : A -> Prop) : (term299 A P Q) = (term300 A P Q).
Proof. exact (EQ_MP (@lem3177736 A P Q) (@lem3177735 A P Q)). Qed.
Lemma lem3178388 (P : Prop) (Q : nat -> Prop) : (term506 P Q) = (term507 P Q).
Proof. exact (@lem3178387 nat P Q). Qed.
Lemma lem3178389 (n' : nat) (x : real) : (term508 n' x) = (term509 n' x).
Proof. exact (@lem3178388 (term441 x) (term510 n' x)). Qed.
Lemma lem3178390 (n' : nat) (x : real) (n : nat) : (term511 n' x n) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (eq_refl (term511 n' x n)). Qed.
Lemma lem3178391 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178392 (n' : nat) (x : real) (n : nat) : (term512 n' x n) = (term463 n' x n).
Proof. exact (MK_COMB (@lem3178391 x) (@lem3178390 n' x n)). Qed.
Lemma lem3178393 (n' : nat) (x : real) : (term513 n' x) = (term464 n' x).
Proof. exact (fun_ext (fun n : nat => @lem3178392 n' x n)). Qed.
Lemma lem3178394 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178395 (n' : nat) (x : real) : (term508 n' x) = (term465 n' x).
Proof. exact (MK_COMB (@lem3178394) (@lem3178393 n' x)). Qed.
Lemma lem3178396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178397 (n' : nat) (x : real) : (term514 n' x) = (term515 n' x).
Proof. exact (MK_COMB (@lem3178396) (@lem3178395 n' x)). Qed.
Lemma lem3178398 (n' : nat) (x : real) (n : nat) : (term511 n' x n) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (eq_refl (term511 n' x n)). Qed.
Lemma lem3178399 (n' : nat) (x : real) : (term516 n' x) = (term510 n' x).
Proof. exact (fun_ext (fun n : nat => @lem3178398 n' x n)). Qed.
Lemma lem3178400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178401 (n' : nat) (x : real) : (term517 n' x) = (term518 n' x).
Proof. exact (MK_COMB (@lem3178400) (@lem3178399 n' x)). Qed.
Lemma lem3178402 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178403 (n' : nat) (x : real) : (term509 n' x) = (term519 n' x).
Proof. exact (MK_COMB (@lem3178402 x) (@lem3178401 n' x)). Qed.
Lemma lem3178404 (n' : nat) (x : real) : ((term508 n' x) = (term509 n' x)) = ((term465 n' x) = (term519 n' x)).
Proof. exact (MK_COMB (@lem3178397 n' x) (@lem3178403 n' x)). Qed.
Lemma lem3178405 (n' : nat) (x : real) : (term465 n' x) = (term519 n' x).
Proof. exact (EQ_MP (@lem3178404 n' x) (@lem3178389 n' x)). Qed.
Lemma lem3178416 (x : real) : (term472 x) = (term520 x).
Proof. exact (fun_ext (fun n' : nat => @lem3178405 n' x)). Qed.
Lemma lem3178417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178418 (x : real) : (term473 x) = (term521 x).
Proof. exact (MK_COMB (@lem3178417) (@lem3178416 x)). Qed.
Lemma lem3178420 {A : Type'} (P : Prop) (Q : A -> Prop) : (term299 A P Q) = (term300 A P Q).
Proof. exact (EQ_MP (@lem3177736 A P Q) (@lem3177735 A P Q)). Qed.
Lemma lem3178421 (P : Prop) (Q : nat -> Prop) : (term506 P Q) = (term507 P Q).
Proof. exact (@lem3178420 nat P Q). Qed.
Lemma lem3178422 (x : real) : (term522 x) = (term523 x).
Proof. exact (@lem3178421 (term441 x) (term524 x)). Qed.
Lemma lem3178423 (n' : nat) (x : real) : (term525 x n') = (term518 n' x).
Proof. exact (eq_refl (term525 x n')). Qed.
Lemma lem3178424 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178425 (n' : nat) (x : real) : (term526 x n') = (term519 n' x).
Proof. exact (MK_COMB (@lem3178424 x) (@lem3178423 n' x)). Qed.
Lemma lem3178426 (x : real) : (term527 x) = (term520 x).
Proof. exact (fun_ext (fun n' : nat => @lem3178425 n' x)). Qed.
Lemma lem3178427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178428 (x : real) : (term522 x) = (term521 x).
Proof. exact (MK_COMB (@lem3178427) (@lem3178426 x)). Qed.
Lemma lem3178429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178430 (x : real) : (term528 x) = (term529 x).
Proof. exact (MK_COMB (@lem3178429) (@lem3178428 x)). Qed.
Lemma lem3178431 (n' : nat) (x : real) : (term525 x n') = (term518 n' x).
Proof. exact (eq_refl (term525 x n')). Qed.
Lemma lem3178432 (x : real) : (term530 x) = (term524 x).
Proof. exact (fun_ext (fun n' : nat => @lem3178431 n' x)). Qed.
Lemma lem3178433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178434 (x : real) : (term531 x) = (term532 x).
Proof. exact (MK_COMB (@lem3178433) (@lem3178432 x)). Qed.
Lemma lem3178435 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem3178436 (x : real) : (term523 x) = (term533 x).
Proof. exact (MK_COMB (@lem3178435 x) (@lem3178434 x)). Qed.
Lemma lem3178437 (x : real) : ((term522 x) = (term523 x)) = ((term521 x) = (term533 x)).
Proof. exact (MK_COMB (@lem3178430 x) (@lem3178436 x)). Qed.
Lemma lem3178438 (x : real) : (term521 x) = (term533 x).
Proof. exact (EQ_MP (@lem3178437 x) (@lem3178422 x)). Qed.
Lemma lem3178453 (x : real) : (term473 x) = (term533 x).
Proof. exact (TRANS (@lem3178418 x) (@lem3178438 x)). Qed.
Lemma lem3178454 (x : real) : (term502 x) = (term533 x).
Proof. exact (TRANS (@lem3178381 x) (@lem3178453 x)). Qed.
Lemma lem3178455 (x : real) : (term533 x) = (term502 x).
Proof. exact (SYM (@lem3178454 x)). Qed.
Lemma lem3178456 (x : real) (h1 : term441 x) : term441 x.
Proof. exact (h1). Qed.
Lemma lem3178458 (P : type1605) : term291 P.
Proof. exact (@lem3177730 P (@lem109466 P)). Qed.
Lemma lem3178459 (x : real) : term534 x.
Proof. exact (@lem3178458 (term535 x)). Qed.
Lemma lem3178460 (n' : nat) (x : real) : (term536 x n') = (term510 n' x).
Proof. exact (eq_refl (term536 x n')). Qed.
Lemma lem3178461 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3178462 (n' : nat) (x : real) (n : nat) : (term537 x n' n) = (term511 n' x n).
Proof. exact (MK_COMB (@lem3178460 n' x) (@lem3178461 n)). Qed.
Lemma lem3178463 (n' : nat) (x : real) (n : nat) : (term511 n' x n) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (eq_refl (term511 n' x n)). Qed.
Lemma lem3178464 (n' : nat) (x : real) (n : nat) : (term537 x n' n) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (TRANS (@lem3178462 n' x n) (@lem3178463 n' x n)). Qed.
Lemma lem3178465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178466 (n' : nat) (x : real) (n : nat) : (term538 x n' n) = (term539 n' x n).
Proof. exact (MK_COMB (@lem3178465) (@lem3178464 n' x n)). Qed.
Lemma lem3178467 (n : nat) (x : real) : (term536 x n) = (term510 n x).
Proof. exact (eq_refl (term536 x n)). Qed.
Lemma lem3178468 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem3178469 (n : nat) (x : real) (n' : nat) : (term537 x n n') = (term511 n x n').
Proof. exact (MK_COMB (@lem3178467 n x) (@lem3178468 n')). Qed.
Lemma lem3178470 (n : nat) (x : real) (n' : nat) : (term511 n x n') = ((term462 x n n') = (term460 n x n')).
Proof. exact (eq_refl (term511 n x n')). Qed.
Lemma lem3178471 (n : nat) (x : real) (n' : nat) : (term537 x n n') = ((term462 x n n') = (term460 n x n')).
Proof. exact (TRANS (@lem3178469 n x n') (@lem3178470 n x n')). Qed.
Lemma lem3178472 (n : nat) (x : real) (n' : nat) : ((term537 x n' n) = (term537 x n n')) = (((term462 x n' n) = (term460 n' x n)) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (MK_COMB (@lem3178466 n' x n) (@lem3178471 n x n')). Qed.
Lemma lem3178473 (x : real) (n' : nat) : (term540 x n') = (term541 x n').
Proof. exact (fun_ext (fun n : nat => @lem3178472 n x n')). Qed.
Lemma lem3178474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178475 (x : real) (n' : nat) : (term542 x n') = (term543 x n').
Proof. exact (MK_COMB (@lem3178474) (@lem3178473 x n')). Qed.
Lemma lem3178476 (x : real) : (term544 x) = (term545 x).
Proof. exact (fun_ext (fun n' : nat => @lem3178475 x n')). Qed.
Lemma lem3178477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178478 (x : real) : (term546 x) = (term547 x).
Proof. exact (MK_COMB (@lem3178477) (@lem3178476 x)). Qed.
Lemma lem3178479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3178480 (x : real) : (term548 x) = (term549 x).
Proof. exact (MK_COMB (@lem3178479) (@lem3178478 x)). Qed.
Lemma lem3178481 (n' : nat) (x : real) : (term536 x n') = (term510 n' x).
Proof. exact (eq_refl (term536 x n')). Qed.
Lemma lem3178482 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3178483 (n' : nat) (x : real) (n : nat) : (term537 x n' n) = (term511 n' x n).
Proof. exact (MK_COMB (@lem3178481 n' x) (@lem3178482 n)). Qed.
Lemma lem3178484 (n' : nat) (x : real) (n : nat) : (term511 n' x n) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (eq_refl (term511 n' x n)). Qed.
Lemma lem3178485 (n' : nat) (x : real) (n : nat) : (term537 x n' n) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (TRANS (@lem3178483 n' x n) (@lem3178484 n' x n)). Qed.
Lemma lem3178486 (n' : nat) (n : nat) : (term550 n' n) = (term550 n' n).
Proof. exact (eq_refl (term550 n' n)). Qed.
Lemma lem3178487 (n' : nat) (x : real) (n : nat) : (term551 x n' n) = (term552 n' x n).
Proof. exact (MK_COMB (@lem3178486 n' n) (@lem3178485 n' x n)). Qed.
Lemma lem3178488 (n' : nat) (x : real) : (term553 x n') = (term554 n' x).
Proof. exact (fun_ext (fun n : nat => @lem3178487 n' x n)). Qed.
Lemma lem3178489 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178490 (n' : nat) (x : real) : (term555 x n') = (term556 n' x).
Proof. exact (MK_COMB (@lem3178489) (@lem3178488 n' x)). Qed.
Lemma lem3178491 (x : real) : (term557 x) = (term558 x).
Proof. exact (fun_ext (fun n' : nat => @lem3178490 n' x)). Qed.
Lemma lem3178492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178493 (x : real) : (term559 x) = (term560 x).
Proof. exact (MK_COMB (@lem3178492) (@lem3178491 x)). Qed.
Lemma lem3178494 (x : real) : (term561 x) = (term562 x).
Proof. exact (MK_COMB (@lem3178480 x) (@lem3178493 x)). Qed.
Lemma lem3178495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3178496 (x : real) : (term563 x) = (term564 x).
Proof. exact (MK_COMB (@lem3178495) (@lem3178494 x)). Qed.
Lemma lem3178497 (n' : nat) (x : real) : (term536 x n') = (term510 n' x).
Proof. exact (eq_refl (term536 x n')). Qed.
Lemma lem3178498 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3178499 (n' : nat) (x : real) (n : nat) : (term537 x n' n) = (term511 n' x n).
Proof. exact (MK_COMB (@lem3178497 n' x) (@lem3178498 n)). Qed.
Lemma lem3178500 (n' : nat) (x : real) (n : nat) : (term511 n' x n) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (eq_refl (term511 n' x n)). Qed.
Lemma lem3178501 (n' : nat) (x : real) (n : nat) : (term537 x n' n) = ((term462 x n' n) = (term460 n' x n)).
Proof. exact (TRANS (@lem3178499 n' x n) (@lem3178500 n' x n)). Qed.
Lemma lem3178502 (n' : nat) (x : real) : (term565 x n') = (term510 n' x).
Proof. exact (fun_ext (fun n : nat => @lem3178501 n' x n)). Qed.
Lemma lem3178503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178504 (n' : nat) (x : real) : (term566 x n') = (term518 n' x).
Proof. exact (MK_COMB (@lem3178503) (@lem3178502 n' x)). Qed.
Lemma lem3178505 (x : real) : (term567 x) = (term524 x).
Proof. exact (fun_ext (fun n' : nat => @lem3178504 n' x)). Qed.
Lemma lem3178506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178507 (x : real) : (term568 x) = (term532 x).
Proof. exact (MK_COMB (@lem3178506) (@lem3178505 x)). Qed.
Lemma lem3178508 (x : real) : (term534 x) = (term569 x).
Proof. exact (MK_COMB (@lem3178496 x) (@lem3178507 x)). Qed.
Lemma lem3178509 (x : real) : term569 x.
Proof. exact (EQ_MP (@lem3178508 x) (@lem3178459 x)). Qed.
Lemma lem3178511 (x : real) (y : real) : (x = y) = ((real_inv x) = (real_inv y)).
Proof. exact (EQ_MP (@lem3177721 x y) (@lem3177720 x y)). Qed.
Lemma lem3178512 (n' : nat) (x : real) (n : nat) : ((term462 x n' n) = (term460 n' x n)) = ((term570 x n' n) = (term571 n' x n)).
Proof. exact (@lem3178511 (term462 x n' n) (term460 n' x n)). Qed.
Lemma lem3178513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178514 (n' : nat) (x : real) (n : nat) : (term539 n' x n) = (term572 n' x n).
Proof. exact (MK_COMB (@lem3178513) (@lem3178512 n' x n)). Qed.
Lemma lem3178515 (n : nat) (x : real) (n' : nat) : ((term462 x n n') = (term460 n x n')) = ((term462 x n n') = (term460 n x n')).
Proof. exact (eq_refl ((term462 x n n') = (term460 n x n'))). Qed.
Lemma lem3178516 (n : nat) (x : real) (n' : nat) : (((term462 x n' n) = (term460 n' x n)) = ((term462 x n n') = (term460 n x n'))) = (((term570 x n' n) = (term571 n' x n)) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (MK_COMB (@lem3178514 n' x n) (@lem3178515 n x n')). Qed.
Lemma lem3178517 (n : nat) (x : real) (n' : nat) : (((term570 x n' n) = (term571 n' x n)) = ((term462 x n n') = (term460 n x n'))) = (((term462 x n' n) = (term460 n' x n)) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (SYM (@lem3178516 n x n')). Qed.
Lemma lem3178523 (x : real) (n : int) : (term263 x n) = (term262 x n).
Proof. exact (EQ_MP (@lem3177692 x n) (@lem3177691 x n)). Qed.
Lemma lem3178524 (x : real) (n' : nat) (n : nat) : (term570 x n' n) = (term573 x n' n).
Proof. exact (@lem3178523 x (term499 n' n)). Qed.
Lemma lem3178525 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3178526 (x : real) (n' : nat) (n : nat) : (term574 x n' n) = (term575 x n' n).
Proof. exact (MK_COMB (@lem3178525) (@lem3178524 x n' n)). Qed.
Lemma lem3178528 (x : real) (y : real) : (term279 x y) = (term280 x y).
Proof. exact (EQ_MP (@lem3177701 x y) (@lem3177700 x y)). Qed.
Lemma lem3178529 (n' : nat) (x : real) (n : nat) : (term571 n' x n) = (term576 n' x n).
Proof. exact (@lem3178528 (term315 x n') (real_pow x n)). Qed.
Lemma lem3178531 (x : real) : (term275 x) = x.
Proof. exact (EQ_MP (@lem3177695 x) (@lem3177694 x)). Qed.
Lemma lem3178532 (x : real) (n' : nat) : (term577 x n') = (real_pow x n').
Proof. exact (@lem3178531 (real_pow x n')). Qed.
Lemma lem3178533 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3178534 (x : real) (n' : nat) : (term578 x n') = (term439 x n').
Proof. exact (MK_COMB (@lem3178533) (@lem3178532 x n')). Qed.
Lemma lem3178535 (x : real) (n : nat) : (term315 x n) = (term315 x n).
Proof. exact (eq_refl (term315 x n)). Qed.
Lemma lem3178536 (n' : nat) (x : real) (n : nat) : (term576 n' x n) = (term447 n' x n).
Proof. exact (MK_COMB (@lem3178534 x n') (@lem3178535 x n)). Qed.
Lemma lem3178537 (n' : nat) (x : real) (n : nat) : (term571 n' x n) = (term447 n' x n).
Proof. exact (TRANS (@lem3178529 n' x n) (@lem3178536 n' x n)). Qed.
Lemma lem3178538 (n' : nat) (x : real) (n : nat) : ((term570 x n' n) = (term571 n' x n)) = ((term573 x n' n) = (term447 n' x n)).
Proof. exact (MK_COMB (@lem3178526 x n' n) (@lem3178537 n' x n)). Qed.
Lemma lem3178541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178542 (n' : nat) (x : real) (n : nat) : (term572 n' x n) = (term579 n' x n).
Proof. exact (MK_COMB (@lem3178541) (@lem3178538 n' x n)). Qed.
Lemma lem3178545 (n : nat) (x : real) (n' : nat) : ((term462 x n n') = (term460 n x n')) = ((term462 x n n') = (term460 n x n')).
Proof. exact (eq_refl ((term462 x n n') = (term460 n x n'))). Qed.
Lemma lem3178546 (n : nat) (x : real) (n' : nat) : (((term570 x n' n) = (term571 n' x n)) = ((term462 x n n') = (term460 n x n'))) = (((term573 x n' n) = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (MK_COMB (@lem3178542 n' x n) (@lem3178545 n x n')). Qed.
Lemma lem3178549 (n : nat) (x : real) (n' : nat) : (((term573 x n' n) = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))) = (((term570 x n' n) = (term571 n' x n)) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (SYM (@lem3178546 n x n')). Qed.
Lemma lem3178555 (y : int) (x : int) : (term180 x y) = (term181 y x).
Proof. exact (EQ_MP (@lem3176505 y x) (@lem3177672 y x)). Qed.
Lemma lem3178556 (n : nat) (n' : nat) : (term580 n' n) = (term499 n n').
Proof. exact (@lem3178555 (int_of_num n) (int_of_num n')). Qed.
Lemma lem3178557 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3178558 (x : real) (n : nat) (n' : nat) : (term573 x n' n) = (term462 x n n').
Proof. exact (MK_COMB (@lem3178557 x) (@lem3178556 n n')). Qed.
Lemma lem3178559 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3178560 (x : real) (n : nat) (n' : nat) : (term575 x n' n) = (term461 x n n').
Proof. exact (MK_COMB (@lem3178559) (@lem3178558 x n n')). Qed.
Lemma lem3178561 (n' : nat) (x : real) (n : nat) : (term447 n' x n) = (term447 n' x n).
Proof. exact (eq_refl (term447 n' x n)). Qed.
Lemma lem3178562 (n' : nat) (x : real) (n : nat) : ((term573 x n' n) = (term447 n' x n)) = ((term462 x n n') = (term447 n' x n)).
Proof. exact (MK_COMB (@lem3178560 x n n') (@lem3178561 n' x n)). Qed.
Lemma lem3178565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178566 (n' : nat) (x : real) (n : nat) : (term579 n' x n) = (term581 n' x n).
Proof. exact (MK_COMB (@lem3178565) (@lem3178562 n' x n)). Qed.
Lemma lem3178569 (n : nat) (x : real) (n' : nat) : ((term462 x n n') = (term460 n x n')) = ((term462 x n n') = (term460 n x n')).
Proof. exact (eq_refl ((term462 x n n') = (term460 n x n'))). Qed.
Lemma lem3178570 (n : nat) (x : real) (n' : nat) : (((term573 x n' n) = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))) = (((term462 x n n') = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (MK_COMB (@lem3178566 n' x n) (@lem3178569 n x n')). Qed.
Lemma lem3178573 (n : nat) (x : real) (n' : nat) : (((term462 x n n') = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))) = (((term573 x n' n) = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (SYM (@lem3178570 n x n')). Qed.
Lemma lem3178579 (n : real) (m : real) : (real_mul m n) = (real_mul n m).
Proof. exact (proj1 (@lem1486340 n m (@el real))). Qed.
Lemma lem3178580 (n : nat) (x : real) (n' : nat) : (term447 n' x n) = (term460 n x n').
Proof. exact (@lem3178579 (term315 x n) (real_pow x n')). Qed.
Lemma lem3178584 (x : real) (n : nat) (n' : nat) : (term461 x n n') = (term461 x n n').
Proof. exact (eq_refl (term461 x n n')). Qed.
Lemma lem3178585 (n : nat) (x : real) (n' : nat) : ((term462 x n n') = (term447 n' x n)) = ((term462 x n n') = (term460 n x n')).
Proof. exact (MK_COMB (@lem3178584 x n n') (@lem3178580 n x n')). Qed.
Lemma lem3178588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178589 (n : nat) (x : real) (n' : nat) : (term581 n' x n) = (term539 n x n').
Proof. exact (MK_COMB (@lem3178588) (@lem3178585 n x n')). Qed.
Lemma lem3178595 (n : nat) (x : real) (n' : nat) : ((term462 x n n') = (term460 n x n')) = ((term462 x n n') = (term460 n x n')).
Proof. exact (eq_refl ((term462 x n n') = (term460 n x n'))). Qed.
Lemma lem3178596 (n : nat) (x : real) (n' : nat) : (((term462 x n n') = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))) = (((term462 x n n') = (term460 n x n')) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (MK_COMB (@lem3178589 n x n') (@lem3178595 n x n')). Qed.
Lemma lem3178598 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3178599 (x : Prop) : (x = x) = True.
Proof. exact (@lem3178598 Prop x). Qed.
Lemma lem3178600 (n : nat) (x : real) (n' : nat) : (((term462 x n n') = (term460 n x n')) = ((term462 x n n') = (term460 n x n'))) = True.
Proof. exact (@lem3178599 ((term462 x n n') = (term460 n x n'))). Qed.
Lemma lem3178601 (n : nat) (x : real) (n' : nat) : (((term462 x n n') = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))) = True.
Proof. exact (TRANS (@lem3178596 n x n') (@lem3178600 n x n')). Qed.
Lemma lem3178602 (n : nat) (x : real) (n' : nat) : True = (((term462 x n n') = (term447 n' x n)) = ((term462 x n n') = (term460 n x n'))).
Proof. exact (SYM (@lem3178601 n x n')). Qed.
Lemma lem3178603 (n : nat) (x : real) (n' : nat) : ((term462 x n n') = (term447 n' x n)) = ((term462 x n n') = (term460 n x n')).
Proof. exact (EQ_MP (@lem3178602 n x n') (@lem0)). Qed.
Lemma lem3178604 (n : nat) (x : real) (n' : nat) : ((term573 x n' n) = (term447 n' x n)) = ((term462 x n n') = (term460 n x n')).
Proof. exact (EQ_MP (@lem3178573 n x n') (@lem3178603 n x n')). Qed.
Lemma lem3178605 (n : nat) (x : real) (n' : nat) : ((term570 x n' n) = (term571 n' x n)) = ((term462 x n n') = (term460 n x n')).
Proof. exact (EQ_MP (@lem3178549 n x n') (@lem3178604 n x n')). Qed.
Lemma lem3178606 (n : nat) (x : real) (n' : nat) : ((term462 x n' n) = (term460 n' x n)) = ((term462 x n n') = (term460 n x n')).
Proof. exact (EQ_MP (@lem3178517 n x n') (@lem3178605 n x n')). Qed.
Lemma lem3178611 (x : real) (n' : nat) : term543 x n'.
Proof. exact (fun n : nat => @lem3178606 n x n'). Qed.
Lemma lem3178616 (x : real) : term547 x.
Proof. exact (fun n' : nat => @lem3178611 x n'). Qed.
Lemma lem3178620 (n : nat) (m : nat) : (Peano.le m n) = (term178 n m).
Proof. exact (EQ_MP (@lem3176499 n m) (@lem3176498 m n)). Qed.
Lemma lem3178621 (p : nat) (n : nat) : (Peano.le n p) = (term178 p n).
Proof. exact (@lem3178620 p n). Qed.
Lemma lem3178628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3178629 (p : nat) (n : nat) : (term550 n p) = (term582 p n).
Proof. exact (MK_COMB (@lem3178628) (@lem3178621 p n)). Qed.
Lemma lem3178632 (n : nat) (x : real) (p : nat) : ((term462 x n p) = (term460 n x p)) = ((term462 x n p) = (term460 n x p)).
Proof. exact (eq_refl ((term462 x n p) = (term460 n x p))). Qed.
Lemma lem3178633 (n : nat) (x : real) (p : nat) : (term552 n x p) = (term583 n x p).
Proof. exact (MK_COMB (@lem3178629 p n) (@lem3178632 n x p)). Qed.
Lemma lem3178635 {A : Type'} (P : A -> Prop) (Q : Prop) : (term173 A P Q) = (term174 A P Q).
Proof. exact (EQ_MP (@lem3176493 A P Q) (@lem3176492 A P Q)). Qed.
Lemma lem3178636 (P : nat -> Prop) (Q : Prop) : (term584 P Q) = (term585 P Q).
Proof. exact (@lem3178635 nat P Q). Qed.
Lemma lem3178637 (n : nat) (x : real) (p : nat) : (term586 n x p) = (term587 n x p).
Proof. exact (@lem3178636 (term588 p n) ((term462 x n p) = (term460 n x p))). Qed.
Lemma lem3178638 (p : nat) (n : nat) (d : nat) : (term589 p n d) = (p = (Nat.add n d)).
Proof. exact (eq_refl (term589 p n d)). Qed.
Lemma lem3178639 (p : nat) (n : nat) : (term590 p n) = (term588 p n).
Proof. exact (fun_ext (fun d : nat => @lem3178638 p n d)). Qed.
Lemma lem3178640 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3178641 (p : nat) (n : nat) : (term591 p n) = (term178 p n).
Proof. exact (MK_COMB (@lem3178640) (@lem3178639 p n)). Qed.
Lemma lem3178642 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3178643 (p : nat) (n : nat) : (term592 p n) = (term582 p n).
Proof. exact (MK_COMB (@lem3178642) (@lem3178641 p n)). Qed.
Lemma lem3178644 (n : nat) (x : real) (p : nat) : ((term462 x n p) = (term460 n x p)) = ((term462 x n p) = (term460 n x p)).
Proof. exact (eq_refl ((term462 x n p) = (term460 n x p))). Qed.
Lemma lem3178645 (n : nat) (x : real) (p : nat) : (term586 n x p) = (term583 n x p).
Proof. exact (MK_COMB (@lem3178643 p n) (@lem3178644 n x p)). Qed.
Lemma lem3178646 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3178647 (n : nat) (x : real) (p : nat) : (term593 n x p) = (term594 n x p).
Proof. exact (MK_COMB (@lem3178646) (@lem3178645 n x p)). Qed.
Lemma lem3178648 (p : nat) (n : nat) (d : nat) : (term589 p n d) = (p = (Nat.add n d)).
Proof. exact (eq_refl (term589 p n d)). Qed.
Lemma lem3178649 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3178650 (p : nat) (n : nat) (d : nat) : (term595 p n d) = (term596 p n d).
Proof. exact (MK_COMB (@lem3178649) (@lem3178648 p n d)). Qed.
Lemma lem3178651 (n : nat) (x : real) (p : nat) : ((term462 x n p) = (term460 n x p)) = ((term462 x n p) = (term460 n x p)).
Proof. exact (eq_refl ((term462 x n p) = (term460 n x p))). Qed.
Lemma lem3178652 (d : nat) (n : nat) (x : real) (p : nat) : (term597 d n x p) = (term598 d n x p).
Proof. exact (MK_COMB (@lem3178650 p n d) (@lem3178651 n x p)). Qed.
Lemma lem3178653 (n : nat) (x : real) (p : nat) : (term599 n x p) = (term600 n x p).
Proof. exact (fun_ext (fun d : nat => @lem3178652 d n x p)). Qed.
Lemma lem3178654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178655 (n : nat) (x : real) (p : nat) : (term587 n x p) = (term601 n x p).
Proof. exact (MK_COMB (@lem3178654) (@lem3178653 n x p)). Qed.
Lemma lem3178656 (n : nat) (x : real) (p : nat) : ((term586 n x p) = (term587 n x p)) = ((term583 n x p) = (term601 n x p)).
Proof. exact (MK_COMB (@lem3178647 n x p) (@lem3178655 n x p)). Qed.
Lemma lem3178657 (n : nat) (x : real) (p : nat) : (term583 n x p) = (term601 n x p).
Proof. exact (EQ_MP (@lem3178656 n x p) (@lem3178637 n x p)). Qed.
Lemma lem3178670 (n : nat) (x : real) (p : nat) : (term552 n x p) = (term601 n x p).
Proof. exact (TRANS (@lem3178633 n x p) (@lem3178657 n x p)). Qed.
Lemma lem3178671 (n : nat) (x : real) (p : nat) : (term601 n x p) = (term552 n x p).
Proof. exact (SYM (@lem3178670 n x p)). Qed.
Lemma lem3178681 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term602 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3178682 (p : Prop) (q : Prop) (p' : Prop) : term603 p q p'.
Proof. exact (fun q' : Prop => @lem3178681 p q p' q'). Qed.
Lemma lem3178683 (p : Prop) (q : Prop) : term604 p q.
Proof. exact (fun p' : Prop => @lem3178682 p q p'). Qed.
Lemma lem3178684 (d : nat) (n : nat) (x : real) (p : nat) : term605 d n x p.
Proof. exact (@lem3178683 (p = (Nat.add n d)) ((term462 x n p) = (term460 n x p))). Qed.
Lemma lem3178685 (d : nat) (n : nat) (x : real) (p : nat) (p' : Prop) : term606 d n x p p'.
Proof. exact (@lem3178684 d n x p p'). Qed.
Lemma lem3178686 (d : nat) (n : nat) (x : real) (p : nat) (p' : Prop) : (term606 d n x p p') = (term607 d n x p p').
Proof. exact (eq_refl (term606 d n x p p')). Qed.
Lemma lem3178687 (d : nat) (n : nat) (x : real) (p : nat) (p' : Prop) : term607 d n x p p'.
Proof. exact (EQ_MP (@lem3178686 d n x p p') (@lem3178685 d n x p p')). Qed.
Lemma lem3178688 (d : nat) (n : nat) (x : real) (p : nat) (p' : Prop) (q' : Prop) : term608 d n x p p' q'.
Proof. exact (@lem3178687 d n x p p' q'). Qed.
Lemma lem3178689 (d : nat) (n : nat) (x : real) (p : nat) (p' : Prop) (q' : Prop) : (term608 d n x p p' q') = (term609 d n x p p' q').
Proof. exact (eq_refl (term608 d n x p p' q')). Qed.
Lemma lem3178690 (d : nat) (n : nat) (x : real) (p : nat) (p' : Prop) (q' : Prop) : term609 d n x p p' q'.
Proof. exact (EQ_MP (@lem3178689 d n x p p' q') (@lem3178688 d n x p p' q')). Qed.
Lemma lem3178693 (p : nat) (n : nat) (d : nat) : (p = (Nat.add n d)) = (p = (Nat.add n d)).
Proof. exact (eq_refl (p = (Nat.add n d))). Qed.
Lemma lem3178694 (x : real) (p : nat) (n : nat) (d : nat) (q' : Prop) : term610 x p n d q'.
Proof. exact (@lem3178690 d n x p (p = (Nat.add n d)) q'). Qed.
Lemma lem3178695 (x : real) (p : nat) (n : nat) (d : nat) (q' : Prop) : term611 x p n d q'.
Proof. exact (@lem3178694 x p n d q' (@lem3178693 p n d)). Qed.
Lemma lem3178700 (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : p = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem3178701 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem3178702 (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : (int_of_num p) = (term159 n d).
Proof. exact (MK_COMB (@lem3178701) (@lem3178700 p n d h1)). Qed.
Lemma lem3178704 (m : nat) (n : nat) : (term159 m n) = (term158 m n).
Proof. exact (EQ_MP (@lem3176487 m n) (@lem3176486 m n)). Qed.
Lemma lem3178705 (n : nat) (d : nat) : (term159 n d) = (term158 n d).
Proof. exact (@lem3178704 n d). Qed.
Lemma lem3178706 (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : (int_of_num p) = (term158 n d).
Proof. exact (TRANS (@lem3178702 p n d h1) (@lem3178705 n d)). Qed.
Lemma lem3178707 (n : nat) : (term612 n) = (term612 n).
Proof. exact (eq_refl (term612 n)). Qed.
Lemma lem3178708 (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : (term499 n p) = (term613 n d).
Proof. exact (MK_COMB (@lem3178707 n) (@lem3178706 p n d h1)). Qed.
Lemma lem3178710 (n : int) (m : int) : (term19 n m) = m.
Proof. exact (EQ_MP (@lem3175560 n m) (@lem3176465 n m)). Qed.
Lemma lem3178711 (n : nat) (d : nat) : (term613 n d) = (int_of_num d).
Proof. exact (@lem3178710 (int_of_num n) (int_of_num d)). Qed.
Lemma lem3178712 (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : (term499 n p) = (int_of_num d).
Proof. exact (TRANS (@lem3178708 p n d h1) (@lem3178711 n d)). Qed.
Lemma lem3178713 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3178714 (x : real) (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : (term462 x n p) = (term10 x d).
Proof. exact (MK_COMB (@lem3178713 x) (@lem3178712 p n d h1)). Qed.
Lemma lem3178715 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3178716 (x : real) (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : (term461 x n p) = (term614 x d).
Proof. exact (MK_COMB (@lem3178715) (@lem3178714 x p n d h1)). Qed.
Lemma lem3178718 (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : p = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem3178719 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem3178720 (x : real) (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : (real_pow x p) = (term16 x n d).
Proof. exact (MK_COMB (@lem3178719 x) (@lem3178718 p n d h1)). Qed.
Lemma lem3178721 (x : real) (n : nat) : (term458 x n) = (term458 x n).
Proof. exact (eq_refl (term458 x n)). Qed.
Lemma lem3178722 (x : real) (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : (term460 n x p) = (term615 x n d).
Proof. exact (MK_COMB (@lem3178721 x n) (@lem3178720 x p n d h1)). Qed.
Lemma lem3178723 (x : real) (p : nat) (n : nat) (d : nat) (h1 : p = (Nat.add n d)) : ((term462 x n p) = (term460 n x p)) = ((term10 x d) = (term615 x n d)).
Proof. exact (MK_COMB (@lem3178716 x p n d h1) (@lem3178722 x p n d h1)). Qed.
Lemma lem3178726 (p : nat) (x : real) (n : nat) (d : nat) : term616 p x n d.
Proof. exact (fun h0 : p = (Nat.add n d) => @lem3178723 x p n d h0). Qed.
Lemma lem3178727 (p : nat) (x : real) (n : nat) (d : nat) : term617 p x n d.
Proof. exact (@lem3178695 x p n d ((term10 x d) = (term615 x n d))). Qed.
Lemma lem3178728 (p : nat) (x : real) (n : nat) (d : nat) : (term598 d n x p) = (term618 p x n d).
Proof. exact (@lem3178727 p x n d (@lem3178726 p x n d)). Qed.
Lemma lem3178760 (p : nat) (x : real) (n : nat) : (term600 n x p) = (term619 p x n).
Proof. exact (fun_ext (fun d : nat => @lem3178728 p x n d)). Qed.
Lemma lem3178792 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178793 (p : nat) (x : real) (n : nat) : (term601 n x p) = (term620 p x n).
Proof. exact (MK_COMB (@lem3178792) (@lem3178760 p x n)). Qed.
Lemma lem3178829 (n : nat) (x : real) (p : nat) : (term620 p x n) = (term601 n x p).
Proof. exact (SYM (@lem3178793 p x n)). Qed.
Lemma lem3178843 (x : real) (n : nat) : (term10 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3175520 x n) (@lem3175519 x n)). Qed.
Lemma lem3178844 (x : real) (d : nat) : (term10 x d) = (real_pow x d).
Proof. exact (@lem3178843 x d). Qed.
Lemma lem3178845 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3178846 (x : real) (d : nat) : (term614 x d) = (term621 x d).
Proof. exact (MK_COMB (@lem3178845) (@lem3178844 x d)). Qed.
Lemma lem3178848 (m : nat) (x : real) (n : nat) : (term16 x m n) = (term17 m x n).
Proof. exact (EQ_MP (@lem3175529 m x n) (@lem3175528 m x n)). Qed.
Lemma lem3178849 (n : nat) (x : real) (d : nat) : (term16 x n d) = (term17 n x d).
Proof. exact (@lem3178848 n x d). Qed.
Lemma lem3178850 (x : real) (n : nat) : (term458 x n) = (term458 x n).
Proof. exact (eq_refl (term458 x n)). Qed.
Lemma lem3178851 (n : nat) (x : real) (d : nat) : (term615 x n d) = (term622 n x d).
Proof. exact (MK_COMB (@lem3178850 x n) (@lem3178849 n x d)). Qed.
Lemma lem3178853 (x : real) (y : real) (z : real) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem3175514 x y z) (@lem3175513 x y z)). Qed.
Lemma lem3178854 (n : nat) (x : real) (d : nat) : (term622 n x d) = (term623 n x d).
Proof. exact (@lem3178853 (term315 x n) (real_pow x n) (real_pow x d)). Qed.
Lemma lem3178855 (n : nat) (x : real) (d : nat) : (term615 x n d) = (term623 n x d).
Proof. exact (TRANS (@lem3178851 n x d) (@lem3178854 n x d)). Qed.
Lemma lem3178856 (n : nat) (x : real) (d : nat) : ((term10 x d) = (term615 x n d)) = ((real_pow x d) = (term623 n x d)).
Proof. exact (MK_COMB (@lem3178846 x d) (@lem3178855 n x d)). Qed.
Lemma lem3178859 (p : nat) (n : nat) (d : nat) : (term596 p n d) = (term596 p n d).
Proof. exact (eq_refl (term596 p n d)). Qed.
Lemma lem3178860 (p : nat) (n : nat) (x : real) (d : nat) : (term618 p x n d) = (term624 p n x d).
Proof. exact (MK_COMB (@lem3178859 p n d) (@lem3178856 n x d)). Qed.
Lemma lem3178865 (p : nat) (n : nat) (x : real) : (term619 p x n) = (term625 p n x).
Proof. exact (fun_ext (fun d : nat => @lem3178860 p n x d)). Qed.
Lemma lem3178866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178867 (p : nat) (n : nat) (x : real) : (term620 p x n) = (term626 p n x).
Proof. exact (MK_COMB (@lem3178866) (@lem3178865 p n x)). Qed.
Lemma lem3178872 (p : nat) (x : real) (n : nat) : (term626 p n x) = (term620 p x n).
Proof. exact (SYM (@lem3178867 p n x)). Qed.
Lemma lem3178873 (x : real) : term627 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem3178874 (x : real) : (term627 x) = ((term628 x) = x).
Proof. exact (eq_refl (term627 x)). Qed.
Lemma lem3178876 (x : real) : term629 x.
Proof. exact (@lem1630283 x). Qed.
Lemma lem3178877 (x : real) : (term629 x) = (term630 x).
Proof. exact (eq_refl (term629 x)). Qed.
Lemma lem3178878 (x : real) : term630 x.
Proof. exact (EQ_MP (@lem3178877 x) (@lem3178876 x)). Qed.
Lemma lem3178879 (x : real) (n : nat) : term631 x n.
Proof. exact (@lem3178878 x n). Qed.
Lemma lem3178880 (x : real) (n : nat) : (term631 x n) = (((real_pow x n) = term83) = (term632 x n)).
Proof. exact (eq_refl (term631 x n)). Qed.
Lemma lem3178882 (x : real) : term633 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem3178883 (x : real) : (term633 x) = (term634 x).
Proof. exact (eq_refl (term633 x)). Qed.
Lemma lem3178884 (x : real) : term634 x.
Proof. exact (EQ_MP (@lem3178883 x) (@lem3178882 x)). Qed.
Lemma lem3178885 (x : real) (h1 : term441 x) : term441 x.
Proof. exact (h1). Qed.
Lemma lem3178886 (x : real) (h1 : term441 x) : (term635 x) = term44.
Proof. exact (@lem3178884 x (@lem3178885 x h1)). Qed.
Lemma lem3178892 (x : real) : term636 x.
Proof. exact (@lem82 (x = term83)). Qed.
Lemma lem3178914 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term602 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3178915 (p : Prop) (q : Prop) (p' : Prop) : term603 p q p'.
Proof. exact (fun q' : Prop => @lem3178914 p q p' q'). Qed.
Lemma lem3178916 (p : Prop) (q : Prop) : term604 p q.
Proof. exact (fun p' : Prop => @lem3178915 p q p'). Qed.
Lemma lem3178917 (p : nat) (n : nat) (x : real) (d : nat) : term637 p n x d.
Proof. exact (@lem3178916 (p = (Nat.add n d)) ((real_pow x d) = (term623 n x d))). Qed.
Lemma lem3178918 (p : nat) (n : nat) (x : real) (d : nat) (p' : Prop) : term638 p n x d p'.
Proof. exact (@lem3178917 p n x d p'). Qed.
Lemma lem3178919 (p : nat) (n : nat) (x : real) (d : nat) (p' : Prop) : (term638 p n x d p') = (term639 p n x d p').
Proof. exact (eq_refl (term638 p n x d p')). Qed.
Lemma lem3178920 (p : nat) (n : nat) (x : real) (d : nat) (p' : Prop) : term639 p n x d p'.
Proof. exact (EQ_MP (@lem3178919 p n x d p') (@lem3178918 p n x d p')). Qed.
Lemma lem3178921 (p : nat) (n : nat) (x : real) (d : nat) (p' : Prop) (q' : Prop) : term640 p n x d p' q'.
Proof. exact (@lem3178920 p n x d p' q'). Qed.
Lemma lem3178922 (p : nat) (n : nat) (x : real) (d : nat) (p' : Prop) (q' : Prop) : (term640 p n x d p' q') = (term641 p n x d p' q').
Proof. exact (eq_refl (term640 p n x d p' q')). Qed.
Lemma lem3178923 (p : nat) (n : nat) (x : real) (d : nat) (p' : Prop) (q' : Prop) : term641 p n x d p' q'.
Proof. exact (EQ_MP (@lem3178922 p n x d p' q') (@lem3178921 p n x d p' q')). Qed.
Lemma lem3178926 (p : nat) (n : nat) (d : nat) : (p = (Nat.add n d)) = (p = (Nat.add n d)).
Proof. exact (eq_refl (p = (Nat.add n d))). Qed.
Lemma lem3178927 (x : real) (p : nat) (n : nat) (d : nat) (q' : Prop) : term642 x p n d q'.
Proof. exact (@lem3178923 p n x d (p = (Nat.add n d)) q'). Qed.
Lemma lem3178928 (x : real) (p : nat) (n : nat) (d : nat) (q' : Prop) : term643 x p n d q'.
Proof. exact (@lem3178927 x p n d q' (@lem3178926 p n d)). Qed.
Lemma lem3178933 (x : real) : term634 x.
Proof. exact (fun h0 : term441 x => @lem3178886 x h0). Qed.
Lemma lem3178934 (x : real) (n : nat) : term644 x n.
Proof. exact (@lem3178933 (real_pow x n)). Qed.
Lemma lem3178936 (x : real) (n : nat) : ((real_pow x n) = term83) = (term632 x n).
Proof. exact (EQ_MP (@lem3178880 x n) (@lem3178879 x n)). Qed.
Lemma lem3178940 (x : real) (h1 : term441 x) : (x = term83) = False.
Proof. exact (@lem3178892 x (@lem3178456 x h1)). Qed.
Lemma lem3178941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3178942 (x : real) (h1 : term441 x) : (term645 x) = (and False).
Proof. exact (MK_COMB (@lem3178941) (@lem3178940 x h1)). Qed.
Lemma lem3178945 (n : nat) : (term646 n) = (term646 n).
Proof. exact (eq_refl (term646 n)). Qed.
Lemma lem3178946 (n : nat) (x : real) (h1 : term441 x) : (term632 x n) = (term647 n).
Proof. exact (MK_COMB (@lem3178942 x h1) (@lem3178945 n)). Qed.
Lemma lem3178948 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3178949 (n : nat) : (term647 n) = False.
Proof. exact (@lem3178948 (term646 n)). Qed.
Lemma lem3178950 (n : nat) (x : real) (h1 : term441 x) : (term632 x n) = False.
Proof. exact (TRANS (@lem3178946 n x h1) (@lem3178949 n)). Qed.
Lemma lem3178951 (n : nat) (x : real) (h1 : term441 x) : ((real_pow x n) = term83) = False.
Proof. exact (TRANS (@lem3178936 x n) (@lem3178950 n x h1)). Qed.
Lemma lem3178952 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3178953 (n : nat) (x : real) (h1 : term441 x) : (term648 x n) = (~ False).
Proof. exact (MK_COMB (@lem3178952) (@lem3178951 n x h1)). Qed.
Lemma lem3178955 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3178956 (n : nat) (x : real) (h1 : term441 x) : (term648 x n) = True.
Proof. exact (TRANS (@lem3178953 n x h1) (@lem3178955)). Qed.
Lemma lem3178957 (n : nat) (x : real) (h1 : term441 x) : True = (term648 x n).
Proof. exact (SYM (@lem3178956 n x h1)). Qed.
Lemma lem3178958 (n : nat) (x : real) (h1 : term441 x) : term648 x n.
Proof. exact (EQ_MP (@lem3178957 n x h1) (@lem0)). Qed.
Lemma lem3178959 (n : nat) (x : real) (h1 : term441 x) : (term649 x n) = term44.
Proof. exact (@lem3178934 x n (@lem3178958 n x h1)). Qed.
Lemma lem3178960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3178961 (n : nat) (x : real) (h1 : term441 x) : (term650 x n) = term230.
Proof. exact (MK_COMB (@lem3178960) (@lem3178959 n x h1)). Qed.
Lemma lem3178962 (x : real) (d : nat) : (real_pow x d) = (real_pow x d).
Proof. exact (eq_refl (real_pow x d)). Qed.
Lemma lem3178963 (n : nat) (d : nat) (x : real) (h1 : term441 x) : (term623 n x d) = (term651 x d).
Proof. exact (MK_COMB (@lem3178961 n x h1) (@lem3178962 x d)). Qed.
Lemma lem3178965 (x : real) : (term628 x) = x.
Proof. exact (EQ_MP (@lem3178874 x) (@lem3178873 x)). Qed.
Lemma lem3178966 (x : real) (d : nat) : (term651 x d) = (real_pow x d).
Proof. exact (@lem3178965 (real_pow x d)). Qed.
Lemma lem3178967 (n : nat) (d : nat) (x : real) (h1 : term441 x) : (term623 n x d) = (real_pow x d).
Proof. exact (TRANS (@lem3178963 n d x h1) (@lem3178966 x d)). Qed.
Lemma lem3178968 (x : real) (d : nat) : (term621 x d) = (term621 x d).
Proof. exact (eq_refl (term621 x d)). Qed.
Lemma lem3178969 (n : nat) (d : nat) (x : real) (h1 : term441 x) : ((real_pow x d) = (term623 n x d)) = ((real_pow x d) = (real_pow x d)).
Proof. exact (MK_COMB (@lem3178968 x d) (@lem3178967 n d x h1)). Qed.
Lemma lem3178971 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3178972 (x : real) : (x = x) = True.
Proof. exact (@lem3178971 real x). Qed.
Lemma lem3178973 (x : real) (d : nat) : ((real_pow x d) = (real_pow x d)) = True.
Proof. exact (@lem3178972 (real_pow x d)). Qed.
Lemma lem3178974 (n : nat) (d : nat) (x : real) (h1 : term441 x) : ((real_pow x d) = (term623 n x d)) = True.
Proof. exact (TRANS (@lem3178969 n d x h1) (@lem3178973 x d)). Qed.
Lemma lem3178975 (p : nat) (n : nat) (d : nat) (x : real) (h1 : term441 x) : term652 p n x d.
Proof. exact (fun h0 : p = (Nat.add n d) => @lem3178974 n d x h1). Qed.
Lemma lem3178976 (x : real) (p : nat) (n : nat) (d : nat) : term653 x p n d.
Proof. exact (@lem3178928 x p n d True). Qed.
Lemma lem3178977 (p : nat) (n : nat) (d : nat) (x : real) (h1 : term441 x) : (term624 p n x d) = (term654 p n d).
Proof. exact (@lem3178976 x p n d (@lem3178975 p n d x h1)). Qed.
Lemma lem3178981 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3178982 (p : nat) (n : nat) (d : nat) : (term654 p n d) = True.
Proof. exact (@lem3178981 (p = (Nat.add n d))). Qed.
Lemma lem3178983 (p : nat) (n : nat) (d : nat) (x : real) (h1 : term441 x) : (term624 p n x d) = True.
Proof. exact (TRANS (@lem3178977 p n d x h1) (@lem3178982 p n d)). Qed.
Lemma lem3178984 (p : nat) (n : nat) (x : real) (h1 : term441 x) : (term625 p n x) = term442.
Proof. exact (fun_ext (fun d : nat => @lem3178983 p n d x h1)). Qed.
Lemma lem3178985 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3178986 (p : nat) (n : nat) (x : real) (h1 : term441 x) : (term626 p n x) = term443.
Proof. exact (MK_COMB (@lem3178985) (@lem3178984 p n x h1)). Qed.
Lemma lem3178988 {A : Type'} (t : Prop) : (term444 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3178989 (t : Prop) : (term445 t) = t.
Proof. exact (@lem3178988 nat t). Qed.
Lemma lem3178990 : term443 = True.
Proof. exact (@lem3178989 True). Qed.
Lemma lem3178991 (p : nat) (n : nat) (x : real) (h1 : term441 x) : (term626 p n x) = True.
Proof. exact (TRANS (@lem3178986 p n x h1) (@lem3178990)). Qed.
Lemma lem3178992 (p : nat) (n : nat) (x : real) (h1 : term441 x) : True = (term626 p n x).
Proof. exact (SYM (@lem3178991 p n x h1)). Qed.
Lemma lem3178993 (p : nat) (n : nat) (x : real) (h1 : term441 x) : term626 p n x.
Proof. exact (EQ_MP (@lem3178992 p n x h1) (@lem0)). Qed.
Lemma lem3178994 (p : nat) (n : nat) (x : real) (h1 : term441 x) : term620 p x n.
Proof. exact (EQ_MP (@lem3178872 p x n) (@lem3178993 p n x h1)). Qed.
Lemma lem3178995 (n : nat) (p : nat) (x : real) (h1 : term441 x) : term601 n x p.
Proof. exact (EQ_MP (@lem3178829 n x p) (@lem3178994 p n x h1)). Qed.
Lemma lem3178996 (n : nat) (p : nat) (x : real) (h1 : term441 x) : term552 n x p.
Proof. exact (EQ_MP (@lem3178671 n x p) (@lem3178995 n p x h1)). Qed.
Lemma lem3179001 (n : nat) (x : real) (h1 : term441 x) : term556 n x.
Proof. exact (fun p : nat => @lem3178996 n p x h1). Qed.
Lemma lem3179006 (x : real) (h1 : term441 x) : term560 x.
Proof. exact (fun n : nat => @lem3179001 n x h1). Qed.
Lemma lem3179007 (x : real) (h1 : term441 x) : term562 x.
Proof. exact (conj (@lem3178616 x) (@lem3179006 x h1)). Qed.
Lemma lem3179008 (x : real) (h1 : term441 x) : term532 x.
Proof. exact (@lem3178509 x (@lem3179007 x h1)). Qed.
Lemma lem3179009 (x : real) : term533 x.
Proof. exact (fun h0 : term441 x => @lem3179008 x h0). Qed.
Lemma lem3179010 (x : real) : term502 x.
Proof. exact (EQ_MP (@lem3178455 x) (@lem3179009 x)). Qed.
Lemma lem3179011 (x : real) : term497 x.
Proof. exact (EQ_MP (@lem3178364 x) (@lem3179010 x)). Qed.
Lemma lem3179012 (x : real) : term474 x.
Proof. exact (EQ_MP (@lem3178340 x) (@lem3179011 x)). Qed.
Lemma lem3179017 : term476.
Proof. exact (fun x : real => @lem3179012 x). Qed.
Lemma lem3179018 : term436.
Proof. exact (EQ_MP (@lem3178305) (@lem3179017)). Qed.
Lemma lem3179019 : term435.
Proof. exact (EQ_MP (@lem3178060) (@lem3179018)). Qed.
