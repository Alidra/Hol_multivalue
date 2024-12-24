Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIV_LE_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FORALL_INT_CASES_spec.
Require Import INT_ABS_NEG_spec.
Require Import INT_ABS_NUM_spec.
Require Import INT_ABS_POS_spec.
Require Import INT_DIV_0_spec.
Require Import INT_DIV_LE_EQ_spec.
Require Import INT_DIV_RNEG_spec.
Require Import INT_LE_DIV_EQ_spec.
Require Import INT_LE_LMUL_spec.
Require Import INT_OF_NUM_LE_spec.
Require Import INT_OF_NUM_LT_spec.
Require Import LE_1_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SWAP_FORALL_THM_spec.
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
Require Import thm1482679_spec.
Require Import thm1482680_spec.
Require Import thm1482981_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm19158_spec.
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
Require Import thm1982735_spec.
Require Import thm1982745_spec.
Require Import thm1982747_spec.
Require Import thm1982749_spec.
Require Import thm1982751_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318541_spec.
Require Import thm2318542_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2611646 (x : int) : term0 x.
Proof. exact (@lem2300522 x). Qed.
Lemma lem2611647 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2611648 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2611647 x) (@lem2611646 x)). Qed.
Lemma lem2611649 (x : int) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem2611651 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem2611652 (x : int) (h1 : term2) : term3 x.
Proof. exact (@lem2611651 h1 x). Qed.
Lemma lem2611653 (x : int) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem2611654 (x : int) (h1 : term2) : term4 x.
Proof. exact (EQ_MP (@lem2611653 x) (@lem2611652 x h1)). Qed.
Lemma lem2611655 (x : int) (y : int) (h1 : term2) : term5 x y.
Proof. exact (@lem2611654 x h1 y). Qed.
Lemma lem2611656 (y : int) (x : int) : (term5 x y) = (term6 y x).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem2611657 (y : int) (x : int) (h1 : term2) : term6 y x.
Proof. exact (EQ_MP (@lem2611656 y x) (@lem2611655 x y h1)). Qed.
Lemma lem2611658 (y : int) (x : int) (z : int) (h1 : term2) : term7 y x z.
Proof. exact (@lem2611657 y x h1 z). Qed.
Lemma lem2611659 (y : int) (x : int) (z : int) : (term7 y x z) = (term8 y x z).
Proof. exact (eq_refl (term7 y x z)). Qed.
Lemma lem2611660 (y : int) (x : int) (z : int) (h1 : term2) : term8 y x z.
Proof. exact (EQ_MP (@lem2611659 y x z) (@lem2611658 y x z h1)). Qed.
Lemma lem2611661 (x : int) (y : int) (z : int) (h1 : term9 x y z) : term9 x y z.
Proof. exact (h1). Qed.
Lemma lem2611662 (x : int) (y : int) (z : int) (h1 : term2) (h2 : term9 x y z) : term10 y x z.
Proof. exact (@lem2611660 y x z h1 (@lem2611661 x y z h2)). Qed.
Lemma lem2611663 (x : int) (y : int) (z : int) (h1 : term9 x y z) : term11 y x z.
Proof. exact (fun h0 : term2 => @lem2611662 x y z h0 h1). Qed.
Lemma lem2611664 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem2611665 (x : int) (y : int) (z : int) (h1 : term2) (h2 : term9 x y z) : term10 y x z.
Proof. exact (@lem2611663 x y z h2 (@lem2611664 h1)). Qed.
Lemma lem2611666 (y : int) (x : int) (z : int) (h1 : term2) : term8 y x z.
Proof. exact (fun h0 : term9 x y z => @lem2611665 x y z h1 h0). Qed.
Lemma lem2611667 (y : int) (x : int) (h1 : term2) : term6 y x.
Proof. exact (fun z : int => @lem2611666 y x z h1). Qed.
Lemma lem2611668 (y : int) (h1 : term2) : term12 y.
Proof. exact (fun x : int => @lem2611667 y x h1). Qed.
Lemma lem2611669 (h1 : term2) : term13.
Proof. exact (fun y : int => @lem2611668 y h1). Qed.
Lemma lem2611670 : term14.
Proof. exact (fun h0 : term2 => @lem2611669 h0). Qed.
Lemma lem2611671 : term13.
Proof. exact (@lem2611670 (@lem2302531)). Qed.
Lemma lem2611672 (y : int) : term15 y.
Proof. exact (@lem2611671 y). Qed.
Lemma lem2611673 (y : int) : (term15 y) = (term12 y).
Proof. exact (eq_refl (term15 y)). Qed.
Lemma lem2611674 (y : int) : term12 y.
Proof. exact (EQ_MP (@lem2611673 y) (@lem2611672 y)). Qed.
Lemma lem2611675 (y : int) (x : int) : term16 y x.
Proof. exact (@lem2611674 y x). Qed.
Lemma lem2611676 (y : int) (x : int) : (term16 y x) = (term6 y x).
Proof. exact (eq_refl (term16 y x)). Qed.
Lemma lem2611677 (y : int) (x : int) : term6 y x.
Proof. exact (EQ_MP (@lem2611676 y x) (@lem2611675 y x)). Qed.
Lemma lem2611678 (y : int) (x : int) (z : int) : term7 y x z.
Proof. exact (@lem2611677 y x z). Qed.
Lemma lem2611679 (y : int) (x : int) (z : int) : (term7 y x z) = (term8 y x z).
Proof. exact (eq_refl (term7 y x z)). Qed.
Lemma lem2611681 (n : int) (m : int) : (term17 n m) = (term18 n m).
Proof. exact (@lem2318604 (term18 n m)). Qed.
Lemma lem2611704 (n : int) (m : int) : (term19 n m) = (term20 n m).
Proof. exact (@lem17045 (term21 n m) (term22 n m)). Qed.
Lemma lem2611706 (m : int) (n : int) : (term23 m n) = (term23 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem2611707 (n : int) (m : int) : (term24 n m) = (term25 n m).
Proof. exact (MK_COMB (@lem2611706 m n) (@lem2611704 n m)). Qed.
Lemma lem2611708 (n : int) (m : int) : (term26 n m) = (term24 n m).
Proof. exact (@lem17362 (term27 m n) (term28 n m)). Qed.
Lemma lem2611728 (n : int) (m : int) : (term26 n m) = (term25 n m).
Proof. exact (TRANS (@lem2611708 n m) (@lem2611707 n m)). Qed.
Lemma lem2611730 (x : int) (y : int) : (int_lt x y) = (term29 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2611731 (n : int) : (term30 n) = (term31 n).
Proof. exact (@lem2611730 term32 n). Qed.
Lemma lem2611733 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2611734 (n : int) : (term31 n) = (term34 n).
Proof. exact (@lem2611733 term35 n). Qed.
Lemma lem2611736 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2611737 : term38 = term39.
Proof. exact (@lem2611736 term32 term40). Qed.
Lemma lem2611739 (n : nat) : (term41 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2611740 : term42 = term43.
Proof. exact (@lem2611739 (NUMERAL 0)). Qed.
Lemma lem2611741 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2611742 : term44 = term45.
Proof. exact (MK_COMB (@lem2611741) (@lem2611740)). Qed.
Lemma lem2611744 (n : nat) : (term41 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2611745 : term46 = term47.
Proof. exact (@lem2611744 term48). Qed.
Lemma lem2611746 : term39 = term49.
Proof. exact (MK_COMB (@lem2611742) (@lem2611745)). Qed.
Lemma lem2611747 : term38 = term49.
Proof. exact (TRANS (@lem2611737) (@lem2611746)). Qed.
Lemma lem2611748 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2611749 : term50 = term51.
Proof. exact (MK_COMB (@lem2611748) (@lem2611747)). Qed.
Lemma lem2611750 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2611751 (n : int) : (term34 n) = (term52 n).
Proof. exact (MK_COMB (@lem2611749) (@lem2611750 n)). Qed.
Lemma lem2611752 (n : int) : (term31 n) = (term52 n).
Proof. exact (TRANS (@lem2611734 n) (@lem2611751 n)). Qed.
Lemma lem2611753 (n : int) : (term30 n) = (term52 n).
Proof. exact (TRANS (@lem2611731 n) (@lem2611752 n)). Qed.
Lemma lem2611756 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2611757 (m : int) (n : int) : (term53 m n) = (term54 m n).
Proof. exact (@lem2611756 (term55 m) (term56 m n)). Qed.
Lemma lem2611759 (x : int) (y : int) : (term57 x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2611760 (m : int) : (term59 m) = (term60 m).
Proof. exact (@lem2611759 (int_abs m) term40). Qed.
Lemma lem2611762 (x : int) : (term61 x) = (term62 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2611763 (m : int) : (term61 m) = (term62 m).
Proof. exact (@lem2611762 m). Qed.
Lemma lem2611764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2611765 (m : int) : (term63 m) = (term64 m).
Proof. exact (MK_COMB (@lem2611764) (@lem2611763 m)). Qed.
Lemma lem2611767 (n : nat) : (term41 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2611768 : term46 = term47.
Proof. exact (@lem2611767 term48). Qed.
Lemma lem2611769 (m : int) : (term60 m) = (term65 m).
Proof. exact (MK_COMB (@lem2611765 m) (@lem2611768)). Qed.
Lemma lem2611770 (m : int) : (term59 m) = (term65 m).
Proof. exact (TRANS (@lem2611760 m) (@lem2611769 m)). Qed.
Lemma lem2611771 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2611772 (m : int) : (term66 m) = (term67 m).
Proof. exact (MK_COMB (@lem2611771) (@lem2611770 m)). Qed.
Lemma lem2611774 (x : int) (y : int) : (term57 x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2611775 (m : int) (n : int) : (term68 m n) = (term69 m n).
Proof. exact (@lem2611774 (int_abs m) n). Qed.
Lemma lem2611777 (x : int) : (term61 x) = (term62 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2611778 (m : int) : (term61 m) = (term62 m).
Proof. exact (@lem2611777 m). Qed.
Lemma lem2611779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2611780 (m : int) : (term63 m) = (term64 m).
Proof. exact (MK_COMB (@lem2611779) (@lem2611778 m)). Qed.
Lemma lem2611781 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2611782 (m : int) (n : int) : (term69 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem2611780 m) (@lem2611781 n)). Qed.
Lemma lem2611783 (m : int) (n : int) : (term68 m n) = (term70 m n).
Proof. exact (TRANS (@lem2611775 m n) (@lem2611782 m n)). Qed.
Lemma lem2611784 (m : int) (n : int) : (term54 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem2611772 m) (@lem2611783 m n)). Qed.
Lemma lem2611786 (m : int) (n : int) : (term53 m n) = (term71 m n).
Proof. exact (TRANS (@lem2611757 m n) (@lem2611784 m n)). Qed.
Lemma lem2611787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2611788 (n : int) : (term72 n) = (term73 n).
Proof. exact (MK_COMB (@lem2611787) (@lem2611753 n)). Qed.
Lemma lem2611789 (m : int) (n : int) : (term27 m n) = (term74 m n).
Proof. exact (MK_COMB (@lem2611788 n) (@lem2611786 m n)). Qed.
Lemma lem2611791 (y : int) (x : int) : (term75 x y) = (term29 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2611792 (n : int) (m : int) : (term76 n m) = (term77 n m).
Proof. exact (@lem2611791 m (term78 n m)). Qed.
Lemma lem2611794 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2611795 (n : int) (m : int) : (term77 n m) = (term79 n m).
Proof. exact (@lem2611794 (term80 m) (term78 n m)). Qed.
Lemma lem2611797 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2611798 (m : int) : (term81 m) = (term82 m).
Proof. exact (@lem2611797 m term40). Qed.
Lemma lem2611800 (n : nat) : (term41 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2611801 : term46 = term47.
Proof. exact (@lem2611800 term48). Qed.
Lemma lem2611802 (m : int) : (term83 m) = (term83 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem2611803 (m : int) : (term82 m) = (term84 m).
Proof. exact (MK_COMB (@lem2611802 m) (@lem2611801)). Qed.
Lemma lem2611804 (m : int) : (term81 m) = (term84 m).
Proof. exact (TRANS (@lem2611798 m) (@lem2611803 m)). Qed.
Lemma lem2611805 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2611806 (m : int) : (term85 m) = (term86 m).
Proof. exact (MK_COMB (@lem2611805) (@lem2611804 m)). Qed.
Lemma lem2611808 (x : int) (y : int) : (term57 x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2611809 (n : int) (m : int) : (term87 n m) = (term88 n m).
Proof. exact (@lem2611808 n (term89 m)). Qed.
Lemma lem2611811 (x : int) : (term90 x) = (term91 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2611812 (m : int) : (term92 m) = (term93 m).
Proof. exact (@lem2611811 (int_abs m)). Qed.
Lemma lem2611814 (x : int) : (term61 x) = (term62 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2611815 (m : int) : (term61 m) = (term62 m).
Proof. exact (@lem2611814 m). Qed.
Lemma lem2611816 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2611817 (m : int) : (term93 m) = (term94 m).
Proof. exact (MK_COMB (@lem2611816) (@lem2611815 m)). Qed.
Lemma lem2611818 (m : int) : (term92 m) = (term94 m).
Proof. exact (TRANS (@lem2611812 m) (@lem2611817 m)). Qed.
Lemma lem2611819 (n : int) : (term95 n) = (term95 n).
Proof. exact (eq_refl (term95 n)). Qed.
Lemma lem2611820 (n : int) (m : int) : (term88 n m) = (term96 n m).
Proof. exact (MK_COMB (@lem2611819 n) (@lem2611818 m)). Qed.
Lemma lem2611821 (n : int) (m : int) : (term87 n m) = (term96 n m).
Proof. exact (TRANS (@lem2611809 n m) (@lem2611820 n m)). Qed.
Lemma lem2611822 (n : int) (m : int) : (term79 n m) = (term97 n m).
Proof. exact (MK_COMB (@lem2611806 m) (@lem2611821 n m)). Qed.
Lemma lem2611823 (n : int) (m : int) : (term77 n m) = (term97 n m).
Proof. exact (TRANS (@lem2611795 n m) (@lem2611822 n m)). Qed.
Lemma lem2611824 (n : int) (m : int) : (term76 n m) = (term97 n m).
Proof. exact (TRANS (@lem2611792 n m) (@lem2611823 n m)). Qed.
Lemma lem2611826 (y : int) (x : int) : (term98 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2611827 (n : int) (m : int) : (term99 n m) = (term100 n m).
Proof. exact (@lem2611826 (term101 n m) m). Qed.
Lemma lem2611829 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2611830 (n : int) (m : int) : (term100 n m) = (term102 n m).
Proof. exact (@lem2611829 (term101 n m) m). Qed.
Lemma lem2611832 (x : int) (y : int) : (term57 x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2611833 (n : int) (m : int) : (term103 n m) = (term104 n m).
Proof. exact (@lem2611832 n (term105 m)). Qed.
Lemma lem2611835 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2611836 (m : int) : (term106 m) = (term107 m).
Proof. exact (@lem2611835 (int_abs m) term40). Qed.
Lemma lem2611838 (x : int) : (term61 x) = (term62 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2611839 (m : int) : (term61 m) = (term62 m).
Proof. exact (@lem2611838 m). Qed.
Lemma lem2611840 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2611841 (m : int) : (term108 m) = (term109 m).
Proof. exact (MK_COMB (@lem2611840) (@lem2611839 m)). Qed.
Lemma lem2611843 (n : nat) : (term41 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2611844 : term46 = term47.
Proof. exact (@lem2611843 term48). Qed.
Lemma lem2611845 (m : int) : (term107 m) = (term110 m).
Proof. exact (MK_COMB (@lem2611841 m) (@lem2611844)). Qed.
Lemma lem2611846 (m : int) : (term106 m) = (term110 m).
Proof. exact (TRANS (@lem2611836 m) (@lem2611845 m)). Qed.
Lemma lem2611847 (n : int) : (term95 n) = (term95 n).
Proof. exact (eq_refl (term95 n)). Qed.
Lemma lem2611848 (n : int) (m : int) : (term104 n m) = (term111 n m).
Proof. exact (MK_COMB (@lem2611847 n) (@lem2611846 m)). Qed.
Lemma lem2611849 (n : int) (m : int) : (term103 n m) = (term111 n m).
Proof. exact (TRANS (@lem2611833 n m) (@lem2611848 n m)). Qed.
Lemma lem2611850 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2611851 (n : int) (m : int) : (term112 n m) = (term113 n m).
Proof. exact (MK_COMB (@lem2611850) (@lem2611849 n m)). Qed.
Lemma lem2611852 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2611853 (n : int) (m : int) : (term102 n m) = (term114 n m).
Proof. exact (MK_COMB (@lem2611851 n m) (@lem2611852 m)). Qed.
Lemma lem2611854 (n : int) (m : int) : (term100 n m) = (term114 n m).
Proof. exact (TRANS (@lem2611830 n m) (@lem2611853 n m)). Qed.
Lemma lem2611855 (n : int) (m : int) : (term99 n m) = (term114 n m).
Proof. exact (TRANS (@lem2611827 n m) (@lem2611854 n m)). Qed.
Lemma lem2611856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2611857 (n : int) (m : int) : (term115 n m) = (term116 n m).
Proof. exact (MK_COMB (@lem2611856) (@lem2611824 n m)). Qed.
Lemma lem2611858 (n : int) (m : int) : (term20 n m) = (term117 n m).
Proof. exact (MK_COMB (@lem2611857 n m) (@lem2611855 n m)). Qed.
Lemma lem2611859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2611860 (m : int) (n : int) : (term23 m n) = (term118 m n).
Proof. exact (MK_COMB (@lem2611859) (@lem2611789 m n)). Qed.
Lemma lem2611861 (n : int) (m : int) : (term25 n m) = (term119 n m).
Proof. exact (MK_COMB (@lem2611860 m n) (@lem2611858 n m)). Qed.
Lemma lem2611862 (n : int) (m : int) : (term26 n m) = (term119 n m).
Proof. exact (TRANS (@lem2611728 n m) (@lem2611861 n m)). Qed.
Lemma lem2611866 (t : Prop) : (term120 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2611902 (n : int) (m : int) : (term121 n m) = (term119 n m).
Proof. exact (@lem2611866 (term119 n m)). Qed.
Lemma lem2611903 (n : int) : (term52 n) = (term122 n).
Proof. exact (@lem1988287 (real_of_int n) term49). Qed.
Lemma lem2611910 : term49 = term47.
Proof. exact (@lem1982721 term47). Qed.
Lemma lem2611913 (n : int) : (term123 n) = (term123 n).
Proof. exact (eq_refl (term123 n)). Qed.
Lemma lem2611914 (n : int) : (term124 n) = (term125 n).
Proof. exact (MK_COMB (@lem2611913 n) (@lem2611910)). Qed.
Lemma lem2611915 (n : int) : (term125 n) = (term126 n).
Proof. exact (@lem1982792 (real_of_int n) term47). Qed.
Lemma lem2611917 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2611918 : term47 = term128.
Proof. exact (@lem2611917 term48). Qed.
Lemma lem2611920 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2611921 : term131 = term132.
Proof. exact (@lem2611920 term48). Qed.
Lemma lem2611922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2611923 : term133 = term134.
Proof. exact (MK_COMB (@lem2611922) (@lem2611921)). Qed.
Lemma lem2611924 : term135 = term136.
Proof. exact (MK_COMB (@lem2611923) (@lem2611918)). Qed.
Lemma lem2611925 : term136 = term137.
Proof. exact (@lem1981613 term131 term47 term47 term47). Qed.
Lemma lem2611927 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2611928 : term140 = term141.
Proof. exact (@lem2611927 term48 term48). Qed.
Lemma lem2611929 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2611930 : term143 = term48.
Proof. exact (EQ_MP (@lem2611929) (@lem940073)). Qed.
Lemma lem2611931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2611932 : term141 = term47.
Proof. exact (MK_COMB (@lem2611931) (@lem2611930)). Qed.
Lemma lem2611933 : term140 = term47.
Proof. exact (TRANS (@lem2611928) (@lem2611932)). Qed.
Lemma lem2611935 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2611936 : term135 = term146.
Proof. exact (@lem2611935 term48 term48). Qed.
Lemma lem2611937 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2611938 : term143 = term48.
Proof. exact (EQ_MP (@lem2611937) (@lem940073)). Qed.
Lemma lem2611939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2611940 : term141 = term47.
Proof. exact (MK_COMB (@lem2611939) (@lem2611938)). Qed.
Lemma lem2611941 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2611942 : term146 = term131.
Proof. exact (MK_COMB (@lem2611941) (@lem2611940)). Qed.
Lemma lem2611943 : term135 = term131.
Proof. exact (TRANS (@lem2611936) (@lem2611942)). Qed.
Lemma lem2611944 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2611945 : term147 = term148.
Proof. exact (MK_COMB (@lem2611944) (@lem2611943)). Qed.
Lemma lem2611946 : term137 = term132.
Proof. exact (MK_COMB (@lem2611945) (@lem2611933)). Qed.
Lemma lem2611947 : term136 = term132.
Proof. exact (TRANS (@lem2611925) (@lem2611946)). Qed.
Lemma lem2611948 : term135 = term132.
Proof. exact (TRANS (@lem2611924) (@lem2611947)). Qed.
Lemma lem2611950 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2611951 : term132 = term131.
Proof. exact (@lem2611950 term131). Qed.
Lemma lem2611952 : term135 = term131.
Proof. exact (TRANS (@lem2611948) (@lem2611951)). Qed.
Lemma lem2611953 (n : int) : (term83 n) = (term83 n).
Proof. exact (eq_refl (term83 n)). Qed.
Lemma lem2611956 (n : int) : (term126 n) = (term150 n).
Proof. exact (MK_COMB (@lem2611953 n) (@lem2611952)). Qed.
Lemma lem2611957 (n : int) : (term125 n) = (term150 n).
Proof. exact (TRANS (@lem2611915 n) (@lem2611956 n)). Qed.
Lemma lem2611958 (n : int) : (term124 n) = (term150 n).
Proof. exact (TRANS (@lem2611914 n) (@lem2611957 n)). Qed.
Lemma lem2611959 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2611960 (n : int) : (term151 n) = (term152 n).
Proof. exact (MK_COMB (@lem2611959) (@lem2611958 n)). Qed.
Lemma lem2611961 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2611962 (n : int) : (term122 n) = (term153 n).
Proof. exact (MK_COMB (@lem2611960 n) (@lem2611961)). Qed.
Lemma lem2611963 (n : int) : (term52 n) = (term153 n).
Proof. exact (TRANS (@lem2611903 n) (@lem2611962 n)). Qed.
Lemma lem2611964 (n : int) (m : int) : (term71 m n) = (term154 n m).
Proof. exact (@lem1988287 (term70 m n) (term65 m)). Qed.
Lemma lem2611973 (m : int) : (term65 m) = (term62 m).
Proof. exact (@lem1982735 (term62 m)). Qed.
Lemma lem2611984 (m : int) (n : int) : (term155 m n) = (term155 m n).
Proof. exact (eq_refl (term155 m n)). Qed.
Lemma lem2611985 (n : int) (m : int) : (term156 n m) = (term157 n m).
Proof. exact (MK_COMB (@lem2611984 m n) (@lem2611973 m)). Qed.
Lemma lem2611992 (n : int) (m : int) : (term157 n m) = (term158 n m).
Proof. exact (@lem1982792 (term70 m n) (term62 m)). Qed.
Lemma lem2611993 (n : int) (m : int) : (term156 n m) = (term158 n m).
Proof. exact (TRANS (@lem2611985 n m) (@lem2611992 n m)). Qed.
Lemma lem2611994 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2611995 (n : int) (m : int) : (term159 n m) = (term160 n m).
Proof. exact (MK_COMB (@lem2611994) (@lem2611993 n m)). Qed.
Lemma lem2611996 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2611997 (n : int) (m : int) : (term154 n m) = (term161 n m).
Proof. exact (MK_COMB (@lem2611995 n m) (@lem2611996)). Qed.
Lemma lem2611998 (n : int) (m : int) : (term71 m n) = (term161 n m).
Proof. exact (TRANS (@lem2611964 n m) (@lem2611997 n m)). Qed.
Lemma lem2611999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612000 (n : int) : (term73 n) = (term162 n).
Proof. exact (MK_COMB (@lem2611999) (@lem2611963 n)). Qed.
Lemma lem2612001 (n : int) (m : int) : (term74 m n) = (term163 n m).
Proof. exact (MK_COMB (@lem2612000 n) (@lem2611998 n m)). Qed.
Lemma lem2612002 (n : int) (m : int) : (term97 n m) = (term164 n m).
Proof. exact (@lem1988287 (term96 n m) (term84 m)). Qed.
Lemma lem2612009 (m : int) : (term84 m) = (term84 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem2612018 (m : int) : (term94 m) = (term165 m).
Proof. exact (@lem1982785 (term62 m)). Qed.
Lemma lem2612021 (n : int) : (term95 n) = (term95 n).
Proof. exact (eq_refl (term95 n)). Qed.
Lemma lem2612022 (n : int) (m : int) : (term96 n m) = (term166 n m).
Proof. exact (MK_COMB (@lem2612021 n) (@lem2612018 m)). Qed.
Lemma lem2612023 (n : int) (m : int) : (term166 n m) = (term167 n m).
Proof. exact (@lem1982751 term131 (real_of_int n) (term62 m)). Qed.
Lemma lem2612024 (m : int) (n : int) : (term168 n m) = (term70 m n).
Proof. exact (@lem1982747 (term62 m) (real_of_int n)). Qed.
Lemma lem2612025 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem2612026 (m : int) (n : int) : (term167 n m) = (term169 m n).
Proof. exact (MK_COMB (@lem2612025) (@lem2612024 m n)). Qed.
Lemma lem2612027 (m : int) (n : int) : (term166 n m) = (term169 m n).
Proof. exact (TRANS (@lem2612023 n m) (@lem2612026 m n)). Qed.
Lemma lem2612028 (m : int) (n : int) : (term96 n m) = (term169 m n).
Proof. exact (TRANS (@lem2612022 n m) (@lem2612027 m n)). Qed.
Lemma lem2612029 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2612030 (m : int) (n : int) : (term170 n m) = (term171 m n).
Proof. exact (MK_COMB (@lem2612029) (@lem2612028 m n)). Qed.
Lemma lem2612031 (n : int) (m : int) : (term172 n m) = (term173 n m).
Proof. exact (MK_COMB (@lem2612030 m n) (@lem2612009 m)). Qed.
Lemma lem2612032 (n : int) (m : int) : (term173 n m) = (term174 n m).
Proof. exact (@lem1982792 (term169 m n) (term84 m)). Qed.
Lemma lem2612033 (m : int) : (term175 m) = (term176 m).
Proof. exact (@lem1982781 (real_of_int m) term131 term47). Qed.
Lemma lem2612035 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612036 : term47 = term128.
Proof. exact (@lem2612035 term48). Qed.
Lemma lem2612038 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612039 : term131 = term132.
Proof. exact (@lem2612038 term48). Qed.
Lemma lem2612040 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612041 : term133 = term134.
Proof. exact (MK_COMB (@lem2612040) (@lem2612039)). Qed.
Lemma lem2612042 : term135 = term136.
Proof. exact (MK_COMB (@lem2612041) (@lem2612036)). Qed.
Lemma lem2612043 : term136 = term137.
Proof. exact (@lem1981613 term131 term47 term47 term47). Qed.
Lemma lem2612045 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612046 : term140 = term141.
Proof. exact (@lem2612045 term48 term48). Qed.
Lemma lem2612047 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612048 : term143 = term48.
Proof. exact (EQ_MP (@lem2612047) (@lem940073)). Qed.
Lemma lem2612049 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612050 : term141 = term47.
Proof. exact (MK_COMB (@lem2612049) (@lem2612048)). Qed.
Lemma lem2612051 : term140 = term47.
Proof. exact (TRANS (@lem2612046) (@lem2612050)). Qed.
Lemma lem2612053 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2612054 : term135 = term146.
Proof. exact (@lem2612053 term48 term48). Qed.
Lemma lem2612055 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612056 : term143 = term48.
Proof. exact (EQ_MP (@lem2612055) (@lem940073)). Qed.
Lemma lem2612057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612058 : term141 = term47.
Proof. exact (MK_COMB (@lem2612057) (@lem2612056)). Qed.
Lemma lem2612059 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2612060 : term146 = term131.
Proof. exact (MK_COMB (@lem2612059) (@lem2612058)). Qed.
Lemma lem2612061 : term135 = term131.
Proof. exact (TRANS (@lem2612054) (@lem2612060)). Qed.
Lemma lem2612062 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612063 : term147 = term148.
Proof. exact (MK_COMB (@lem2612062) (@lem2612061)). Qed.
Lemma lem2612064 : term137 = term132.
Proof. exact (MK_COMB (@lem2612063) (@lem2612051)). Qed.
Lemma lem2612065 : term136 = term132.
Proof. exact (TRANS (@lem2612043) (@lem2612064)). Qed.
Lemma lem2612066 : term135 = term132.
Proof. exact (TRANS (@lem2612042) (@lem2612065)). Qed.
Lemma lem2612068 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612069 : term132 = term131.
Proof. exact (@lem2612068 term131). Qed.
Lemma lem2612070 : term135 = term131.
Proof. exact (TRANS (@lem2612066) (@lem2612069)). Qed.
Lemma lem2612073 (m : int) : (term177 m) = (term177 m).
Proof. exact (eq_refl (term177 m)). Qed.
Lemma lem2612074 (m : int) : (term176 m) = (term178 m).
Proof. exact (MK_COMB (@lem2612073 m) (@lem2612070)). Qed.
Lemma lem2612075 (m : int) : (term175 m) = (term178 m).
Proof. exact (TRANS (@lem2612033 m) (@lem2612074 m)). Qed.
Lemma lem2612076 (m : int) (n : int) : (term179 m n) = (term179 m n).
Proof. exact (eq_refl (term179 m n)). Qed.
Lemma lem2612079 (n : int) (m : int) : (term174 n m) = (term180 n m).
Proof. exact (MK_COMB (@lem2612076 m n) (@lem2612075 m)). Qed.
Lemma lem2612080 (n : int) (m : int) : (term173 n m) = (term180 n m).
Proof. exact (TRANS (@lem2612032 n m) (@lem2612079 n m)). Qed.
Lemma lem2612081 (n : int) (m : int) : (term172 n m) = (term180 n m).
Proof. exact (TRANS (@lem2612031 n m) (@lem2612080 n m)). Qed.
Lemma lem2612082 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612083 (n : int) (m : int) : (term181 n m) = (term182 n m).
Proof. exact (MK_COMB (@lem2612082) (@lem2612081 n m)). Qed.
Lemma lem2612084 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612085 (n : int) (m : int) : (term164 n m) = (term183 n m).
Proof. exact (MK_COMB (@lem2612083 n m) (@lem2612084)). Qed.
Lemma lem2612086 (n : int) (m : int) : (term97 n m) = (term183 n m).
Proof. exact (TRANS (@lem2612002 n m) (@lem2612085 n m)). Qed.
Lemma lem2612087 (n : int) (m : int) : (term114 n m) = (term184 n m).
Proof. exact (@lem1988287 (real_of_int m) (term111 n m)). Qed.
Lemma lem2612101 (m : int) (n : int) : (term111 n m) = (term185 m n).
Proof. exact (@lem1982781 (term62 m) (real_of_int n) term47). Qed.
Lemma lem2612102 (n : int) : (term186 n) = (term187 n).
Proof. exact (@lem1982747 term47 (real_of_int n)). Qed.
Lemma lem2612103 (n : int) : (term187 n) = (real_of_int n).
Proof. exact (@lem1982709 (real_of_int n)). Qed.
Lemma lem2612104 (n : int) : (term186 n) = (real_of_int n).
Proof. exact (TRANS (@lem2612102 n) (@lem2612103 n)). Qed.
Lemma lem2612105 (m : int) (n : int) : (term168 n m) = (term70 m n).
Proof. exact (@lem1982747 (term62 m) (real_of_int n)). Qed.
Lemma lem2612106 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2612107 (m : int) (n : int) : (term188 n m) = (term189 m n).
Proof. exact (MK_COMB (@lem2612106) (@lem2612105 m n)). Qed.
Lemma lem2612108 (m : int) (n : int) : (term185 m n) = (term190 m n).
Proof. exact (MK_COMB (@lem2612107 m n) (@lem2612104 n)). Qed.
Lemma lem2612110 (m : int) (n : int) : (term111 n m) = (term190 m n).
Proof. exact (TRANS (@lem2612101 m n) (@lem2612108 m n)). Qed.
Lemma lem2612113 (m : int) : (term123 m) = (term123 m).
Proof. exact (eq_refl (term123 m)). Qed.
Lemma lem2612114 (m : int) (n : int) : (term191 n m) = (term192 m n).
Proof. exact (MK_COMB (@lem2612113 m) (@lem2612110 m n)). Qed.
Lemma lem2612115 (m : int) (n : int) : (term192 m n) = (term193 m n).
Proof. exact (@lem1982792 (real_of_int m) (term190 m n)). Qed.
Lemma lem2612122 (m : int) (n : int) : (term194 m n) = (term195 m n).
Proof. exact (@lem1982781 (term70 m n) term131 (real_of_int n)). Qed.
Lemma lem2612123 (m : int) : (term83 m) = (term83 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem2612124 (m : int) (n : int) : (term193 m n) = (term196 m n).
Proof. exact (MK_COMB (@lem2612123 m) (@lem2612122 m n)). Qed.
Lemma lem2612129 (m : int) (n : int) : (term196 m n) = (term197 m n).
Proof. exact (@lem1982757 (term169 m n) (real_of_int m) (term198 n)). Qed.
Lemma lem2612130 (m : int) (n : int) : (term193 m n) = (term197 m n).
Proof. exact (TRANS (@lem2612124 m n) (@lem2612129 m n)). Qed.
Lemma lem2612131 (m : int) (n : int) : (term192 m n) = (term197 m n).
Proof. exact (TRANS (@lem2612115 m n) (@lem2612130 m n)). Qed.
Lemma lem2612132 (m : int) (n : int) : (term191 n m) = (term197 m n).
Proof. exact (TRANS (@lem2612114 m n) (@lem2612131 m n)). Qed.
Lemma lem2612133 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612134 (m : int) (n : int) : (term199 n m) = (term200 m n).
Proof. exact (MK_COMB (@lem2612133) (@lem2612132 m n)). Qed.
Lemma lem2612135 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612136 (m : int) (n : int) : (term184 n m) = (term201 m n).
Proof. exact (MK_COMB (@lem2612134 m n) (@lem2612135)). Qed.
Lemma lem2612137 (m : int) (n : int) : (term114 n m) = (term201 m n).
Proof. exact (TRANS (@lem2612087 n m) (@lem2612136 m n)). Qed.
Lemma lem2612138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2612139 (n : int) (m : int) : (term116 n m) = (term202 n m).
Proof. exact (MK_COMB (@lem2612138) (@lem2612086 n m)). Qed.
Lemma lem2612140 (m : int) (n : int) : (term117 n m) = (term203 m n).
Proof. exact (MK_COMB (@lem2612139 n m) (@lem2612137 m n)). Qed.
Lemma lem2612141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612142 (n : int) (m : int) : (term118 m n) = (term204 n m).
Proof. exact (MK_COMB (@lem2612141) (@lem2612001 n m)). Qed.
Lemma lem2612143 (m : int) (n : int) : (term119 n m) = (term205 m n).
Proof. exact (MK_COMB (@lem2612142 n m) (@lem2612140 m n)). Qed.
Lemma lem2612150 (m : int) (n : int) : (term121 n m) = (term205 m n).
Proof. exact (TRANS (@lem2611902 n m) (@lem2612143 m n)). Qed.
Lemma lem2612173 (m : int) (n : int) : (term205 m n) = (term206 m n).
Proof. exact (@lem19158 (term183 n m) (term163 n m) (term201 m n)). Qed.
Lemma lem2612174 (m : int) (n : int) : (term121 n m) = (term206 m n).
Proof. exact (TRANS (@lem2612150 m n) (@lem2612173 m n)). Qed.
Lemma lem2612176 (a : real) (x : real) (r : real) : (term207 a x r) = (term208 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2612177 (n : int) (m : int) : (term161 n m) = (term209 n m).
Proof. exact (@lem2612176 (term70 m n) (real_of_int m) term43). Qed.
Lemma lem2612184 (m : int) : (term187 m) = (real_of_int m).
Proof. exact (@lem1982733 (real_of_int m)). Qed.
Lemma lem2612195 (m : int) (n : int) : (term189 m n) = (term189 m n).
Proof. exact (eq_refl (term189 m n)). Qed.
Lemma lem2612198 (n : int) (m : int) : (term210 n m) = (term211 n m).
Proof. exact (MK_COMB (@lem2612195 m n) (@lem2612184 m)). Qed.
Lemma lem2612199 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612200 (n : int) (m : int) : (term212 n m) = (term213 n m).
Proof. exact (MK_COMB (@lem2612199) (@lem2612198 n m)). Qed.
Lemma lem2612201 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612202 (n : int) (m : int) : (term214 n m) = (term215 n m).
Proof. exact (MK_COMB (@lem2612200 n m) (@lem2612201)). Qed.
Lemma lem2612229 (n : int) (m : int) : (term216 n m) = (term216 n m).
Proof. exact (eq_refl (term216 n m)). Qed.
Lemma lem2612230 (n : int) (m : int) : (term209 n m) = (term217 n m).
Proof. exact (MK_COMB (@lem2612229 n m) (@lem2612202 n m)). Qed.
Lemma lem2612231 (n : int) (m : int) : (term161 n m) = (term217 n m).
Proof. exact (TRANS (@lem2612177 n m) (@lem2612230 n m)). Qed.
Lemma lem2612232 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2612233 (n : int) (m : int) : (term163 n m) = (term218 n m).
Proof. exact (MK_COMB (@lem2612232 n) (@lem2612231 n m)). Qed.
Lemma lem2612234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612235 (n : int) (m : int) : (term204 n m) = (term219 n m).
Proof. exact (MK_COMB (@lem2612234) (@lem2612233 n m)). Qed.
Lemma lem2612236 (n : int) (m : int) : (term183 n m) = (term183 n m).
Proof. exact (eq_refl (term183 n m)). Qed.
Lemma lem2612237 (n : int) (m : int) : (term220 n m) = (term221 n m).
Proof. exact (MK_COMB (@lem2612235 n m) (@lem2612236 n m)). Qed.
Lemma lem2612238 (n : int) (m : int) : (term222 n m) = (term221 n m).
Proof. exact (eq_refl (term222 n m)). Qed.
Lemma lem2612239 (n : int) (m : int) : (term221 n m) = (term222 n m).
Proof. exact (SYM (@lem2612238 n m)). Qed.
Lemma lem2612240 (n : int) (m : int) : (term222 n m) = (term223 n m).
Proof. exact (@lem1482981 (term224 n m) (real_of_int m)). Qed.
Lemma lem2612241 (n : int) (m : int) : (term221 n m) = (term223 n m).
Proof. exact (TRANS (@lem2612239 n m) (@lem2612240 n m)). Qed.
Lemma lem2612242 (n : int) (m : int) : (term225 n m) = (term226 n m).
Proof. exact (eq_refl (term225 n m)). Qed.
Lemma lem2612243 (m : int) : (term227 m) = (term227 m).
Proof. exact (eq_refl (term227 m)). Qed.
Lemma lem2612244 (n : int) (m : int) : (term228 n m) = (term229 n m).
Proof. exact (MK_COMB (@lem2612243 m) (@lem2612242 n m)). Qed.
Lemma lem2612245 (n : int) (m : int) : (term230 n m) = (term231 n m).
Proof. exact (eq_refl (term230 n m)). Qed.
Lemma lem2612246 (m : int) : (term232 m) = (term232 m).
Proof. exact (eq_refl (term232 m)). Qed.
Lemma lem2612247 (n : int) (m : int) : (term233 n m) = (term234 n m).
Proof. exact (MK_COMB (@lem2612246 m) (@lem2612245 n m)). Qed.
Lemma lem2612248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2612249 (n : int) (m : int) : (term235 n m) = (term236 n m).
Proof. exact (MK_COMB (@lem2612248) (@lem2612247 n m)). Qed.
Lemma lem2612250 (n : int) (m : int) : (term223 n m) = (term237 n m).
Proof. exact (MK_COMB (@lem2612249 n m) (@lem2612244 n m)). Qed.
Lemma lem2612251 (n : int) (m : int) : (term238 n m) = (term238 n m).
Proof. exact (eq_refl (term238 n m)). Qed.
Lemma lem2612252 (n : int) (m : int) : ((term221 n m) = (term223 n m)) = ((term221 n m) = (term237 n m)).
Proof. exact (MK_COMB (@lem2612251 n m) (@lem2612250 n m)). Qed.
Lemma lem2612253 (n : int) (m : int) : (term221 n m) = (term237 n m).
Proof. exact (EQ_MP (@lem2612252 n m) (@lem2612241 n m)). Qed.
Lemma lem2612254 (m : int) : (term239 m) = (term240 m).
Proof. exact (@lem1988291 (real_of_int m) term43). Qed.
Lemma lem2612260 (m : int) : (term241 m) = (term242 m).
Proof. exact (@lem1982792 (real_of_int m) term43). Qed.
Lemma lem2612262 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612263 : term43 = term243.
Proof. exact (@lem2612262 (NUMERAL 0)). Qed.
Lemma lem2612265 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612266 : term131 = term132.
Proof. exact (@lem2612265 term48). Qed.
Lemma lem2612267 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612268 : term133 = term134.
Proof. exact (MK_COMB (@lem2612267) (@lem2612266)). Qed.
Lemma lem2612269 : term244 = term245.
Proof. exact (MK_COMB (@lem2612268) (@lem2612263)). Qed.
Lemma lem2612270 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2612272 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612273 : term140 = term141.
Proof. exact (@lem2612272 term48 term48). Qed.
Lemma lem2612274 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612275 : term143 = term48.
Proof. exact (EQ_MP (@lem2612274) (@lem940073)). Qed.
Lemma lem2612276 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612277 : term141 = term47.
Proof. exact (MK_COMB (@lem2612276) (@lem2612275)). Qed.
Lemma lem2612278 : term140 = term47.
Proof. exact (TRANS (@lem2612273) (@lem2612277)). Qed.
Lemma lem2612280 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2612281 : term244 = term43.
Proof. exact (@lem2612280 term48). Qed.
Lemma lem2612282 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612283 : term248 = term249.
Proof. exact (MK_COMB (@lem2612282) (@lem2612281)). Qed.
Lemma lem2612284 : term246 = term243.
Proof. exact (MK_COMB (@lem2612283) (@lem2612278)). Qed.
Lemma lem2612285 : term245 = term243.
Proof. exact (TRANS (@lem2612270) (@lem2612284)). Qed.
Lemma lem2612286 : term244 = term243.
Proof. exact (TRANS (@lem2612269) (@lem2612285)). Qed.
Lemma lem2612288 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612289 : term243 = term43.
Proof. exact (@lem2612288 term43). Qed.
Lemma lem2612290 : term244 = term43.
Proof. exact (TRANS (@lem2612286) (@lem2612289)). Qed.
Lemma lem2612291 (m : int) : (term83 m) = (term83 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem2612292 (m : int) : (term242 m) = (term250 m).
Proof. exact (MK_COMB (@lem2612291 m) (@lem2612290)). Qed.
Lemma lem2612293 (m : int) : (term250 m) = (real_of_int m).
Proof. exact (@lem1982723 (real_of_int m)). Qed.
Lemma lem2612294 (m : int) : (term242 m) = (real_of_int m).
Proof. exact (TRANS (@lem2612292 m) (@lem2612293 m)). Qed.
Lemma lem2612296 (m : int) : (term241 m) = (real_of_int m).
Proof. exact (TRANS (@lem2612260 m) (@lem2612294 m)). Qed.
Lemma lem2612297 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612298 (m : int) : (term251 m) = (term252 m).
Proof. exact (MK_COMB (@lem2612297) (@lem2612296 m)). Qed.
Lemma lem2612299 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612300 (m : int) : (term240 m) = (term239 m).
Proof. exact (MK_COMB (@lem2612298 m) (@lem2612299)). Qed.
Lemma lem2612301 (m : int) : (term239 m) = (term239 m).
Proof. exact (TRANS (@lem2612254 m) (@lem2612300 m)). Qed.
Lemma lem2612302 (n : int) : (term153 n) = (term253 n).
Proof. exact (@lem1988291 (term150 n) term43). Qed.
Lemma lem2612314 (n : int) : (term254 n) = (term255 n).
Proof. exact (@lem1982792 (term150 n) term43). Qed.
Lemma lem2612316 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612317 : term43 = term243.
Proof. exact (@lem2612316 (NUMERAL 0)). Qed.
Lemma lem2612319 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612320 : term131 = term132.
Proof. exact (@lem2612319 term48). Qed.
Lemma lem2612321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612322 : term133 = term134.
Proof. exact (MK_COMB (@lem2612321) (@lem2612320)). Qed.
Lemma lem2612323 : term244 = term245.
Proof. exact (MK_COMB (@lem2612322) (@lem2612317)). Qed.
Lemma lem2612324 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2612326 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612327 : term140 = term141.
Proof. exact (@lem2612326 term48 term48). Qed.
Lemma lem2612328 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612329 : term143 = term48.
Proof. exact (EQ_MP (@lem2612328) (@lem940073)). Qed.
Lemma lem2612330 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612331 : term141 = term47.
Proof. exact (MK_COMB (@lem2612330) (@lem2612329)). Qed.
Lemma lem2612332 : term140 = term47.
Proof. exact (TRANS (@lem2612327) (@lem2612331)). Qed.
Lemma lem2612334 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2612335 : term244 = term43.
Proof. exact (@lem2612334 term48). Qed.
Lemma lem2612336 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612337 : term248 = term249.
Proof. exact (MK_COMB (@lem2612336) (@lem2612335)). Qed.
Lemma lem2612338 : term246 = term243.
Proof. exact (MK_COMB (@lem2612337) (@lem2612332)). Qed.
Lemma lem2612339 : term245 = term243.
Proof. exact (TRANS (@lem2612324) (@lem2612338)). Qed.
Lemma lem2612340 : term244 = term243.
Proof. exact (TRANS (@lem2612323) (@lem2612339)). Qed.
Lemma lem2612342 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612343 : term243 = term43.
Proof. exact (@lem2612342 term43). Qed.
Lemma lem2612344 : term244 = term43.
Proof. exact (TRANS (@lem2612340) (@lem2612343)). Qed.
Lemma lem2612345 (n : int) : (term256 n) = (term256 n).
Proof. exact (eq_refl (term256 n)). Qed.
Lemma lem2612346 (n : int) : (term255 n) = (term257 n).
Proof. exact (MK_COMB (@lem2612345 n) (@lem2612344)). Qed.
Lemma lem2612347 (n : int) : (term257 n) = (term150 n).
Proof. exact (@lem1982723 (term150 n)). Qed.
Lemma lem2612348 (n : int) : (term255 n) = (term150 n).
Proof. exact (TRANS (@lem2612346 n) (@lem2612347 n)). Qed.
Lemma lem2612350 (n : int) : (term254 n) = (term150 n).
Proof. exact (TRANS (@lem2612314 n) (@lem2612348 n)). Qed.
Lemma lem2612351 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612352 (n : int) : (term258 n) = (term152 n).
Proof. exact (MK_COMB (@lem2612351) (@lem2612350 n)). Qed.
Lemma lem2612353 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612354 (n : int) : (term253 n) = (term153 n).
Proof. exact (MK_COMB (@lem2612352 n) (@lem2612353)). Qed.
Lemma lem2612355 (n : int) : (term153 n) = (term153 n).
Proof. exact (TRANS (@lem2612302 n) (@lem2612354 n)). Qed.
Lemma lem2612356 (n : int) (m : int) : (term259 n m) = (term260 n m).
Proof. exact (@lem1988291 (term261 n m) term43). Qed.
Lemma lem2612380 (n : int) (m : int) : (term262 n m) = (term263 n m).
Proof. exact (@lem1982792 (term261 n m) term43). Qed.
Lemma lem2612382 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612383 : term43 = term243.
Proof. exact (@lem2612382 (NUMERAL 0)). Qed.
Lemma lem2612385 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612386 : term131 = term132.
Proof. exact (@lem2612385 term48). Qed.
Lemma lem2612387 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612388 : term133 = term134.
Proof. exact (MK_COMB (@lem2612387) (@lem2612386)). Qed.
Lemma lem2612389 : term244 = term245.
Proof. exact (MK_COMB (@lem2612388) (@lem2612383)). Qed.
Lemma lem2612390 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2612392 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612393 : term140 = term141.
Proof. exact (@lem2612392 term48 term48). Qed.
Lemma lem2612394 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612395 : term143 = term48.
Proof. exact (EQ_MP (@lem2612394) (@lem940073)). Qed.
Lemma lem2612396 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612397 : term141 = term47.
Proof. exact (MK_COMB (@lem2612396) (@lem2612395)). Qed.
Lemma lem2612398 : term140 = term47.
Proof. exact (TRANS (@lem2612393) (@lem2612397)). Qed.
Lemma lem2612400 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2612401 : term244 = term43.
Proof. exact (@lem2612400 term48). Qed.
Lemma lem2612402 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612403 : term248 = term249.
Proof. exact (MK_COMB (@lem2612402) (@lem2612401)). Qed.
Lemma lem2612404 : term246 = term243.
Proof. exact (MK_COMB (@lem2612403) (@lem2612398)). Qed.
Lemma lem2612405 : term245 = term243.
Proof. exact (TRANS (@lem2612390) (@lem2612404)). Qed.
Lemma lem2612406 : term244 = term243.
Proof. exact (TRANS (@lem2612389) (@lem2612405)). Qed.
Lemma lem2612408 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612409 : term243 = term43.
Proof. exact (@lem2612408 term43). Qed.
Lemma lem2612410 : term244 = term43.
Proof. exact (TRANS (@lem2612406) (@lem2612409)). Qed.
Lemma lem2612411 (n : int) (m : int) : (term264 n m) = (term264 n m).
Proof. exact (eq_refl (term264 n m)). Qed.
Lemma lem2612412 (n : int) (m : int) : (term263 n m) = (term265 n m).
Proof. exact (MK_COMB (@lem2612411 n m) (@lem2612410)). Qed.
Lemma lem2612413 (n : int) (m : int) : (term265 n m) = (term261 n m).
Proof. exact (@lem1982723 (term261 n m)). Qed.
Lemma lem2612414 (n : int) (m : int) : (term263 n m) = (term261 n m).
Proof. exact (TRANS (@lem2612412 n m) (@lem2612413 n m)). Qed.
Lemma lem2612416 (n : int) (m : int) : (term262 n m) = (term261 n m).
Proof. exact (TRANS (@lem2612380 n m) (@lem2612414 n m)). Qed.
Lemma lem2612417 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612418 (n : int) (m : int) : (term266 n m) = (term267 n m).
Proof. exact (MK_COMB (@lem2612417) (@lem2612416 n m)). Qed.
Lemma lem2612419 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612420 (n : int) (m : int) : (term260 n m) = (term259 n m).
Proof. exact (MK_COMB (@lem2612418 n m) (@lem2612419)). Qed.
Lemma lem2612421 (n : int) (m : int) : (term259 n m) = (term259 n m).
Proof. exact (TRANS (@lem2612356 n m) (@lem2612420 n m)). Qed.
Lemma lem2612422 (n : int) (m : int) : (term268 n m) = (term269 n m).
Proof. exact (@lem1988291 (term270 n m) term43). Qed.
Lemma lem2612440 (n : int) (m : int) : (term271 n m) = (term272 n m).
Proof. exact (@lem1982792 (term270 n m) term43). Qed.
Lemma lem2612442 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612443 : term43 = term243.
Proof. exact (@lem2612442 (NUMERAL 0)). Qed.
Lemma lem2612445 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612446 : term131 = term132.
Proof. exact (@lem2612445 term48). Qed.
Lemma lem2612447 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612448 : term133 = term134.
Proof. exact (MK_COMB (@lem2612447) (@lem2612446)). Qed.
Lemma lem2612449 : term244 = term245.
Proof. exact (MK_COMB (@lem2612448) (@lem2612443)). Qed.
Lemma lem2612450 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2612452 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612453 : term140 = term141.
Proof. exact (@lem2612452 term48 term48). Qed.
Lemma lem2612454 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612455 : term143 = term48.
Proof. exact (EQ_MP (@lem2612454) (@lem940073)). Qed.
Lemma lem2612456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612457 : term141 = term47.
Proof. exact (MK_COMB (@lem2612456) (@lem2612455)). Qed.
Lemma lem2612458 : term140 = term47.
Proof. exact (TRANS (@lem2612453) (@lem2612457)). Qed.
Lemma lem2612460 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2612461 : term244 = term43.
Proof. exact (@lem2612460 term48). Qed.
Lemma lem2612462 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612463 : term248 = term249.
Proof. exact (MK_COMB (@lem2612462) (@lem2612461)). Qed.
Lemma lem2612464 : term246 = term243.
Proof. exact (MK_COMB (@lem2612463) (@lem2612458)). Qed.
Lemma lem2612465 : term245 = term243.
Proof. exact (TRANS (@lem2612450) (@lem2612464)). Qed.
Lemma lem2612466 : term244 = term243.
Proof. exact (TRANS (@lem2612449) (@lem2612465)). Qed.
Lemma lem2612468 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612469 : term243 = term43.
Proof. exact (@lem2612468 term43). Qed.
Lemma lem2612470 : term244 = term43.
Proof. exact (TRANS (@lem2612466) (@lem2612469)). Qed.
Lemma lem2612471 (n : int) (m : int) : (term273 n m) = (term273 n m).
Proof. exact (eq_refl (term273 n m)). Qed.
Lemma lem2612472 (n : int) (m : int) : (term272 n m) = (term274 n m).
Proof. exact (MK_COMB (@lem2612471 n m) (@lem2612470)). Qed.
Lemma lem2612473 (n : int) (m : int) : (term274 n m) = (term270 n m).
Proof. exact (@lem1982723 (term270 n m)). Qed.
Lemma lem2612474 (n : int) (m : int) : (term272 n m) = (term270 n m).
Proof. exact (TRANS (@lem2612472 n m) (@lem2612473 n m)). Qed.
Lemma lem2612476 (n : int) (m : int) : (term271 n m) = (term270 n m).
Proof. exact (TRANS (@lem2612440 n m) (@lem2612474 n m)). Qed.
Lemma lem2612477 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612478 (n : int) (m : int) : (term275 n m) = (term276 n m).
Proof. exact (MK_COMB (@lem2612477) (@lem2612476 n m)). Qed.
Lemma lem2612479 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612480 (n : int) (m : int) : (term269 n m) = (term268 n m).
Proof. exact (MK_COMB (@lem2612478 n m) (@lem2612479)). Qed.
Lemma lem2612481 (n : int) (m : int) : (term268 n m) = (term268 n m).
Proof. exact (TRANS (@lem2612422 n m) (@lem2612480 n m)). Qed.
Lemma lem2612482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612483 (n : int) (m : int) : (term277 n m) = (term277 n m).
Proof. exact (MK_COMB (@lem2612482) (@lem2612421 n m)). Qed.
Lemma lem2612484 (n : int) (m : int) : (term278 n m) = (term278 n m).
Proof. exact (MK_COMB (@lem2612483 n m) (@lem2612481 n m)). Qed.
Lemma lem2612485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612486 (n : int) : (term162 n) = (term162 n).
Proof. exact (MK_COMB (@lem2612485) (@lem2612355 n)). Qed.
Lemma lem2612487 (n : int) (m : int) : (term279 n m) = (term279 n m).
Proof. exact (MK_COMB (@lem2612486 n) (@lem2612484 n m)). Qed.
Lemma lem2612488 (n : int) (m : int) : (term280 n m) = (term281 n m).
Proof. exact (@lem1988291 (term282 n m) term43). Qed.
Lemma lem2612524 (n : int) (m : int) : (term283 n m) = (term284 n m).
Proof. exact (@lem1982792 (term282 n m) term43). Qed.
Lemma lem2612526 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612527 : term43 = term243.
Proof. exact (@lem2612526 (NUMERAL 0)). Qed.
Lemma lem2612529 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612530 : term131 = term132.
Proof. exact (@lem2612529 term48). Qed.
Lemma lem2612531 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612532 : term133 = term134.
Proof. exact (MK_COMB (@lem2612531) (@lem2612530)). Qed.
Lemma lem2612533 : term244 = term245.
Proof. exact (MK_COMB (@lem2612532) (@lem2612527)). Qed.
Lemma lem2612534 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2612536 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612537 : term140 = term141.
Proof. exact (@lem2612536 term48 term48). Qed.
Lemma lem2612538 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612539 : term143 = term48.
Proof. exact (EQ_MP (@lem2612538) (@lem940073)). Qed.
Lemma lem2612540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612541 : term141 = term47.
Proof. exact (MK_COMB (@lem2612540) (@lem2612539)). Qed.
Lemma lem2612542 : term140 = term47.
Proof. exact (TRANS (@lem2612537) (@lem2612541)). Qed.
Lemma lem2612544 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2612545 : term244 = term43.
Proof. exact (@lem2612544 term48). Qed.
Lemma lem2612546 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612547 : term248 = term249.
Proof. exact (MK_COMB (@lem2612546) (@lem2612545)). Qed.
Lemma lem2612548 : term246 = term243.
Proof. exact (MK_COMB (@lem2612547) (@lem2612542)). Qed.
Lemma lem2612549 : term245 = term243.
Proof. exact (TRANS (@lem2612534) (@lem2612548)). Qed.
Lemma lem2612550 : term244 = term243.
Proof. exact (TRANS (@lem2612533) (@lem2612549)). Qed.
Lemma lem2612552 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612553 : term243 = term43.
Proof. exact (@lem2612552 term43). Qed.
Lemma lem2612554 : term244 = term43.
Proof. exact (TRANS (@lem2612550) (@lem2612553)). Qed.
Lemma lem2612555 (n : int) (m : int) : (term285 n m) = (term285 n m).
Proof. exact (eq_refl (term285 n m)). Qed.
Lemma lem2612556 (n : int) (m : int) : (term284 n m) = (term286 n m).
Proof. exact (MK_COMB (@lem2612555 n m) (@lem2612554)). Qed.
Lemma lem2612557 (n : int) (m : int) : (term286 n m) = (term282 n m).
Proof. exact (@lem1982723 (term282 n m)). Qed.
Lemma lem2612558 (n : int) (m : int) : (term284 n m) = (term282 n m).
Proof. exact (TRANS (@lem2612556 n m) (@lem2612557 n m)). Qed.
Lemma lem2612560 (n : int) (m : int) : (term283 n m) = (term282 n m).
Proof. exact (TRANS (@lem2612524 n m) (@lem2612558 n m)). Qed.
Lemma lem2612561 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612562 (n : int) (m : int) : (term287 n m) = (term288 n m).
Proof. exact (MK_COMB (@lem2612561) (@lem2612560 n m)). Qed.
Lemma lem2612563 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612564 (n : int) (m : int) : (term281 n m) = (term280 n m).
Proof. exact (MK_COMB (@lem2612562 n m) (@lem2612563)). Qed.
Lemma lem2612565 (n : int) (m : int) : (term280 n m) = (term280 n m).
Proof. exact (TRANS (@lem2612488 n m) (@lem2612564 n m)). Qed.
Lemma lem2612566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612567 (n : int) (m : int) : (term289 n m) = (term289 n m).
Proof. exact (MK_COMB (@lem2612566) (@lem2612487 n m)). Qed.
Lemma lem2612568 (n : int) (m : int) : (term231 n m) = (term231 n m).
Proof. exact (MK_COMB (@lem2612567 n m) (@lem2612565 n m)). Qed.
Lemma lem2612569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612570 (m : int) : (term232 m) = (term232 m).
Proof. exact (MK_COMB (@lem2612569) (@lem2612301 m)). Qed.
Lemma lem2612571 (n : int) (m : int) : (term234 n m) = (term234 n m).
Proof. exact (MK_COMB (@lem2612570 m) (@lem2612568 n m)). Qed.
Lemma lem2612572 (m : int) : (term290 m) = (term291 m).
Proof. exact (@lem1988289 term43 (real_of_int m)). Qed.
Lemma lem2612578 (m : int) : (term292 m) = (term293 m).
Proof. exact (@lem1982792 term43 (real_of_int m)). Qed.
Lemma lem2612583 (m : int) : (term293 m) = (term198 m).
Proof. exact (@lem1982721 (term198 m)). Qed.
Lemma lem2612585 (m : int) : (term292 m) = (term198 m).
Proof. exact (TRANS (@lem2612578 m) (@lem2612583 m)). Qed.
Lemma lem2612586 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2612587 (m : int) : (term294 m) = (term295 m).
Proof. exact (MK_COMB (@lem2612586) (@lem2612585 m)). Qed.
Lemma lem2612588 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612589 (m : int) : (term291 m) = (term296 m).
Proof. exact (MK_COMB (@lem2612587 m) (@lem2612588)). Qed.
Lemma lem2612590 (m : int) : (term290 m) = (term296 m).
Proof. exact (TRANS (@lem2612572 m) (@lem2612589 m)). Qed.
Lemma lem2612591 (n : int) (m : int) : (term297 n m) = (term298 n m).
Proof. exact (@lem1988291 (term299 n m) term43). Qed.
Lemma lem2612592 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612599 (m : int) : (term198 m) = (term198 m).
Proof. exact (eq_refl (term198 m)). Qed.
Lemma lem2612600 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2612607 (m : int) : (term91 m) = (term198 m).
Proof. exact (@lem1982785 (real_of_int m)). Qed.
Lemma lem2612608 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612609 (m : int) : (term300 m) = (term301 m).
Proof. exact (MK_COMB (@lem2612608) (@lem2612607 m)). Qed.
Lemma lem2612610 (m : int) (n : int) : (term302 m n) = (term303 m n).
Proof. exact (MK_COMB (@lem2612609 m) (@lem2612600 n)). Qed.
Lemma lem2612615 (m : int) (n : int) : (term303 m n) = (term304 m n).
Proof. exact (@lem1982745 term131 (real_of_int m) (real_of_int n)). Qed.
Lemma lem2612616 (m : int) (n : int) : (term302 m n) = (term304 m n).
Proof. exact (TRANS (@lem2612610 m n) (@lem2612615 m n)). Qed.
Lemma lem2612617 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2612618 (m : int) (n : int) : (term305 m n) = (term306 m n).
Proof. exact (MK_COMB (@lem2612617) (@lem2612616 m n)). Qed.
Lemma lem2612621 (n : int) (m : int) : (term299 n m) = (term307 n m).
Proof. exact (MK_COMB (@lem2612618 m n) (@lem2612599 m)). Qed.
Lemma lem2612622 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2612623 (n : int) (m : int) : (term308 n m) = (term309 n m).
Proof. exact (MK_COMB (@lem2612622) (@lem2612621 n m)). Qed.
Lemma lem2612624 (n : int) (m : int) : (term310 n m) = (term311 n m).
Proof. exact (MK_COMB (@lem2612623 n m) (@lem2612592)). Qed.
Lemma lem2612625 (n : int) (m : int) : (term311 n m) = (term312 n m).
Proof. exact (@lem1982792 (term307 n m) term43). Qed.
Lemma lem2612627 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612628 : term43 = term243.
Proof. exact (@lem2612627 (NUMERAL 0)). Qed.
Lemma lem2612630 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612631 : term131 = term132.
Proof. exact (@lem2612630 term48). Qed.
Lemma lem2612632 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612633 : term133 = term134.
Proof. exact (MK_COMB (@lem2612632) (@lem2612631)). Qed.
Lemma lem2612634 : term244 = term245.
Proof. exact (MK_COMB (@lem2612633) (@lem2612628)). Qed.
Lemma lem2612635 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2612637 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612638 : term140 = term141.
Proof. exact (@lem2612637 term48 term48). Qed.
Lemma lem2612639 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612640 : term143 = term48.
Proof. exact (EQ_MP (@lem2612639) (@lem940073)). Qed.
Lemma lem2612641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612642 : term141 = term47.
Proof. exact (MK_COMB (@lem2612641) (@lem2612640)). Qed.
Lemma lem2612643 : term140 = term47.
Proof. exact (TRANS (@lem2612638) (@lem2612642)). Qed.
Lemma lem2612645 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2612646 : term244 = term43.
Proof. exact (@lem2612645 term48). Qed.
Lemma lem2612647 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612648 : term248 = term249.
Proof. exact (MK_COMB (@lem2612647) (@lem2612646)). Qed.
Lemma lem2612649 : term246 = term243.
Proof. exact (MK_COMB (@lem2612648) (@lem2612643)). Qed.
Lemma lem2612650 : term245 = term243.
Proof. exact (TRANS (@lem2612635) (@lem2612649)). Qed.
Lemma lem2612651 : term244 = term243.
Proof. exact (TRANS (@lem2612634) (@lem2612650)). Qed.
Lemma lem2612653 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612654 : term243 = term43.
Proof. exact (@lem2612653 term43). Qed.
Lemma lem2612655 : term244 = term43.
Proof. exact (TRANS (@lem2612651) (@lem2612654)). Qed.
Lemma lem2612656 (n : int) (m : int) : (term313 n m) = (term313 n m).
Proof. exact (eq_refl (term313 n m)). Qed.
Lemma lem2612657 (n : int) (m : int) : (term312 n m) = (term314 n m).
Proof. exact (MK_COMB (@lem2612656 n m) (@lem2612655)). Qed.
Lemma lem2612658 (n : int) (m : int) : (term314 n m) = (term307 n m).
Proof. exact (@lem1982723 (term307 n m)). Qed.
Lemma lem2612659 (n : int) (m : int) : (term312 n m) = (term307 n m).
Proof. exact (TRANS (@lem2612657 n m) (@lem2612658 n m)). Qed.
Lemma lem2612660 (n : int) (m : int) : (term311 n m) = (term307 n m).
Proof. exact (TRANS (@lem2612625 n m) (@lem2612659 n m)). Qed.
Lemma lem2612661 (n : int) (m : int) : (term310 n m) = (term307 n m).
Proof. exact (TRANS (@lem2612624 n m) (@lem2612660 n m)). Qed.
Lemma lem2612662 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612663 (n : int) (m : int) : (term315 n m) = (term316 n m).
Proof. exact (MK_COMB (@lem2612662) (@lem2612661 n m)). Qed.
Lemma lem2612664 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612665 (n : int) (m : int) : (term298 n m) = (term317 n m).
Proof. exact (MK_COMB (@lem2612663 n m) (@lem2612664)). Qed.
Lemma lem2612666 (n : int) (m : int) : (term297 n m) = (term317 n m).
Proof. exact (TRANS (@lem2612591 n m) (@lem2612665 n m)). Qed.
Lemma lem2612667 (n : int) (m : int) : (term318 n m) = (term319 n m).
Proof. exact (@lem1988291 (term320 n m) term43). Qed.
Lemma lem2612668 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612669 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2612670 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2612677 (m : int) : (term91 m) = (term198 m).
Proof. exact (@lem1982785 (real_of_int m)). Qed.
Lemma lem2612678 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612679 (m : int) : (term300 m) = (term301 m).
Proof. exact (MK_COMB (@lem2612678) (@lem2612677 m)). Qed.
Lemma lem2612680 (m : int) (n : int) : (term302 m n) = (term303 m n).
Proof. exact (MK_COMB (@lem2612679 m) (@lem2612670 n)). Qed.
Lemma lem2612685 (m : int) (n : int) : (term303 m n) = (term304 m n).
Proof. exact (@lem1982745 term131 (real_of_int m) (real_of_int n)). Qed.
Lemma lem2612686 (m : int) (n : int) : (term302 m n) = (term304 m n).
Proof. exact (TRANS (@lem2612680 m n) (@lem2612685 m n)). Qed.
Lemma lem2612687 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2612688 (m : int) (n : int) : (term305 m n) = (term306 m n).
Proof. exact (MK_COMB (@lem2612687) (@lem2612686 m n)). Qed.
Lemma lem2612691 (n : int) (m : int) : (term320 n m) = (term321 n m).
Proof. exact (MK_COMB (@lem2612688 m n) (@lem2612669 m)). Qed.
Lemma lem2612692 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2612693 (n : int) (m : int) : (term322 n m) = (term323 n m).
Proof. exact (MK_COMB (@lem2612692) (@lem2612691 n m)). Qed.
Lemma lem2612694 (n : int) (m : int) : (term324 n m) = (term325 n m).
Proof. exact (MK_COMB (@lem2612693 n m) (@lem2612668)). Qed.
Lemma lem2612695 (n : int) (m : int) : (term325 n m) = (term326 n m).
Proof. exact (@lem1982792 (term321 n m) term43). Qed.
Lemma lem2612697 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612698 : term43 = term243.
Proof. exact (@lem2612697 (NUMERAL 0)). Qed.
Lemma lem2612700 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612701 : term131 = term132.
Proof. exact (@lem2612700 term48). Qed.
Lemma lem2612702 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612703 : term133 = term134.
Proof. exact (MK_COMB (@lem2612702) (@lem2612701)). Qed.
Lemma lem2612704 : term244 = term245.
Proof. exact (MK_COMB (@lem2612703) (@lem2612698)). Qed.
Lemma lem2612705 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2612707 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612708 : term140 = term141.
Proof. exact (@lem2612707 term48 term48). Qed.
Lemma lem2612709 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612710 : term143 = term48.
Proof. exact (EQ_MP (@lem2612709) (@lem940073)). Qed.
Lemma lem2612711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612712 : term141 = term47.
Proof. exact (MK_COMB (@lem2612711) (@lem2612710)). Qed.
Lemma lem2612713 : term140 = term47.
Proof. exact (TRANS (@lem2612708) (@lem2612712)). Qed.
Lemma lem2612715 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2612716 : term244 = term43.
Proof. exact (@lem2612715 term48). Qed.
Lemma lem2612717 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612718 : term248 = term249.
Proof. exact (MK_COMB (@lem2612717) (@lem2612716)). Qed.
Lemma lem2612719 : term246 = term243.
Proof. exact (MK_COMB (@lem2612718) (@lem2612713)). Qed.
Lemma lem2612720 : term245 = term243.
Proof. exact (TRANS (@lem2612705) (@lem2612719)). Qed.
Lemma lem2612721 : term244 = term243.
Proof. exact (TRANS (@lem2612704) (@lem2612720)). Qed.
Lemma lem2612723 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612724 : term243 = term43.
Proof. exact (@lem2612723 term43). Qed.
Lemma lem2612725 : term244 = term43.
Proof. exact (TRANS (@lem2612721) (@lem2612724)). Qed.
Lemma lem2612726 (n : int) (m : int) : (term327 n m) = (term327 n m).
Proof. exact (eq_refl (term327 n m)). Qed.
Lemma lem2612727 (n : int) (m : int) : (term326 n m) = (term328 n m).
Proof. exact (MK_COMB (@lem2612726 n m) (@lem2612725)). Qed.
Lemma lem2612728 (n : int) (m : int) : (term328 n m) = (term321 n m).
Proof. exact (@lem1982723 (term321 n m)). Qed.
Lemma lem2612729 (n : int) (m : int) : (term326 n m) = (term321 n m).
Proof. exact (TRANS (@lem2612727 n m) (@lem2612728 n m)). Qed.
Lemma lem2612730 (n : int) (m : int) : (term325 n m) = (term321 n m).
Proof. exact (TRANS (@lem2612695 n m) (@lem2612729 n m)). Qed.
Lemma lem2612731 (n : int) (m : int) : (term324 n m) = (term321 n m).
Proof. exact (TRANS (@lem2612694 n m) (@lem2612730 n m)). Qed.
Lemma lem2612732 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612733 (n : int) (m : int) : (term329 n m) = (term330 n m).
Proof. exact (MK_COMB (@lem2612732) (@lem2612731 n m)). Qed.
Lemma lem2612734 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612735 (n : int) (m : int) : (term319 n m) = (term331 n m).
Proof. exact (MK_COMB (@lem2612733 n m) (@lem2612734)). Qed.
Lemma lem2612736 (n : int) (m : int) : (term318 n m) = (term331 n m).
Proof. exact (TRANS (@lem2612667 n m) (@lem2612735 n m)). Qed.
Lemma lem2612737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612738 (n : int) (m : int) : (term332 n m) = (term333 n m).
Proof. exact (MK_COMB (@lem2612737) (@lem2612666 n m)). Qed.
Lemma lem2612739 (n : int) (m : int) : (term334 n m) = (term335 n m).
Proof. exact (MK_COMB (@lem2612738 n m) (@lem2612736 n m)). Qed.
Lemma lem2612740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612741 (n : int) : (term162 n) = (term162 n).
Proof. exact (MK_COMB (@lem2612740) (@lem2612355 n)). Qed.
Lemma lem2612742 (n : int) (m : int) : (term336 n m) = (term337 n m).
Proof. exact (MK_COMB (@lem2612741 n) (@lem2612739 n m)). Qed.
Lemma lem2612743 (n : int) (m : int) : (term338 n m) = (term339 n m).
Proof. exact (@lem1988291 (term340 n m) term43). Qed.
Lemma lem2612744 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612757 (m : int) : (term178 m) = (term178 m).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem2612758 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2612765 (m : int) : (term91 m) = (term198 m).
Proof. exact (@lem1982785 (real_of_int m)). Qed.
Lemma lem2612766 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612767 (m : int) : (term300 m) = (term301 m).
Proof. exact (MK_COMB (@lem2612766) (@lem2612765 m)). Qed.
Lemma lem2612768 (m : int) (n : int) : (term302 m n) = (term303 m n).
Proof. exact (MK_COMB (@lem2612767 m) (@lem2612758 n)). Qed.
Lemma lem2612773 (m : int) (n : int) : (term303 m n) = (term304 m n).
Proof. exact (@lem1982745 term131 (real_of_int m) (real_of_int n)). Qed.
Lemma lem2612774 (m : int) (n : int) : (term302 m n) = (term304 m n).
Proof. exact (TRANS (@lem2612768 m n) (@lem2612773 m n)). Qed.
Lemma lem2612777 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem2612778 (m : int) (n : int) : (term341 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem2612777) (@lem2612774 m n)). Qed.
Lemma lem2612779 (m : int) (n : int) : (term342 m n) = (term343 m n).
Proof. exact (@lem1982749 term131 term131 (term58 m n)). Qed.
Lemma lem2612781 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612782 : term131 = term132.
Proof. exact (@lem2612781 term48). Qed.
Lemma lem2612784 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612785 : term131 = term132.
Proof. exact (@lem2612784 term48). Qed.
Lemma lem2612786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612787 : term133 = term134.
Proof. exact (MK_COMB (@lem2612786) (@lem2612785)). Qed.
Lemma lem2612788 : term344 = term345.
Proof. exact (MK_COMB (@lem2612787) (@lem2612782)). Qed.
Lemma lem2612789 : term345 = term346.
Proof. exact (@lem1981613 term131 term131 term47 term47). Qed.
Lemma lem2612791 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612792 : term140 = term141.
Proof. exact (@lem2612791 term48 term48). Qed.
Lemma lem2612793 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612794 : term143 = term48.
Proof. exact (EQ_MP (@lem2612793) (@lem940073)). Qed.
Lemma lem2612795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612796 : term141 = term47.
Proof. exact (MK_COMB (@lem2612795) (@lem2612794)). Qed.
Lemma lem2612797 : term140 = term47.
Proof. exact (TRANS (@lem2612792) (@lem2612796)). Qed.
Lemma lem2612799 (m : nat) (n : nat) : (term347 m n) = (term139 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2612800 : term344 = term141.
Proof. exact (@lem2612799 term48 term48). Qed.
Lemma lem2612801 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612802 : term143 = term48.
Proof. exact (EQ_MP (@lem2612801) (@lem940073)). Qed.
Lemma lem2612803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612804 : term141 = term47.
Proof. exact (MK_COMB (@lem2612803) (@lem2612802)). Qed.
Lemma lem2612805 : term344 = term47.
Proof. exact (TRANS (@lem2612800) (@lem2612804)). Qed.
Lemma lem2612806 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612807 : term348 = term349.
Proof. exact (MK_COMB (@lem2612806) (@lem2612805)). Qed.
Lemma lem2612808 : term346 = term128.
Proof. exact (MK_COMB (@lem2612807) (@lem2612797)). Qed.
Lemma lem2612809 : term345 = term128.
Proof. exact (TRANS (@lem2612789) (@lem2612808)). Qed.
Lemma lem2612810 : term344 = term128.
Proof. exact (TRANS (@lem2612788) (@lem2612809)). Qed.
Lemma lem2612812 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612813 : term128 = term47.
Proof. exact (@lem2612812 term47). Qed.
Lemma lem2612814 : term344 = term47.
Proof. exact (TRANS (@lem2612810) (@lem2612813)). Qed.
Lemma lem2612815 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612816 : term350 = term351.
Proof. exact (MK_COMB (@lem2612815) (@lem2612814)). Qed.
Lemma lem2612817 (m : int) (n : int) : (term58 m n) = (term58 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem2612818 (m : int) (n : int) : (term343 m n) = (term352 m n).
Proof. exact (MK_COMB (@lem2612816) (@lem2612817 m n)). Qed.
Lemma lem2612819 (m : int) (n : int) : (term342 m n) = (term352 m n).
Proof. exact (TRANS (@lem2612779 m n) (@lem2612818 m n)). Qed.
Lemma lem2612820 (m : int) (n : int) : (term352 m n) = (term58 m n).
Proof. exact (@lem1982709 (term58 m n)). Qed.
Lemma lem2612821 (m : int) (n : int) : (term342 m n) = (term58 m n).
Proof. exact (TRANS (@lem2612819 m n) (@lem2612820 m n)). Qed.
Lemma lem2612822 (m : int) (n : int) : (term341 m n) = (term58 m n).
Proof. exact (TRANS (@lem2612778 m n) (@lem2612821 m n)). Qed.
Lemma lem2612823 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2612824 (m : int) (n : int) : (term353 m n) = (term354 m n).
Proof. exact (MK_COMB (@lem2612823) (@lem2612822 m n)). Qed.
Lemma lem2612827 (n : int) (m : int) : (term340 n m) = (term355 n m).
Proof. exact (MK_COMB (@lem2612824 m n) (@lem2612757 m)). Qed.
Lemma lem2612828 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2612829 (n : int) (m : int) : (term356 n m) = (term357 n m).
Proof. exact (MK_COMB (@lem2612828) (@lem2612827 n m)). Qed.
Lemma lem2612830 (n : int) (m : int) : (term358 n m) = (term359 n m).
Proof. exact (MK_COMB (@lem2612829 n m) (@lem2612744)). Qed.
Lemma lem2612831 (n : int) (m : int) : (term359 n m) = (term360 n m).
Proof. exact (@lem1982792 (term355 n m) term43). Qed.
Lemma lem2612833 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2612834 : term43 = term243.
Proof. exact (@lem2612833 (NUMERAL 0)). Qed.
Lemma lem2612836 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2612837 : term131 = term132.
Proof. exact (@lem2612836 term48). Qed.
Lemma lem2612838 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2612839 : term133 = term134.
Proof. exact (MK_COMB (@lem2612838) (@lem2612837)). Qed.
Lemma lem2612840 : term244 = term245.
Proof. exact (MK_COMB (@lem2612839) (@lem2612834)). Qed.
Lemma lem2612841 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2612843 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2612844 : term140 = term141.
Proof. exact (@lem2612843 term48 term48). Qed.
Lemma lem2612845 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2612846 : term143 = term48.
Proof. exact (EQ_MP (@lem2612845) (@lem940073)). Qed.
Lemma lem2612847 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2612848 : term141 = term47.
Proof. exact (MK_COMB (@lem2612847) (@lem2612846)). Qed.
Lemma lem2612849 : term140 = term47.
Proof. exact (TRANS (@lem2612844) (@lem2612848)). Qed.
Lemma lem2612851 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2612852 : term244 = term43.
Proof. exact (@lem2612851 term48). Qed.
Lemma lem2612853 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2612854 : term248 = term249.
Proof. exact (MK_COMB (@lem2612853) (@lem2612852)). Qed.
Lemma lem2612855 : term246 = term243.
Proof. exact (MK_COMB (@lem2612854) (@lem2612849)). Qed.
Lemma lem2612856 : term245 = term243.
Proof. exact (TRANS (@lem2612841) (@lem2612855)). Qed.
Lemma lem2612857 : term244 = term243.
Proof. exact (TRANS (@lem2612840) (@lem2612856)). Qed.
Lemma lem2612859 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2612860 : term243 = term43.
Proof. exact (@lem2612859 term43). Qed.
Lemma lem2612861 : term244 = term43.
Proof. exact (TRANS (@lem2612857) (@lem2612860)). Qed.
Lemma lem2612862 (n : int) (m : int) : (term361 n m) = (term361 n m).
Proof. exact (eq_refl (term361 n m)). Qed.
Lemma lem2612863 (n : int) (m : int) : (term360 n m) = (term362 n m).
Proof. exact (MK_COMB (@lem2612862 n m) (@lem2612861)). Qed.
Lemma lem2612864 (n : int) (m : int) : (term362 n m) = (term355 n m).
Proof. exact (@lem1982723 (term355 n m)). Qed.
Lemma lem2612865 (n : int) (m : int) : (term360 n m) = (term355 n m).
Proof. exact (TRANS (@lem2612863 n m) (@lem2612864 n m)). Qed.
Lemma lem2612866 (n : int) (m : int) : (term359 n m) = (term355 n m).
Proof. exact (TRANS (@lem2612831 n m) (@lem2612865 n m)). Qed.
Lemma lem2612867 (n : int) (m : int) : (term358 n m) = (term355 n m).
Proof. exact (TRANS (@lem2612830 n m) (@lem2612866 n m)). Qed.
Lemma lem2612868 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612869 (n : int) (m : int) : (term363 n m) = (term364 n m).
Proof. exact (MK_COMB (@lem2612868) (@lem2612867 n m)). Qed.
Lemma lem2612870 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612871 (n : int) (m : int) : (term339 n m) = (term365 n m).
Proof. exact (MK_COMB (@lem2612869 n m) (@lem2612870)). Qed.
Lemma lem2612872 (n : int) (m : int) : (term338 n m) = (term365 n m).
Proof. exact (TRANS (@lem2612743 n m) (@lem2612871 n m)). Qed.
Lemma lem2612873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612874 (n : int) (m : int) : (term366 n m) = (term367 n m).
Proof. exact (MK_COMB (@lem2612873) (@lem2612742 n m)). Qed.
Lemma lem2612875 (n : int) (m : int) : (term226 n m) = (term368 n m).
Proof. exact (MK_COMB (@lem2612874 n m) (@lem2612872 n m)). Qed.
Lemma lem2612876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612877 (m : int) : (term227 m) = (term369 m).
Proof. exact (MK_COMB (@lem2612876) (@lem2612590 m)). Qed.
Lemma lem2612878 (n : int) (m : int) : (term229 n m) = (term370 n m).
Proof. exact (MK_COMB (@lem2612877 m) (@lem2612875 n m)). Qed.
Lemma lem2612879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2612880 (n : int) (m : int) : (term236 n m) = (term236 n m).
Proof. exact (MK_COMB (@lem2612879) (@lem2612571 n m)). Qed.
Lemma lem2612881 (n : int) (m : int) : (term237 n m) = (term371 n m).
Proof. exact (MK_COMB (@lem2612880 n m) (@lem2612878 n m)). Qed.
Lemma lem2612892 (n : int) (m : int) : (term221 n m) = (term371 n m).
Proof. exact (TRANS (@lem2612253 n m) (@lem2612881 n m)). Qed.
Lemma lem2612893 (n : int) (m : int) : (term220 n m) = (term371 n m).
Proof. exact (TRANS (@lem2612237 n m) (@lem2612892 n m)). Qed.
Lemma lem2612895 (a : real) (x : real) (r : real) : (term207 a x r) = (term208 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2612896 (n : int) (m : int) : (term161 n m) = (term209 n m).
Proof. exact (@lem2612895 (term70 m n) (real_of_int m) term43). Qed.
Lemma lem2612903 (m : int) : (term187 m) = (real_of_int m).
Proof. exact (@lem1982733 (real_of_int m)). Qed.
Lemma lem2612914 (m : int) (n : int) : (term189 m n) = (term189 m n).
Proof. exact (eq_refl (term189 m n)). Qed.
Lemma lem2612917 (n : int) (m : int) : (term210 n m) = (term211 n m).
Proof. exact (MK_COMB (@lem2612914 m n) (@lem2612903 m)). Qed.
Lemma lem2612918 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2612919 (n : int) (m : int) : (term212 n m) = (term213 n m).
Proof. exact (MK_COMB (@lem2612918) (@lem2612917 n m)). Qed.
Lemma lem2612920 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2612921 (n : int) (m : int) : (term214 n m) = (term215 n m).
Proof. exact (MK_COMB (@lem2612919 n m) (@lem2612920)). Qed.
Lemma lem2612948 (n : int) (m : int) : (term216 n m) = (term216 n m).
Proof. exact (eq_refl (term216 n m)). Qed.
Lemma lem2612949 (n : int) (m : int) : (term209 n m) = (term217 n m).
Proof. exact (MK_COMB (@lem2612948 n m) (@lem2612921 n m)). Qed.
Lemma lem2612950 (n : int) (m : int) : (term161 n m) = (term217 n m).
Proof. exact (TRANS (@lem2612896 n m) (@lem2612949 n m)). Qed.
Lemma lem2612951 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2612952 (n : int) (m : int) : (term163 n m) = (term218 n m).
Proof. exact (MK_COMB (@lem2612951 n) (@lem2612950 n m)). Qed.
Lemma lem2612953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612954 (n : int) (m : int) : (term204 n m) = (term219 n m).
Proof. exact (MK_COMB (@lem2612953) (@lem2612952 n m)). Qed.
Lemma lem2612955 (m : int) (n : int) : (term201 m n) = (term201 m n).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem2612956 (m : int) (n : int) : (term372 m n) = (term373 m n).
Proof. exact (MK_COMB (@lem2612954 n m) (@lem2612955 m n)). Qed.
Lemma lem2612957 (m : int) (n : int) : (term374 n m) = (term373 m n).
Proof. exact (eq_refl (term374 n m)). Qed.
Lemma lem2612958 (n : int) (m : int) : (term373 m n) = (term374 n m).
Proof. exact (SYM (@lem2612957 m n)). Qed.
Lemma lem2612959 (n : int) (m : int) : (term374 n m) = (term375 n m).
Proof. exact (@lem1482981 (term376 m n) (real_of_int m)). Qed.
Lemma lem2612960 (n : int) (m : int) : (term373 m n) = (term375 n m).
Proof. exact (TRANS (@lem2612958 n m) (@lem2612959 n m)). Qed.
Lemma lem2612961 (m : int) (n : int) : (term377 n m) = (term378 m n).
Proof. exact (eq_refl (term377 n m)). Qed.
Lemma lem2612962 (m : int) : (term227 m) = (term227 m).
Proof. exact (eq_refl (term227 m)). Qed.
Lemma lem2612963 (m : int) (n : int) : (term379 n m) = (term380 m n).
Proof. exact (MK_COMB (@lem2612962 m) (@lem2612961 m n)). Qed.
Lemma lem2612964 (m : int) (n : int) : (term381 n m) = (term382 m n).
Proof. exact (eq_refl (term381 n m)). Qed.
Lemma lem2612965 (m : int) : (term232 m) = (term232 m).
Proof. exact (eq_refl (term232 m)). Qed.
Lemma lem2612966 (m : int) (n : int) : (term383 n m) = (term384 m n).
Proof. exact (MK_COMB (@lem2612965 m) (@lem2612964 m n)). Qed.
Lemma lem2612967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2612968 (m : int) (n : int) : (term385 n m) = (term386 m n).
Proof. exact (MK_COMB (@lem2612967) (@lem2612966 m n)). Qed.
Lemma lem2612969 (m : int) (n : int) : (term375 n m) = (term387 m n).
Proof. exact (MK_COMB (@lem2612968 m n) (@lem2612963 m n)). Qed.
Lemma lem2612970 (m : int) (n : int) : (term388 m n) = (term388 m n).
Proof. exact (eq_refl (term388 m n)). Qed.
Lemma lem2612971 (m : int) (n : int) : ((term373 m n) = (term375 n m)) = ((term373 m n) = (term387 m n)).
Proof. exact (MK_COMB (@lem2612970 m n) (@lem2612969 m n)). Qed.
Lemma lem2612972 (m : int) (n : int) : (term373 m n) = (term387 m n).
Proof. exact (EQ_MP (@lem2612971 m n) (@lem2612960 n m)). Qed.
Lemma lem2612973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612974 (n : int) (m : int) : (term277 n m) = (term277 n m).
Proof. exact (MK_COMB (@lem2612973) (@lem2612421 n m)). Qed.
Lemma lem2612975 (n : int) (m : int) : (term278 n m) = (term278 n m).
Proof. exact (MK_COMB (@lem2612974 n m) (@lem2612481 n m)). Qed.
Lemma lem2612976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2612977 (n : int) : (term162 n) = (term162 n).
Proof. exact (MK_COMB (@lem2612976) (@lem2612355 n)). Qed.
Lemma lem2612978 (n : int) (m : int) : (term279 n m) = (term279 n m).
Proof. exact (MK_COMB (@lem2612977 n) (@lem2612975 n m)). Qed.
Lemma lem2612979 (m : int) (n : int) : (term389 m n) = (term390 m n).
Proof. exact (@lem1988291 (term391 m n) term43). Qed.
Lemma lem2613015 (m : int) (n : int) : (term392 m n) = (term393 m n).
Proof. exact (@lem1982792 (term391 m n) term43). Qed.
Lemma lem2613017 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613018 : term43 = term243.
Proof. exact (@lem2613017 (NUMERAL 0)). Qed.
Lemma lem2613020 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613021 : term131 = term132.
Proof. exact (@lem2613020 term48). Qed.
Lemma lem2613022 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613023 : term133 = term134.
Proof. exact (MK_COMB (@lem2613022) (@lem2613021)). Qed.
Lemma lem2613024 : term244 = term245.
Proof. exact (MK_COMB (@lem2613023) (@lem2613018)). Qed.
Lemma lem2613025 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2613027 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613028 : term140 = term141.
Proof. exact (@lem2613027 term48 term48). Qed.
Lemma lem2613029 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613030 : term143 = term48.
Proof. exact (EQ_MP (@lem2613029) (@lem940073)). Qed.
Lemma lem2613031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613032 : term141 = term47.
Proof. exact (MK_COMB (@lem2613031) (@lem2613030)). Qed.
Lemma lem2613033 : term140 = term47.
Proof. exact (TRANS (@lem2613028) (@lem2613032)). Qed.
Lemma lem2613035 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2613036 : term244 = term43.
Proof. exact (@lem2613035 term48). Qed.
Lemma lem2613037 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2613038 : term248 = term249.
Proof. exact (MK_COMB (@lem2613037) (@lem2613036)). Qed.
Lemma lem2613039 : term246 = term243.
Proof. exact (MK_COMB (@lem2613038) (@lem2613033)). Qed.
Lemma lem2613040 : term245 = term243.
Proof. exact (TRANS (@lem2613025) (@lem2613039)). Qed.
Lemma lem2613041 : term244 = term243.
Proof. exact (TRANS (@lem2613024) (@lem2613040)). Qed.
Lemma lem2613043 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2613044 : term243 = term43.
Proof. exact (@lem2613043 term43). Qed.
Lemma lem2613045 : term244 = term43.
Proof. exact (TRANS (@lem2613041) (@lem2613044)). Qed.
Lemma lem2613046 (m : int) (n : int) : (term394 m n) = (term394 m n).
Proof. exact (eq_refl (term394 m n)). Qed.
Lemma lem2613047 (m : int) (n : int) : (term393 m n) = (term395 m n).
Proof. exact (MK_COMB (@lem2613046 m n) (@lem2613045)). Qed.
Lemma lem2613048 (m : int) (n : int) : (term395 m n) = (term391 m n).
Proof. exact (@lem1982723 (term391 m n)). Qed.
Lemma lem2613049 (m : int) (n : int) : (term393 m n) = (term391 m n).
Proof. exact (TRANS (@lem2613047 m n) (@lem2613048 m n)). Qed.
Lemma lem2613051 (m : int) (n : int) : (term392 m n) = (term391 m n).
Proof. exact (TRANS (@lem2613015 m n) (@lem2613049 m n)). Qed.
Lemma lem2613052 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2613053 (m : int) (n : int) : (term396 m n) = (term397 m n).
Proof. exact (MK_COMB (@lem2613052) (@lem2613051 m n)). Qed.
Lemma lem2613054 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2613055 (m : int) (n : int) : (term390 m n) = (term389 m n).
Proof. exact (MK_COMB (@lem2613053 m n) (@lem2613054)). Qed.
Lemma lem2613056 (m : int) (n : int) : (term389 m n) = (term389 m n).
Proof. exact (TRANS (@lem2612979 m n) (@lem2613055 m n)). Qed.
Lemma lem2613057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2613058 (n : int) (m : int) : (term289 n m) = (term289 n m).
Proof. exact (MK_COMB (@lem2613057) (@lem2612978 n m)). Qed.
Lemma lem2613059 (m : int) (n : int) : (term382 m n) = (term382 m n).
Proof. exact (MK_COMB (@lem2613058 n m) (@lem2613056 m n)). Qed.
Lemma lem2613060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2613061 (m : int) : (term232 m) = (term232 m).
Proof. exact (MK_COMB (@lem2613060) (@lem2612301 m)). Qed.
Lemma lem2613062 (m : int) (n : int) : (term384 m n) = (term384 m n).
Proof. exact (MK_COMB (@lem2613061 m) (@lem2613059 m n)). Qed.
Lemma lem2613063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2613064 (n : int) (m : int) : (term332 n m) = (term333 n m).
Proof. exact (MK_COMB (@lem2613063) (@lem2612666 n m)). Qed.
Lemma lem2613065 (n : int) (m : int) : (term334 n m) = (term335 n m).
Proof. exact (MK_COMB (@lem2613064 n m) (@lem2612736 n m)). Qed.
Lemma lem2613066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2613067 (n : int) : (term162 n) = (term162 n).
Proof. exact (MK_COMB (@lem2613066) (@lem2612355 n)). Qed.
Lemma lem2613068 (n : int) (m : int) : (term336 n m) = (term337 n m).
Proof. exact (MK_COMB (@lem2613067 n) (@lem2613065 n m)). Qed.
Lemma lem2613069 (m : int) (n : int) : (term398 m n) = (term399 m n).
Proof. exact (@lem1988291 (term400 m n) term43). Qed.
Lemma lem2613070 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2613083 (m : int) (n : int) : (term401 m n) = (term401 m n).
Proof. exact (eq_refl (term401 m n)). Qed.
Lemma lem2613084 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2613091 (m : int) : (term91 m) = (term198 m).
Proof. exact (@lem1982785 (real_of_int m)). Qed.
Lemma lem2613092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613093 (m : int) : (term300 m) = (term301 m).
Proof. exact (MK_COMB (@lem2613092) (@lem2613091 m)). Qed.
Lemma lem2613094 (m : int) (n : int) : (term302 m n) = (term303 m n).
Proof. exact (MK_COMB (@lem2613093 m) (@lem2613084 n)). Qed.
Lemma lem2613099 (m : int) (n : int) : (term303 m n) = (term304 m n).
Proof. exact (@lem1982745 term131 (real_of_int m) (real_of_int n)). Qed.
Lemma lem2613100 (m : int) (n : int) : (term302 m n) = (term304 m n).
Proof. exact (TRANS (@lem2613094 m n) (@lem2613099 m n)). Qed.
Lemma lem2613103 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem2613104 (m : int) (n : int) : (term341 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem2613103) (@lem2613100 m n)). Qed.
Lemma lem2613105 (m : int) (n : int) : (term342 m n) = (term343 m n).
Proof. exact (@lem1982749 term131 term131 (term58 m n)). Qed.
Lemma lem2613107 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613108 : term131 = term132.
Proof. exact (@lem2613107 term48). Qed.
Lemma lem2613110 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613111 : term131 = term132.
Proof. exact (@lem2613110 term48). Qed.
Lemma lem2613112 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613113 : term133 = term134.
Proof. exact (MK_COMB (@lem2613112) (@lem2613111)). Qed.
Lemma lem2613114 : term344 = term345.
Proof. exact (MK_COMB (@lem2613113) (@lem2613108)). Qed.
Lemma lem2613115 : term345 = term346.
Proof. exact (@lem1981613 term131 term131 term47 term47). Qed.
Lemma lem2613117 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613118 : term140 = term141.
Proof. exact (@lem2613117 term48 term48). Qed.
Lemma lem2613119 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613120 : term143 = term48.
Proof. exact (EQ_MP (@lem2613119) (@lem940073)). Qed.
Lemma lem2613121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613122 : term141 = term47.
Proof. exact (MK_COMB (@lem2613121) (@lem2613120)). Qed.
Lemma lem2613123 : term140 = term47.
Proof. exact (TRANS (@lem2613118) (@lem2613122)). Qed.
Lemma lem2613125 (m : nat) (n : nat) : (term347 m n) = (term139 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2613126 : term344 = term141.
Proof. exact (@lem2613125 term48 term48). Qed.
Lemma lem2613127 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613128 : term143 = term48.
Proof. exact (EQ_MP (@lem2613127) (@lem940073)). Qed.
Lemma lem2613129 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613130 : term141 = term47.
Proof. exact (MK_COMB (@lem2613129) (@lem2613128)). Qed.
Lemma lem2613131 : term344 = term47.
Proof. exact (TRANS (@lem2613126) (@lem2613130)). Qed.
Lemma lem2613132 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2613133 : term348 = term349.
Proof. exact (MK_COMB (@lem2613132) (@lem2613131)). Qed.
Lemma lem2613134 : term346 = term128.
Proof. exact (MK_COMB (@lem2613133) (@lem2613123)). Qed.
Lemma lem2613135 : term345 = term128.
Proof. exact (TRANS (@lem2613115) (@lem2613134)). Qed.
Lemma lem2613136 : term344 = term128.
Proof. exact (TRANS (@lem2613114) (@lem2613135)). Qed.
Lemma lem2613138 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2613139 : term128 = term47.
Proof. exact (@lem2613138 term47). Qed.
Lemma lem2613140 : term344 = term47.
Proof. exact (TRANS (@lem2613136) (@lem2613139)). Qed.
Lemma lem2613141 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613142 : term350 = term351.
Proof. exact (MK_COMB (@lem2613141) (@lem2613140)). Qed.
Lemma lem2613143 (m : int) (n : int) : (term58 m n) = (term58 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem2613144 (m : int) (n : int) : (term343 m n) = (term352 m n).
Proof. exact (MK_COMB (@lem2613142) (@lem2613143 m n)). Qed.
Lemma lem2613145 (m : int) (n : int) : (term342 m n) = (term352 m n).
Proof. exact (TRANS (@lem2613105 m n) (@lem2613144 m n)). Qed.
Lemma lem2613146 (m : int) (n : int) : (term352 m n) = (term58 m n).
Proof. exact (@lem1982709 (term58 m n)). Qed.
Lemma lem2613147 (m : int) (n : int) : (term342 m n) = (term58 m n).
Proof. exact (TRANS (@lem2613145 m n) (@lem2613146 m n)). Qed.
Lemma lem2613148 (m : int) (n : int) : (term341 m n) = (term58 m n).
Proof. exact (TRANS (@lem2613104 m n) (@lem2613147 m n)). Qed.
Lemma lem2613149 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613150 (m : int) (n : int) : (term353 m n) = (term354 m n).
Proof. exact (MK_COMB (@lem2613149) (@lem2613148 m n)). Qed.
Lemma lem2613153 (m : int) (n : int) : (term400 m n) = (term402 m n).
Proof. exact (MK_COMB (@lem2613150 m n) (@lem2613083 m n)). Qed.
Lemma lem2613154 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2613155 (m : int) (n : int) : (term403 m n) = (term404 m n).
Proof. exact (MK_COMB (@lem2613154) (@lem2613153 m n)). Qed.
Lemma lem2613156 (m : int) (n : int) : (term405 m n) = (term406 m n).
Proof. exact (MK_COMB (@lem2613155 m n) (@lem2613070)). Qed.
Lemma lem2613157 (m : int) (n : int) : (term406 m n) = (term407 m n).
Proof. exact (@lem1982792 (term402 m n) term43). Qed.
Lemma lem2613159 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613160 : term43 = term243.
Proof. exact (@lem2613159 (NUMERAL 0)). Qed.
Lemma lem2613162 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613163 : term131 = term132.
Proof. exact (@lem2613162 term48). Qed.
Lemma lem2613164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613165 : term133 = term134.
Proof. exact (MK_COMB (@lem2613164) (@lem2613163)). Qed.
Lemma lem2613166 : term244 = term245.
Proof. exact (MK_COMB (@lem2613165) (@lem2613160)). Qed.
Lemma lem2613167 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2613169 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613170 : term140 = term141.
Proof. exact (@lem2613169 term48 term48). Qed.
Lemma lem2613171 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613172 : term143 = term48.
Proof. exact (EQ_MP (@lem2613171) (@lem940073)). Qed.
Lemma lem2613173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613174 : term141 = term47.
Proof. exact (MK_COMB (@lem2613173) (@lem2613172)). Qed.
Lemma lem2613175 : term140 = term47.
Proof. exact (TRANS (@lem2613170) (@lem2613174)). Qed.
Lemma lem2613177 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2613178 : term244 = term43.
Proof. exact (@lem2613177 term48). Qed.
Lemma lem2613179 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2613180 : term248 = term249.
Proof. exact (MK_COMB (@lem2613179) (@lem2613178)). Qed.
Lemma lem2613181 : term246 = term243.
Proof. exact (MK_COMB (@lem2613180) (@lem2613175)). Qed.
Lemma lem2613182 : term245 = term243.
Proof. exact (TRANS (@lem2613167) (@lem2613181)). Qed.
Lemma lem2613183 : term244 = term243.
Proof. exact (TRANS (@lem2613166) (@lem2613182)). Qed.
Lemma lem2613185 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2613186 : term243 = term43.
Proof. exact (@lem2613185 term43). Qed.
Lemma lem2613187 : term244 = term43.
Proof. exact (TRANS (@lem2613183) (@lem2613186)). Qed.
Lemma lem2613188 (m : int) (n : int) : (term408 m n) = (term408 m n).
Proof. exact (eq_refl (term408 m n)). Qed.
Lemma lem2613189 (m : int) (n : int) : (term407 m n) = (term409 m n).
Proof. exact (MK_COMB (@lem2613188 m n) (@lem2613187)). Qed.
Lemma lem2613190 (m : int) (n : int) : (term409 m n) = (term402 m n).
Proof. exact (@lem1982723 (term402 m n)). Qed.
Lemma lem2613191 (m : int) (n : int) : (term407 m n) = (term402 m n).
Proof. exact (TRANS (@lem2613189 m n) (@lem2613190 m n)). Qed.
Lemma lem2613192 (m : int) (n : int) : (term406 m n) = (term402 m n).
Proof. exact (TRANS (@lem2613157 m n) (@lem2613191 m n)). Qed.
Lemma lem2613193 (m : int) (n : int) : (term405 m n) = (term402 m n).
Proof. exact (TRANS (@lem2613156 m n) (@lem2613192 m n)). Qed.
Lemma lem2613194 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2613195 (m : int) (n : int) : (term410 m n) = (term411 m n).
Proof. exact (MK_COMB (@lem2613194) (@lem2613193 m n)). Qed.
Lemma lem2613196 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2613197 (m : int) (n : int) : (term399 m n) = (term412 m n).
Proof. exact (MK_COMB (@lem2613195 m n) (@lem2613196)). Qed.
Lemma lem2613198 (m : int) (n : int) : (term398 m n) = (term412 m n).
Proof. exact (TRANS (@lem2613069 m n) (@lem2613197 m n)). Qed.
Lemma lem2613199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2613200 (n : int) (m : int) : (term366 n m) = (term367 n m).
Proof. exact (MK_COMB (@lem2613199) (@lem2613068 n m)). Qed.
Lemma lem2613201 (m : int) (n : int) : (term378 m n) = (term413 m n).
Proof. exact (MK_COMB (@lem2613200 n m) (@lem2613198 m n)). Qed.
Lemma lem2613202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2613203 (m : int) : (term227 m) = (term369 m).
Proof. exact (MK_COMB (@lem2613202) (@lem2612590 m)). Qed.
Lemma lem2613204 (m : int) (n : int) : (term380 m n) = (term414 m n).
Proof. exact (MK_COMB (@lem2613203 m) (@lem2613201 m n)). Qed.
Lemma lem2613205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2613206 (m : int) (n : int) : (term386 m n) = (term386 m n).
Proof. exact (MK_COMB (@lem2613205) (@lem2613062 m n)). Qed.
Lemma lem2613207 (m : int) (n : int) : (term387 m n) = (term415 m n).
Proof. exact (MK_COMB (@lem2613206 m n) (@lem2613204 m n)). Qed.
Lemma lem2613218 (m : int) (n : int) : (term373 m n) = (term415 m n).
Proof. exact (TRANS (@lem2612972 m n) (@lem2613207 m n)). Qed.
Lemma lem2613219 (m : int) (n : int) : (term372 m n) = (term415 m n).
Proof. exact (TRANS (@lem2612956 m n) (@lem2613218 m n)). Qed.
Lemma lem2613220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2613221 (n : int) (m : int) : (term416 n m) = (term417 n m).
Proof. exact (MK_COMB (@lem2613220) (@lem2612893 n m)). Qed.
Lemma lem2613222 (m : int) (n : int) : (term206 m n) = (term418 m n).
Proof. exact (MK_COMB (@lem2613221 n m) (@lem2613219 m n)). Qed.
Lemma lem2613223 (m : int) (n : int) (h1 : term418 m n) : term418 m n.
Proof. exact (h1). Qed.
Lemma lem2613224 (n : int) (m : int) (h1 : term371 n m) : term371 n m.
Proof. exact (h1). Qed.
Lemma lem2613225 (n : int) (m : int) (h1 : term234 n m) : term234 n m.
Proof. exact (h1). Qed.
Lemma lem2613226 (n : int) (m : int) (h1 : term234 n m) : term231 n m.
Proof. exact (proj2 (@lem2613225 n m h1)). Qed.
Lemma lem2613228 (n : int) (m : int) (h1 : term234 n m) : term280 n m.
Proof. exact (proj2 (@lem2613226 n m h1)). Qed.
Lemma lem2613229 (n : int) (m : int) (h1 : term234 n m) : term279 n m.
Proof. exact (proj1 (@lem2613226 n m h1)). Qed.
Lemma lem2613230 (n : int) (m : int) (h1 : term234 n m) : term278 n m.
Proof. exact (proj2 (@lem2613229 n m h1)). Qed.
Lemma lem2613232 (n : int) (m : int) (h1 : term234 n m) : term268 n m.
Proof. exact (proj2 (@lem2613230 n m h1)). Qed.
Lemma lem2613235 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2613236 : term419 = term420.
Proof. exact (@lem2613235 term43 term47). Qed.
Lemma lem2613238 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613239 : term47 = term128.
Proof. exact (@lem2613238 term48). Qed.
Lemma lem2613241 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613242 : term43 = term243.
Proof. exact (@lem2613241 (NUMERAL 0)). Qed.
Lemma lem2613243 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2613244 : term421 = term422.
Proof. exact (MK_COMB (@lem2613243) (@lem2613242)). Qed.
Lemma lem2613245 : term420 = term423.
Proof. exact (MK_COMB (@lem2613244) (@lem2613239)). Qed.
Lemma lem2613246 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2613248 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613249 : term420 = term426.
Proof. exact (@lem2613248 (NUMERAL 0) term48). Qed.
Lemma lem2613250 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613251 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613252 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613251 h1) (fun h1 : term426 = True => @lem2613250)). Qed.
Lemma lem2613253 : term426 = True.
Proof. exact (EQ_MP (@lem2613252) (@lem2613250)). Qed.
Lemma lem2613254 : term420 = True.
Proof. exact (TRANS (@lem2613249) (@lem2613253)). Qed.
Lemma lem2613255 : True = term420.
Proof. exact (SYM (@lem2613254)). Qed.
Lemma lem2613256 : term420.
Proof. exact (EQ_MP (@lem2613255) (@lem0)). Qed.
Lemma lem2613257 : term428.
Proof. exact (@lem2613246 (@lem2613256)). Qed.
Lemma lem2613259 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613260 : term420 = term426.
Proof. exact (@lem2613259 (NUMERAL 0) term48). Qed.
Lemma lem2613261 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613262 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613263 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613262 h1) (fun h1 : term426 = True => @lem2613261)). Qed.
Lemma lem2613264 : term426 = True.
Proof. exact (EQ_MP (@lem2613263) (@lem2613261)). Qed.
Lemma lem2613265 : term420 = True.
Proof. exact (TRANS (@lem2613260) (@lem2613264)). Qed.
Lemma lem2613266 : True = term420.
Proof. exact (SYM (@lem2613265)). Qed.
Lemma lem2613267 : term420.
Proof. exact (EQ_MP (@lem2613266) (@lem0)). Qed.
Lemma lem2613268 : term423 = term429.
Proof. exact (@lem2613257 (@lem2613267)). Qed.
Lemma lem2613270 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613271 : term140 = term141.
Proof. exact (@lem2613270 term48 term48). Qed.
Lemma lem2613272 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613273 : term143 = term48.
Proof. exact (EQ_MP (@lem2613272) (@lem940073)). Qed.
Lemma lem2613274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613275 : term141 = term47.
Proof. exact (MK_COMB (@lem2613274) (@lem2613273)). Qed.
Lemma lem2613276 : term140 = term47.
Proof. exact (TRANS (@lem2613271) (@lem2613275)). Qed.
Lemma lem2613278 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613279 : term431 = term43.
Proof. exact (@lem2613278 term48). Qed.
Lemma lem2613280 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2613281 : term432 = term421.
Proof. exact (MK_COMB (@lem2613280) (@lem2613279)). Qed.
Lemma lem2613282 : term429 = term420.
Proof. exact (MK_COMB (@lem2613281) (@lem2613276)). Qed.
Lemma lem2613284 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613285 : term420 = term426.
Proof. exact (@lem2613284 (NUMERAL 0) term48). Qed.
Lemma lem2613286 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613287 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613288 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613287 h1) (fun h1 : term426 = True => @lem2613286)). Qed.
Lemma lem2613289 : term426 = True.
Proof. exact (EQ_MP (@lem2613288) (@lem2613286)). Qed.
Lemma lem2613290 : term420 = True.
Proof. exact (TRANS (@lem2613285) (@lem2613289)). Qed.
Lemma lem2613291 : term429 = True.
Proof. exact (TRANS (@lem2613282) (@lem2613290)). Qed.
Lemma lem2613292 : term423 = True.
Proof. exact (TRANS (@lem2613268) (@lem2613291)). Qed.
Lemma lem2613293 : term420 = True.
Proof. exact (TRANS (@lem2613245) (@lem2613292)). Qed.
Lemma lem2613294 : term419 = True.
Proof. exact (TRANS (@lem2613236) (@lem2613293)). Qed.
Lemma lem2613295 : True = term419.
Proof. exact (SYM (@lem2613294)). Qed.
Lemma lem2613296 : term419.
Proof. exact (EQ_MP (@lem2613295) (@lem0)). Qed.
Lemma lem2613297 (n : int) (m : int) (h1 : term234 n m) : term433 n m.
Proof. exact (conj (@lem2613296) (@lem2613232 n m h1)). Qed.
Lemma lem2613299 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2613300 (n : int) (m : int) : term435 n m.
Proof. exact (@lem2613299 term47 (term270 n m)). Qed.
Lemma lem2613301 (n : int) (m : int) (h1 : term234 n m) : term436 n m.
Proof. exact (@lem2613300 n m (@lem2613297 n m h1)). Qed.
Lemma lem2613302 (n : int) (m : int) : (term437 n m) = (term270 n m).
Proof. exact (@lem1982733 (term270 n m)). Qed.
Lemma lem2613303 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2613304 (n : int) (m : int) : (term438 n m) = (term276 n m).
Proof. exact (MK_COMB (@lem2613303) (@lem2613302 n m)). Qed.
Lemma lem2613305 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2613306 (n : int) (m : int) : (term436 n m) = (term268 n m).
Proof. exact (MK_COMB (@lem2613304 n m) (@lem2613305)). Qed.
Lemma lem2613307 (n : int) (m : int) (h1 : term234 n m) : term268 n m.
Proof. exact (EQ_MP (@lem2613306 n m) (@lem2613301 n m h1)). Qed.
Lemma lem2613309 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2613310 : term419 = term420.
Proof. exact (@lem2613309 term43 term47). Qed.
Lemma lem2613312 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613313 : term47 = term128.
Proof. exact (@lem2613312 term48). Qed.
Lemma lem2613315 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613316 : term43 = term243.
Proof. exact (@lem2613315 (NUMERAL 0)). Qed.
Lemma lem2613317 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2613318 : term421 = term422.
Proof. exact (MK_COMB (@lem2613317) (@lem2613316)). Qed.
Lemma lem2613319 : term420 = term423.
Proof. exact (MK_COMB (@lem2613318) (@lem2613313)). Qed.
Lemma lem2613320 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2613322 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613323 : term420 = term426.
Proof. exact (@lem2613322 (NUMERAL 0) term48). Qed.
Lemma lem2613324 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613325 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613326 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613325 h1) (fun h1 : term426 = True => @lem2613324)). Qed.
Lemma lem2613327 : term426 = True.
Proof. exact (EQ_MP (@lem2613326) (@lem2613324)). Qed.
Lemma lem2613328 : term420 = True.
Proof. exact (TRANS (@lem2613323) (@lem2613327)). Qed.
Lemma lem2613329 : True = term420.
Proof. exact (SYM (@lem2613328)). Qed.
Lemma lem2613330 : term420.
Proof. exact (EQ_MP (@lem2613329) (@lem0)). Qed.
Lemma lem2613331 : term428.
Proof. exact (@lem2613320 (@lem2613330)). Qed.
Lemma lem2613333 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613334 : term420 = term426.
Proof. exact (@lem2613333 (NUMERAL 0) term48). Qed.
Lemma lem2613335 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613336 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613337 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613336 h1) (fun h1 : term426 = True => @lem2613335)). Qed.
Lemma lem2613338 : term426 = True.
Proof. exact (EQ_MP (@lem2613337) (@lem2613335)). Qed.
Lemma lem2613339 : term420 = True.
Proof. exact (TRANS (@lem2613334) (@lem2613338)). Qed.
Lemma lem2613340 : True = term420.
Proof. exact (SYM (@lem2613339)). Qed.
Lemma lem2613341 : term420.
Proof. exact (EQ_MP (@lem2613340) (@lem0)). Qed.
Lemma lem2613342 : term423 = term429.
Proof. exact (@lem2613331 (@lem2613341)). Qed.
Lemma lem2613344 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613345 : term140 = term141.
Proof. exact (@lem2613344 term48 term48). Qed.
Lemma lem2613346 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613347 : term143 = term48.
Proof. exact (EQ_MP (@lem2613346) (@lem940073)). Qed.
Lemma lem2613348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613349 : term141 = term47.
Proof. exact (MK_COMB (@lem2613348) (@lem2613347)). Qed.
Lemma lem2613350 : term140 = term47.
Proof. exact (TRANS (@lem2613345) (@lem2613349)). Qed.
Lemma lem2613352 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613353 : term431 = term43.
Proof. exact (@lem2613352 term48). Qed.
Lemma lem2613354 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2613355 : term432 = term421.
Proof. exact (MK_COMB (@lem2613354) (@lem2613353)). Qed.
Lemma lem2613356 : term429 = term420.
Proof. exact (MK_COMB (@lem2613355) (@lem2613350)). Qed.
Lemma lem2613358 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613359 : term420 = term426.
Proof. exact (@lem2613358 (NUMERAL 0) term48). Qed.
Lemma lem2613360 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613361 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613362 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613361 h1) (fun h1 : term426 = True => @lem2613360)). Qed.
Lemma lem2613363 : term426 = True.
Proof. exact (EQ_MP (@lem2613362) (@lem2613360)). Qed.
Lemma lem2613364 : term420 = True.
Proof. exact (TRANS (@lem2613359) (@lem2613363)). Qed.
Lemma lem2613365 : term429 = True.
Proof. exact (TRANS (@lem2613356) (@lem2613364)). Qed.
Lemma lem2613366 : term423 = True.
Proof. exact (TRANS (@lem2613342) (@lem2613365)). Qed.
Lemma lem2613367 : term420 = True.
Proof. exact (TRANS (@lem2613319) (@lem2613366)). Qed.
Lemma lem2613368 : term419 = True.
Proof. exact (TRANS (@lem2613310) (@lem2613367)). Qed.
Lemma lem2613369 : True = term419.
Proof. exact (SYM (@lem2613368)). Qed.
Lemma lem2613370 : term419.
Proof. exact (EQ_MP (@lem2613369) (@lem0)). Qed.
Lemma lem2613371 (n : int) (m : int) (h1 : term234 n m) : term439 n m.
Proof. exact (conj (@lem2613370) (@lem2613228 n m h1)). Qed.
Lemma lem2613373 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2613374 (n : int) (m : int) : term440 n m.
Proof. exact (@lem2613373 term47 (term282 n m)). Qed.
Lemma lem2613375 (n : int) (m : int) (h1 : term234 n m) : term441 n m.
Proof. exact (@lem2613374 n m (@lem2613371 n m h1)). Qed.
Lemma lem2613376 (n : int) (m : int) : (term442 n m) = (term282 n m).
Proof. exact (@lem1982733 (term282 n m)). Qed.
Lemma lem2613377 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2613378 (n : int) (m : int) : (term443 n m) = (term288 n m).
Proof. exact (MK_COMB (@lem2613377) (@lem2613376 n m)). Qed.
Lemma lem2613379 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2613380 (n : int) (m : int) : (term441 n m) = (term280 n m).
Proof. exact (MK_COMB (@lem2613378 n m) (@lem2613379)). Qed.
Lemma lem2613381 (n : int) (m : int) (h1 : term234 n m) : term280 n m.
Proof. exact (EQ_MP (@lem2613380 n m) (@lem2613375 n m h1)). Qed.
Lemma lem2613382 (n : int) (m : int) (h1 : term234 n m) : term444 n m.
Proof. exact (conj (@lem2613381 n m h1) (@lem2613307 n m h1)). Qed.
Lemma lem2613384 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2613385 (n : int) (m : int) : term446 n m.
Proof. exact (@lem2613384 (term282 n m) (term270 n m)). Qed.
Lemma lem2613386 (n : int) (m : int) (h1 : term234 n m) : term447 n m.
Proof. exact (@lem2613385 n m (@lem2613382 n m h1)). Qed.
Lemma lem2613387 (n : int) (m : int) : (term448 n m) = (term449 n m).
Proof. exact (@lem1982753 (term304 m n) (term58 m n) (term178 m) (real_of_int m)). Qed.
Lemma lem2613388 (m : int) (n : int) : (term450 m n) = (term451 m n).
Proof. exact (@lem1982713 term131 (term58 m n)). Qed.
Lemma lem2613390 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613391 : term47 = term128.
Proof. exact (@lem2613390 term48). Qed.
Lemma lem2613393 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613394 : term131 = term132.
Proof. exact (@lem2613393 term48). Qed.
Lemma lem2613395 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613396 : term452 = term453.
Proof. exact (MK_COMB (@lem2613395) (@lem2613394)). Qed.
Lemma lem2613397 : term454 = term455.
Proof. exact (MK_COMB (@lem2613396) (@lem2613391)). Qed.
Lemma lem2613398 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2613400 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613401 : term420 = term426.
Proof. exact (@lem2613400 (NUMERAL 0) term48). Qed.
Lemma lem2613402 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613403 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613404 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613403 h1) (fun h1 : term426 = True => @lem2613402)). Qed.
Lemma lem2613405 : term426 = True.
Proof. exact (EQ_MP (@lem2613404) (@lem2613402)). Qed.
Lemma lem2613406 : term420 = True.
Proof. exact (TRANS (@lem2613401) (@lem2613405)). Qed.
Lemma lem2613407 : True = term420.
Proof. exact (SYM (@lem2613406)). Qed.
Lemma lem2613408 : term420.
Proof. exact (EQ_MP (@lem2613407) (@lem0)). Qed.
Lemma lem2613409 : term457.
Proof. exact (@lem2613398 (@lem2613408)). Qed.
Lemma lem2613411 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613412 : term420 = term426.
Proof. exact (@lem2613411 (NUMERAL 0) term48). Qed.
Lemma lem2613413 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613414 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613415 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613414 h1) (fun h1 : term426 = True => @lem2613413)). Qed.
Lemma lem2613416 : term426 = True.
Proof. exact (EQ_MP (@lem2613415) (@lem2613413)). Qed.
Lemma lem2613417 : term420 = True.
Proof. exact (TRANS (@lem2613412) (@lem2613416)). Qed.
Lemma lem2613418 : True = term420.
Proof. exact (SYM (@lem2613417)). Qed.
Lemma lem2613419 : term420.
Proof. exact (EQ_MP (@lem2613418) (@lem0)). Qed.
Lemma lem2613420 : term458.
Proof. exact (@lem2613409 (@lem2613419)). Qed.
Lemma lem2613422 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613423 : term420 = term426.
Proof. exact (@lem2613422 (NUMERAL 0) term48). Qed.
Lemma lem2613424 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613425 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613426 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613425 h1) (fun h1 : term426 = True => @lem2613424)). Qed.
Lemma lem2613427 : term426 = True.
Proof. exact (EQ_MP (@lem2613426) (@lem2613424)). Qed.
Lemma lem2613428 : term420 = True.
Proof. exact (TRANS (@lem2613423) (@lem2613427)). Qed.
Lemma lem2613429 : True = term420.
Proof. exact (SYM (@lem2613428)). Qed.
Lemma lem2613430 : term420.
Proof. exact (EQ_MP (@lem2613429) (@lem0)). Qed.
Lemma lem2613431 : term459.
Proof. exact (@lem2613420 (@lem2613430)). Qed.
Lemma lem2613433 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613434 : term140 = term141.
Proof. exact (@lem2613433 term48 term48). Qed.
Lemma lem2613435 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613436 : term143 = term48.
Proof. exact (EQ_MP (@lem2613435) (@lem940073)). Qed.
Lemma lem2613437 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613438 : term141 = term47.
Proof. exact (MK_COMB (@lem2613437) (@lem2613436)). Qed.
Lemma lem2613439 : term140 = term47.
Proof. exact (TRANS (@lem2613434) (@lem2613438)). Qed.
Lemma lem2613441 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2613442 : term135 = term146.
Proof. exact (@lem2613441 term48 term48). Qed.
Lemma lem2613443 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613444 : term143 = term48.
Proof. exact (EQ_MP (@lem2613443) (@lem940073)). Qed.
Lemma lem2613445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613446 : term141 = term47.
Proof. exact (MK_COMB (@lem2613445) (@lem2613444)). Qed.
Lemma lem2613447 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2613448 : term146 = term131.
Proof. exact (MK_COMB (@lem2613447) (@lem2613446)). Qed.
Lemma lem2613449 : term135 = term131.
Proof. exact (TRANS (@lem2613442) (@lem2613448)). Qed.
Lemma lem2613450 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613451 : term460 = term452.
Proof. exact (MK_COMB (@lem2613450) (@lem2613449)). Qed.
Lemma lem2613452 : term461 = term454.
Proof. exact (MK_COMB (@lem2613451) (@lem2613439)). Qed.
Lemma lem2613454 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2613455 : term454 = term43.
Proof. exact (@lem2613454 term48). Qed.
Lemma lem2613456 : term461 = term43.
Proof. exact (TRANS (@lem2613452) (@lem2613455)). Qed.
Lemma lem2613457 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613458 : term463 = term464.
Proof. exact (MK_COMB (@lem2613457) (@lem2613456)). Qed.
Lemma lem2613459 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2613460 : term465 = term431.
Proof. exact (MK_COMB (@lem2613458) (@lem2613459)). Qed.
Lemma lem2613462 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613463 : term431 = term43.
Proof. exact (@lem2613462 term48). Qed.
Lemma lem2613464 : term465 = term43.
Proof. exact (TRANS (@lem2613460) (@lem2613463)). Qed.
Lemma lem2613466 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613467 : term140 = term141.
Proof. exact (@lem2613466 term48 term48). Qed.
Lemma lem2613468 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613469 : term143 = term48.
Proof. exact (EQ_MP (@lem2613468) (@lem940073)). Qed.
Lemma lem2613470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613471 : term141 = term47.
Proof. exact (MK_COMB (@lem2613470) (@lem2613469)). Qed.
Lemma lem2613472 : term140 = term47.
Proof. exact (TRANS (@lem2613467) (@lem2613471)). Qed.
Lemma lem2613473 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2613474 : term466 = term431.
Proof. exact (MK_COMB (@lem2613473) (@lem2613472)). Qed.
Lemma lem2613476 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613477 : term431 = term43.
Proof. exact (@lem2613476 term48). Qed.
Lemma lem2613478 : term466 = term43.
Proof. exact (TRANS (@lem2613474) (@lem2613477)). Qed.
Lemma lem2613479 : term43 = term466.
Proof. exact (SYM (@lem2613478)). Qed.
Lemma lem2613480 : term465 = term466.
Proof. exact (TRANS (@lem2613464) (@lem2613479)). Qed.
Lemma lem2613481 : term455 = term243.
Proof. exact (@lem2613431 (@lem2613480)). Qed.
Lemma lem2613482 : term454 = term243.
Proof. exact (TRANS (@lem2613397) (@lem2613481)). Qed.
Lemma lem2613484 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2613485 : term243 = term43.
Proof. exact (@lem2613484 term43). Qed.
Lemma lem2613486 : term454 = term43.
Proof. exact (TRANS (@lem2613482) (@lem2613485)). Qed.
Lemma lem2613487 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613488 : term467 = term464.
Proof. exact (MK_COMB (@lem2613487) (@lem2613486)). Qed.
Lemma lem2613489 (m : int) (n : int) : (term58 m n) = (term58 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem2613490 (m : int) (n : int) : (term451 m n) = (term468 m n).
Proof. exact (MK_COMB (@lem2613488) (@lem2613489 m n)). Qed.
Lemma lem2613491 (m : int) (n : int) : (term450 m n) = (term468 m n).
Proof. exact (TRANS (@lem2613388 m n) (@lem2613490 m n)). Qed.
Lemma lem2613492 (m : int) (n : int) : (term468 m n) = term43.
Proof. exact (@lem1982719 (term58 m n)). Qed.
Lemma lem2613493 (m : int) (n : int) : (term450 m n) = term43.
Proof. exact (TRANS (@lem2613491 m n) (@lem2613492 m n)). Qed.
Lemma lem2613494 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613495 (m : int) (n : int) : (term469 m n) = term45.
Proof. exact (MK_COMB (@lem2613494) (@lem2613493 m n)). Qed.
Lemma lem2613496 (m : int) : (term470 m) = (term471 m).
Proof. exact (@lem1982759 (term198 m) (real_of_int m) term131). Qed.
Lemma lem2613497 (m : int) : (term472 m) = (term473 m).
Proof. exact (@lem1982713 term131 (real_of_int m)). Qed.
Lemma lem2613499 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613500 : term47 = term128.
Proof. exact (@lem2613499 term48). Qed.
Lemma lem2613502 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613503 : term131 = term132.
Proof. exact (@lem2613502 term48). Qed.
Lemma lem2613504 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613505 : term452 = term453.
Proof. exact (MK_COMB (@lem2613504) (@lem2613503)). Qed.
Lemma lem2613506 : term454 = term455.
Proof. exact (MK_COMB (@lem2613505) (@lem2613500)). Qed.
Lemma lem2613507 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2613509 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613510 : term420 = term426.
Proof. exact (@lem2613509 (NUMERAL 0) term48). Qed.
Lemma lem2613511 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613512 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613513 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613512 h1) (fun h1 : term426 = True => @lem2613511)). Qed.
Lemma lem2613514 : term426 = True.
Proof. exact (EQ_MP (@lem2613513) (@lem2613511)). Qed.
Lemma lem2613515 : term420 = True.
Proof. exact (TRANS (@lem2613510) (@lem2613514)). Qed.
Lemma lem2613516 : True = term420.
Proof. exact (SYM (@lem2613515)). Qed.
Lemma lem2613517 : term420.
Proof. exact (EQ_MP (@lem2613516) (@lem0)). Qed.
Lemma lem2613518 : term457.
Proof. exact (@lem2613507 (@lem2613517)). Qed.
Lemma lem2613520 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613521 : term420 = term426.
Proof. exact (@lem2613520 (NUMERAL 0) term48). Qed.
Lemma lem2613522 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613523 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613524 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613523 h1) (fun h1 : term426 = True => @lem2613522)). Qed.
Lemma lem2613525 : term426 = True.
Proof. exact (EQ_MP (@lem2613524) (@lem2613522)). Qed.
Lemma lem2613526 : term420 = True.
Proof. exact (TRANS (@lem2613521) (@lem2613525)). Qed.
Lemma lem2613527 : True = term420.
Proof. exact (SYM (@lem2613526)). Qed.
Lemma lem2613528 : term420.
Proof. exact (EQ_MP (@lem2613527) (@lem0)). Qed.
Lemma lem2613529 : term458.
Proof. exact (@lem2613518 (@lem2613528)). Qed.
Lemma lem2613531 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613532 : term420 = term426.
Proof. exact (@lem2613531 (NUMERAL 0) term48). Qed.
Lemma lem2613533 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613534 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613535 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613534 h1) (fun h1 : term426 = True => @lem2613533)). Qed.
Lemma lem2613536 : term426 = True.
Proof. exact (EQ_MP (@lem2613535) (@lem2613533)). Qed.
Lemma lem2613537 : term420 = True.
Proof. exact (TRANS (@lem2613532) (@lem2613536)). Qed.
Lemma lem2613538 : True = term420.
Proof. exact (SYM (@lem2613537)). Qed.
Lemma lem2613539 : term420.
Proof. exact (EQ_MP (@lem2613538) (@lem0)). Qed.
Lemma lem2613540 : term459.
Proof. exact (@lem2613529 (@lem2613539)). Qed.
Lemma lem2613542 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613543 : term140 = term141.
Proof. exact (@lem2613542 term48 term48). Qed.
Lemma lem2613544 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613545 : term143 = term48.
Proof. exact (EQ_MP (@lem2613544) (@lem940073)). Qed.
Lemma lem2613546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613547 : term141 = term47.
Proof. exact (MK_COMB (@lem2613546) (@lem2613545)). Qed.
Lemma lem2613548 : term140 = term47.
Proof. exact (TRANS (@lem2613543) (@lem2613547)). Qed.
Lemma lem2613550 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2613551 : term135 = term146.
Proof. exact (@lem2613550 term48 term48). Qed.
Lemma lem2613552 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613553 : term143 = term48.
Proof. exact (EQ_MP (@lem2613552) (@lem940073)). Qed.
Lemma lem2613554 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613555 : term141 = term47.
Proof. exact (MK_COMB (@lem2613554) (@lem2613553)). Qed.
Lemma lem2613556 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2613557 : term146 = term131.
Proof. exact (MK_COMB (@lem2613556) (@lem2613555)). Qed.
Lemma lem2613558 : term135 = term131.
Proof. exact (TRANS (@lem2613551) (@lem2613557)). Qed.
Lemma lem2613559 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613560 : term460 = term452.
Proof. exact (MK_COMB (@lem2613559) (@lem2613558)). Qed.
Lemma lem2613561 : term461 = term454.
Proof. exact (MK_COMB (@lem2613560) (@lem2613548)). Qed.
Lemma lem2613563 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2613564 : term454 = term43.
Proof. exact (@lem2613563 term48). Qed.
Lemma lem2613565 : term461 = term43.
Proof. exact (TRANS (@lem2613561) (@lem2613564)). Qed.
Lemma lem2613566 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613567 : term463 = term464.
Proof. exact (MK_COMB (@lem2613566) (@lem2613565)). Qed.
Lemma lem2613568 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2613569 : term465 = term431.
Proof. exact (MK_COMB (@lem2613567) (@lem2613568)). Qed.
Lemma lem2613571 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613572 : term431 = term43.
Proof. exact (@lem2613571 term48). Qed.
Lemma lem2613573 : term465 = term43.
Proof. exact (TRANS (@lem2613569) (@lem2613572)). Qed.
Lemma lem2613575 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613576 : term140 = term141.
Proof. exact (@lem2613575 term48 term48). Qed.
Lemma lem2613577 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613578 : term143 = term48.
Proof. exact (EQ_MP (@lem2613577) (@lem940073)). Qed.
Lemma lem2613579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613580 : term141 = term47.
Proof. exact (MK_COMB (@lem2613579) (@lem2613578)). Qed.
Lemma lem2613581 : term140 = term47.
Proof. exact (TRANS (@lem2613576) (@lem2613580)). Qed.
Lemma lem2613582 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2613583 : term466 = term431.
Proof. exact (MK_COMB (@lem2613582) (@lem2613581)). Qed.
Lemma lem2613585 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613586 : term431 = term43.
Proof. exact (@lem2613585 term48). Qed.
Lemma lem2613587 : term466 = term43.
Proof. exact (TRANS (@lem2613583) (@lem2613586)). Qed.
Lemma lem2613588 : term43 = term466.
Proof. exact (SYM (@lem2613587)). Qed.
Lemma lem2613589 : term465 = term466.
Proof. exact (TRANS (@lem2613573) (@lem2613588)). Qed.
Lemma lem2613590 : term455 = term243.
Proof. exact (@lem2613540 (@lem2613589)). Qed.
Lemma lem2613591 : term454 = term243.
Proof. exact (TRANS (@lem2613506) (@lem2613590)). Qed.
Lemma lem2613593 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2613594 : term243 = term43.
Proof. exact (@lem2613593 term43). Qed.
Lemma lem2613595 : term454 = term43.
Proof. exact (TRANS (@lem2613591) (@lem2613594)). Qed.
Lemma lem2613596 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613597 : term467 = term464.
Proof. exact (MK_COMB (@lem2613596) (@lem2613595)). Qed.
Lemma lem2613598 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2613599 (m : int) : (term473 m) = (term474 m).
Proof. exact (MK_COMB (@lem2613597) (@lem2613598 m)). Qed.
Lemma lem2613600 (m : int) : (term472 m) = (term474 m).
Proof. exact (TRANS (@lem2613497 m) (@lem2613599 m)). Qed.
Lemma lem2613601 (m : int) : (term474 m) = term43.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2613602 (m : int) : (term472 m) = term43.
Proof. exact (TRANS (@lem2613600 m) (@lem2613601 m)). Qed.
Lemma lem2613603 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613604 (m : int) : (term475 m) = term45.
Proof. exact (MK_COMB (@lem2613603) (@lem2613602 m)). Qed.
Lemma lem2613605 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2613606 (m : int) : (term471 m) = term476.
Proof. exact (MK_COMB (@lem2613604 m) (@lem2613605)). Qed.
Lemma lem2613607 (m : int) : (term470 m) = term476.
Proof. exact (TRANS (@lem2613496 m) (@lem2613606 m)). Qed.
Lemma lem2613608 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2613609 (m : int) : (term470 m) = term131.
Proof. exact (TRANS (@lem2613607 m) (@lem2613608)). Qed.
Lemma lem2613610 (n : int) (m : int) : (term449 n m) = term476.
Proof. exact (MK_COMB (@lem2613495 m n) (@lem2613609 m)). Qed.
Lemma lem2613611 (n : int) (m : int) : (term448 n m) = term476.
Proof. exact (TRANS (@lem2613387 n m) (@lem2613610 n m)). Qed.
Lemma lem2613612 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2613613 (n : int) (m : int) : (term448 n m) = term131.
Proof. exact (TRANS (@lem2613611 n m) (@lem2613612)). Qed.
Lemma lem2613614 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2613615 (n : int) (m : int) : (term477 n m) = term478.
Proof. exact (MK_COMB (@lem2613614) (@lem2613613 n m)). Qed.
Lemma lem2613616 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2613617 (n : int) (m : int) : (term447 n m) = term479.
Proof. exact (MK_COMB (@lem2613615 n m) (@lem2613616)). Qed.
Lemma lem2613618 (n : int) (m : int) (h1 : term234 n m) : term479.
Proof. exact (EQ_MP (@lem2613617 n m) (@lem2613386 n m h1)). Qed.
Lemma lem2613620 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2613621 : term479 = term480.
Proof. exact (@lem2613620 term43 term131). Qed.
Lemma lem2613623 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613624 : term131 = term132.
Proof. exact (@lem2613623 term48). Qed.
Lemma lem2613626 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613627 : term43 = term243.
Proof. exact (@lem2613626 (NUMERAL 0)). Qed.
Lemma lem2613628 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2613629 : term481 = term482.
Proof. exact (MK_COMB (@lem2613628) (@lem2613627)). Qed.
Lemma lem2613630 : term480 = term483.
Proof. exact (MK_COMB (@lem2613629) (@lem2613624)). Qed.
Lemma lem2613631 : term484.
Proof. exact (@lem1980026 term43 term47 term131 term47). Qed.
Lemma lem2613633 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613634 : term420 = term426.
Proof. exact (@lem2613633 (NUMERAL 0) term48). Qed.
Lemma lem2613635 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613636 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613637 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613636 h1) (fun h1 : term426 = True => @lem2613635)). Qed.
Lemma lem2613638 : term426 = True.
Proof. exact (EQ_MP (@lem2613637) (@lem2613635)). Qed.
Lemma lem2613639 : term420 = True.
Proof. exact (TRANS (@lem2613634) (@lem2613638)). Qed.
Lemma lem2613640 : True = term420.
Proof. exact (SYM (@lem2613639)). Qed.
Lemma lem2613641 : term420.
Proof. exact (EQ_MP (@lem2613640) (@lem0)). Qed.
Lemma lem2613642 : term485.
Proof. exact (@lem2613631 (@lem2613641)). Qed.
Lemma lem2613644 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613645 : term420 = term426.
Proof. exact (@lem2613644 (NUMERAL 0) term48). Qed.
Lemma lem2613646 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613647 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613648 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613647 h1) (fun h1 : term426 = True => @lem2613646)). Qed.
Lemma lem2613649 : term426 = True.
Proof. exact (EQ_MP (@lem2613648) (@lem2613646)). Qed.
Lemma lem2613650 : term420 = True.
Proof. exact (TRANS (@lem2613645) (@lem2613649)). Qed.
Lemma lem2613651 : True = term420.
Proof. exact (SYM (@lem2613650)). Qed.
Lemma lem2613652 : term420.
Proof. exact (EQ_MP (@lem2613651) (@lem0)). Qed.
Lemma lem2613653 : term483 = term486.
Proof. exact (@lem2613642 (@lem2613652)). Qed.
Lemma lem2613655 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2613656 : term135 = term146.
Proof. exact (@lem2613655 term48 term48). Qed.
Lemma lem2613657 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613658 : term143 = term48.
Proof. exact (EQ_MP (@lem2613657) (@lem940073)). Qed.
Lemma lem2613659 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613660 : term141 = term47.
Proof. exact (MK_COMB (@lem2613659) (@lem2613658)). Qed.
Lemma lem2613661 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2613662 : term146 = term131.
Proof. exact (MK_COMB (@lem2613661) (@lem2613660)). Qed.
Lemma lem2613663 : term135 = term131.
Proof. exact (TRANS (@lem2613656) (@lem2613662)). Qed.
Lemma lem2613665 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613666 : term431 = term43.
Proof. exact (@lem2613665 term48). Qed.
Lemma lem2613667 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2613668 : term487 = term481.
Proof. exact (MK_COMB (@lem2613667) (@lem2613666)). Qed.
Lemma lem2613669 : term486 = term480.
Proof. exact (MK_COMB (@lem2613668) (@lem2613663)). Qed.
Lemma lem2613671 (m : nat) (n : nat) : (term488 m n) = (term489 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2613672 : term480 = term490.
Proof. exact (@lem2613671 (NUMERAL 0) term48). Qed.
Lemma lem2613673 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613674 (h1 : term427 = (BIT1 0)) : (term48 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2613675 : (term427 = (BIT1 0)) = ((term48 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613674 h1) (fun h1 : (term48 = (NUMERAL 0)) = False => @lem2613673)). Qed.
Lemma lem2613676 : (term48 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2613675) (@lem2613673)). Qed.
Lemma lem2613677 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2613678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2613679 : term491 = (and True).
Proof. exact (MK_COMB (@lem2613678) (@lem2613677)). Qed.
Lemma lem2613680 : term490 = (True /\ False).
Proof. exact (MK_COMB (@lem2613679) (@lem2613676)). Qed.
Lemma lem2613682 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2613683 : term490 = False.
Proof. exact (TRANS (@lem2613680) (@lem2613682)). Qed.
Lemma lem2613684 : term480 = False.
Proof. exact (TRANS (@lem2613672) (@lem2613683)). Qed.
Lemma lem2613685 : term486 = False.
Proof. exact (TRANS (@lem2613669) (@lem2613684)). Qed.
Lemma lem2613686 : term483 = False.
Proof. exact (TRANS (@lem2613653) (@lem2613685)). Qed.
Lemma lem2613687 : term480 = False.
Proof. exact (TRANS (@lem2613630) (@lem2613686)). Qed.
Lemma lem2613688 : term479 = False.
Proof. exact (TRANS (@lem2613621) (@lem2613687)). Qed.
Lemma lem2613689 (n : int) (m : int) (h1 : term234 n m) : False.
Proof. exact (EQ_MP (@lem2613688) (@lem2613618 n m h1)). Qed.
Lemma lem2613690 (n : int) (m : int) (h1 : term370 n m) : term370 n m.
Proof. exact (h1). Qed.
Lemma lem2613691 (n : int) (m : int) (h1 : term370 n m) : term368 n m.
Proof. exact (proj2 (@lem2613690 n m h1)). Qed.
Lemma lem2613693 (n : int) (m : int) (h1 : term370 n m) : term365 n m.
Proof. exact (proj2 (@lem2613691 n m h1)). Qed.
Lemma lem2613694 (n : int) (m : int) (h1 : term370 n m) : term337 n m.
Proof. exact (proj1 (@lem2613691 n m h1)). Qed.
Lemma lem2613695 (n : int) (m : int) (h1 : term370 n m) : term335 n m.
Proof. exact (proj2 (@lem2613694 n m h1)). Qed.
Lemma lem2613697 (n : int) (m : int) (h1 : term370 n m) : term331 n m.
Proof. exact (proj2 (@lem2613695 n m h1)). Qed.
Lemma lem2613700 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2613701 : term419 = term420.
Proof. exact (@lem2613700 term43 term47). Qed.
Lemma lem2613703 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613704 : term47 = term128.
Proof. exact (@lem2613703 term48). Qed.
Lemma lem2613706 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613707 : term43 = term243.
Proof. exact (@lem2613706 (NUMERAL 0)). Qed.
Lemma lem2613708 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2613709 : term421 = term422.
Proof. exact (MK_COMB (@lem2613708) (@lem2613707)). Qed.
Lemma lem2613710 : term420 = term423.
Proof. exact (MK_COMB (@lem2613709) (@lem2613704)). Qed.
Lemma lem2613711 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2613713 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613714 : term420 = term426.
Proof. exact (@lem2613713 (NUMERAL 0) term48). Qed.
Lemma lem2613715 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613716 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613717 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613716 h1) (fun h1 : term426 = True => @lem2613715)). Qed.
Lemma lem2613718 : term426 = True.
Proof. exact (EQ_MP (@lem2613717) (@lem2613715)). Qed.
Lemma lem2613719 : term420 = True.
Proof. exact (TRANS (@lem2613714) (@lem2613718)). Qed.
Lemma lem2613720 : True = term420.
Proof. exact (SYM (@lem2613719)). Qed.
Lemma lem2613721 : term420.
Proof. exact (EQ_MP (@lem2613720) (@lem0)). Qed.
Lemma lem2613722 : term428.
Proof. exact (@lem2613711 (@lem2613721)). Qed.
Lemma lem2613724 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613725 : term420 = term426.
Proof. exact (@lem2613724 (NUMERAL 0) term48). Qed.
Lemma lem2613726 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613727 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613728 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613727 h1) (fun h1 : term426 = True => @lem2613726)). Qed.
Lemma lem2613729 : term426 = True.
Proof. exact (EQ_MP (@lem2613728) (@lem2613726)). Qed.
Lemma lem2613730 : term420 = True.
Proof. exact (TRANS (@lem2613725) (@lem2613729)). Qed.
Lemma lem2613731 : True = term420.
Proof. exact (SYM (@lem2613730)). Qed.
Lemma lem2613732 : term420.
Proof. exact (EQ_MP (@lem2613731) (@lem0)). Qed.
Lemma lem2613733 : term423 = term429.
Proof. exact (@lem2613722 (@lem2613732)). Qed.
Lemma lem2613735 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613736 : term140 = term141.
Proof. exact (@lem2613735 term48 term48). Qed.
Lemma lem2613737 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613738 : term143 = term48.
Proof. exact (EQ_MP (@lem2613737) (@lem940073)). Qed.
Lemma lem2613739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613740 : term141 = term47.
Proof. exact (MK_COMB (@lem2613739) (@lem2613738)). Qed.
Lemma lem2613741 : term140 = term47.
Proof. exact (TRANS (@lem2613736) (@lem2613740)). Qed.
Lemma lem2613743 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613744 : term431 = term43.
Proof. exact (@lem2613743 term48). Qed.
Lemma lem2613745 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2613746 : term432 = term421.
Proof. exact (MK_COMB (@lem2613745) (@lem2613744)). Qed.
Lemma lem2613747 : term429 = term420.
Proof. exact (MK_COMB (@lem2613746) (@lem2613741)). Qed.
Lemma lem2613749 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613750 : term420 = term426.
Proof. exact (@lem2613749 (NUMERAL 0) term48). Qed.
Lemma lem2613751 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613752 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613753 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613752 h1) (fun h1 : term426 = True => @lem2613751)). Qed.
Lemma lem2613754 : term426 = True.
Proof. exact (EQ_MP (@lem2613753) (@lem2613751)). Qed.
Lemma lem2613755 : term420 = True.
Proof. exact (TRANS (@lem2613750) (@lem2613754)). Qed.
Lemma lem2613756 : term429 = True.
Proof. exact (TRANS (@lem2613747) (@lem2613755)). Qed.
Lemma lem2613757 : term423 = True.
Proof. exact (TRANS (@lem2613733) (@lem2613756)). Qed.
Lemma lem2613758 : term420 = True.
Proof. exact (TRANS (@lem2613710) (@lem2613757)). Qed.
Lemma lem2613759 : term419 = True.
Proof. exact (TRANS (@lem2613701) (@lem2613758)). Qed.
Lemma lem2613760 : True = term419.
Proof. exact (SYM (@lem2613759)). Qed.
Lemma lem2613761 : term419.
Proof. exact (EQ_MP (@lem2613760) (@lem0)). Qed.
Lemma lem2613762 (n : int) (m : int) (h1 : term370 n m) : term492 n m.
Proof. exact (conj (@lem2613761) (@lem2613693 n m h1)). Qed.
Lemma lem2613764 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2613765 (n : int) (m : int) : term493 n m.
Proof. exact (@lem2613764 term47 (term355 n m)). Qed.
Lemma lem2613766 (n : int) (m : int) (h1 : term370 n m) : term494 n m.
Proof. exact (@lem2613765 n m (@lem2613762 n m h1)). Qed.
Lemma lem2613767 (n : int) (m : int) : (term495 n m) = (term355 n m).
Proof. exact (@lem1982733 (term355 n m)). Qed.
Lemma lem2613768 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2613769 (n : int) (m : int) : (term496 n m) = (term364 n m).
Proof. exact (MK_COMB (@lem2613768) (@lem2613767 n m)). Qed.
Lemma lem2613770 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2613771 (n : int) (m : int) : (term494 n m) = (term365 n m).
Proof. exact (MK_COMB (@lem2613769 n m) (@lem2613770)). Qed.
Lemma lem2613772 (n : int) (m : int) (h1 : term370 n m) : term365 n m.
Proof. exact (EQ_MP (@lem2613771 n m) (@lem2613766 n m h1)). Qed.
Lemma lem2613774 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2613775 : term419 = term420.
Proof. exact (@lem2613774 term43 term47). Qed.
Lemma lem2613777 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613778 : term47 = term128.
Proof. exact (@lem2613777 term48). Qed.
Lemma lem2613780 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613781 : term43 = term243.
Proof. exact (@lem2613780 (NUMERAL 0)). Qed.
Lemma lem2613782 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2613783 : term421 = term422.
Proof. exact (MK_COMB (@lem2613782) (@lem2613781)). Qed.
Lemma lem2613784 : term420 = term423.
Proof. exact (MK_COMB (@lem2613783) (@lem2613778)). Qed.
Lemma lem2613785 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2613787 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613788 : term420 = term426.
Proof. exact (@lem2613787 (NUMERAL 0) term48). Qed.
Lemma lem2613789 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613790 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613791 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613790 h1) (fun h1 : term426 = True => @lem2613789)). Qed.
Lemma lem2613792 : term426 = True.
Proof. exact (EQ_MP (@lem2613791) (@lem2613789)). Qed.
Lemma lem2613793 : term420 = True.
Proof. exact (TRANS (@lem2613788) (@lem2613792)). Qed.
Lemma lem2613794 : True = term420.
Proof. exact (SYM (@lem2613793)). Qed.
Lemma lem2613795 : term420.
Proof. exact (EQ_MP (@lem2613794) (@lem0)). Qed.
Lemma lem2613796 : term428.
Proof. exact (@lem2613785 (@lem2613795)). Qed.
Lemma lem2613798 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613799 : term420 = term426.
Proof. exact (@lem2613798 (NUMERAL 0) term48). Qed.
Lemma lem2613800 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613801 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613802 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613801 h1) (fun h1 : term426 = True => @lem2613800)). Qed.
Lemma lem2613803 : term426 = True.
Proof. exact (EQ_MP (@lem2613802) (@lem2613800)). Qed.
Lemma lem2613804 : term420 = True.
Proof. exact (TRANS (@lem2613799) (@lem2613803)). Qed.
Lemma lem2613805 : True = term420.
Proof. exact (SYM (@lem2613804)). Qed.
Lemma lem2613806 : term420.
Proof. exact (EQ_MP (@lem2613805) (@lem0)). Qed.
Lemma lem2613807 : term423 = term429.
Proof. exact (@lem2613796 (@lem2613806)). Qed.
Lemma lem2613809 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613810 : term140 = term141.
Proof. exact (@lem2613809 term48 term48). Qed.
Lemma lem2613811 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613812 : term143 = term48.
Proof. exact (EQ_MP (@lem2613811) (@lem940073)). Qed.
Lemma lem2613813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613814 : term141 = term47.
Proof. exact (MK_COMB (@lem2613813) (@lem2613812)). Qed.
Lemma lem2613815 : term140 = term47.
Proof. exact (TRANS (@lem2613810) (@lem2613814)). Qed.
Lemma lem2613817 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613818 : term431 = term43.
Proof. exact (@lem2613817 term48). Qed.
Lemma lem2613819 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2613820 : term432 = term421.
Proof. exact (MK_COMB (@lem2613819) (@lem2613818)). Qed.
Lemma lem2613821 : term429 = term420.
Proof. exact (MK_COMB (@lem2613820) (@lem2613815)). Qed.
Lemma lem2613823 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613824 : term420 = term426.
Proof. exact (@lem2613823 (NUMERAL 0) term48). Qed.
Lemma lem2613825 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613826 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613827 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613826 h1) (fun h1 : term426 = True => @lem2613825)). Qed.
Lemma lem2613828 : term426 = True.
Proof. exact (EQ_MP (@lem2613827) (@lem2613825)). Qed.
Lemma lem2613829 : term420 = True.
Proof. exact (TRANS (@lem2613824) (@lem2613828)). Qed.
Lemma lem2613830 : term429 = True.
Proof. exact (TRANS (@lem2613821) (@lem2613829)). Qed.
Lemma lem2613831 : term423 = True.
Proof. exact (TRANS (@lem2613807) (@lem2613830)). Qed.
Lemma lem2613832 : term420 = True.
Proof. exact (TRANS (@lem2613784) (@lem2613831)). Qed.
Lemma lem2613833 : term419 = True.
Proof. exact (TRANS (@lem2613775) (@lem2613832)). Qed.
Lemma lem2613834 : True = term419.
Proof. exact (SYM (@lem2613833)). Qed.
Lemma lem2613835 : term419.
Proof. exact (EQ_MP (@lem2613834) (@lem0)). Qed.
Lemma lem2613836 (n : int) (m : int) (h1 : term370 n m) : term497 n m.
Proof. exact (conj (@lem2613835) (@lem2613697 n m h1)). Qed.
Lemma lem2613838 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2613839 (n : int) (m : int) : term498 n m.
Proof. exact (@lem2613838 term47 (term321 n m)). Qed.
Lemma lem2613840 (n : int) (m : int) (h1 : term370 n m) : term499 n m.
Proof. exact (@lem2613839 n m (@lem2613836 n m h1)). Qed.
Lemma lem2613841 (n : int) (m : int) : (term500 n m) = (term321 n m).
Proof. exact (@lem1982733 (term321 n m)). Qed.
Lemma lem2613842 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2613843 (n : int) (m : int) : (term501 n m) = (term330 n m).
Proof. exact (MK_COMB (@lem2613842) (@lem2613841 n m)). Qed.
Lemma lem2613844 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2613845 (n : int) (m : int) : (term499 n m) = (term331 n m).
Proof. exact (MK_COMB (@lem2613843 n m) (@lem2613844)). Qed.
Lemma lem2613846 (n : int) (m : int) (h1 : term370 n m) : term331 n m.
Proof. exact (EQ_MP (@lem2613845 n m) (@lem2613840 n m h1)). Qed.
Lemma lem2613847 (n : int) (m : int) (h1 : term370 n m) : term502 n m.
Proof. exact (conj (@lem2613846 n m h1) (@lem2613772 n m h1)). Qed.
Lemma lem2613849 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2613850 (n : int) (m : int) : term503 n m.
Proof. exact (@lem2613849 (term321 n m) (term355 n m)). Qed.
Lemma lem2613851 (n : int) (m : int) (h1 : term370 n m) : term504 n m.
Proof. exact (@lem2613850 n m (@lem2613847 n m h1)). Qed.
Lemma lem2613852 (n : int) (m : int) : (term505 n m) = (term506 n m).
Proof. exact (@lem1982753 (term304 m n) (term58 m n) (real_of_int m) (term178 m)). Qed.
Lemma lem2613853 (m : int) (n : int) : (term450 m n) = (term451 m n).
Proof. exact (@lem1982713 term131 (term58 m n)). Qed.
Lemma lem2613855 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613856 : term47 = term128.
Proof. exact (@lem2613855 term48). Qed.
Lemma lem2613858 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613859 : term131 = term132.
Proof. exact (@lem2613858 term48). Qed.
Lemma lem2613860 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613861 : term452 = term453.
Proof. exact (MK_COMB (@lem2613860) (@lem2613859)). Qed.
Lemma lem2613862 : term454 = term455.
Proof. exact (MK_COMB (@lem2613861) (@lem2613856)). Qed.
Lemma lem2613863 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2613865 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613866 : term420 = term426.
Proof. exact (@lem2613865 (NUMERAL 0) term48). Qed.
Lemma lem2613867 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613868 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613869 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613868 h1) (fun h1 : term426 = True => @lem2613867)). Qed.
Lemma lem2613870 : term426 = True.
Proof. exact (EQ_MP (@lem2613869) (@lem2613867)). Qed.
Lemma lem2613871 : term420 = True.
Proof. exact (TRANS (@lem2613866) (@lem2613870)). Qed.
Lemma lem2613872 : True = term420.
Proof. exact (SYM (@lem2613871)). Qed.
Lemma lem2613873 : term420.
Proof. exact (EQ_MP (@lem2613872) (@lem0)). Qed.
Lemma lem2613874 : term457.
Proof. exact (@lem2613863 (@lem2613873)). Qed.
Lemma lem2613876 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613877 : term420 = term426.
Proof. exact (@lem2613876 (NUMERAL 0) term48). Qed.
Lemma lem2613878 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613879 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613880 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613879 h1) (fun h1 : term426 = True => @lem2613878)). Qed.
Lemma lem2613881 : term426 = True.
Proof. exact (EQ_MP (@lem2613880) (@lem2613878)). Qed.
Lemma lem2613882 : term420 = True.
Proof. exact (TRANS (@lem2613877) (@lem2613881)). Qed.
Lemma lem2613883 : True = term420.
Proof. exact (SYM (@lem2613882)). Qed.
Lemma lem2613884 : term420.
Proof. exact (EQ_MP (@lem2613883) (@lem0)). Qed.
Lemma lem2613885 : term458.
Proof. exact (@lem2613874 (@lem2613884)). Qed.
Lemma lem2613887 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613888 : term420 = term426.
Proof. exact (@lem2613887 (NUMERAL 0) term48). Qed.
Lemma lem2613889 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613890 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613891 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613890 h1) (fun h1 : term426 = True => @lem2613889)). Qed.
Lemma lem2613892 : term426 = True.
Proof. exact (EQ_MP (@lem2613891) (@lem2613889)). Qed.
Lemma lem2613893 : term420 = True.
Proof. exact (TRANS (@lem2613888) (@lem2613892)). Qed.
Lemma lem2613894 : True = term420.
Proof. exact (SYM (@lem2613893)). Qed.
Lemma lem2613895 : term420.
Proof. exact (EQ_MP (@lem2613894) (@lem0)). Qed.
Lemma lem2613896 : term459.
Proof. exact (@lem2613885 (@lem2613895)). Qed.
Lemma lem2613898 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613899 : term140 = term141.
Proof. exact (@lem2613898 term48 term48). Qed.
Lemma lem2613900 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613901 : term143 = term48.
Proof. exact (EQ_MP (@lem2613900) (@lem940073)). Qed.
Lemma lem2613902 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613903 : term141 = term47.
Proof. exact (MK_COMB (@lem2613902) (@lem2613901)). Qed.
Lemma lem2613904 : term140 = term47.
Proof. exact (TRANS (@lem2613899) (@lem2613903)). Qed.
Lemma lem2613906 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2613907 : term135 = term146.
Proof. exact (@lem2613906 term48 term48). Qed.
Lemma lem2613908 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613909 : term143 = term48.
Proof. exact (EQ_MP (@lem2613908) (@lem940073)). Qed.
Lemma lem2613910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613911 : term141 = term47.
Proof. exact (MK_COMB (@lem2613910) (@lem2613909)). Qed.
Lemma lem2613912 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2613913 : term146 = term131.
Proof. exact (MK_COMB (@lem2613912) (@lem2613911)). Qed.
Lemma lem2613914 : term135 = term131.
Proof. exact (TRANS (@lem2613907) (@lem2613913)). Qed.
Lemma lem2613915 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613916 : term460 = term452.
Proof. exact (MK_COMB (@lem2613915) (@lem2613914)). Qed.
Lemma lem2613917 : term461 = term454.
Proof. exact (MK_COMB (@lem2613916) (@lem2613904)). Qed.
Lemma lem2613919 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2613920 : term454 = term43.
Proof. exact (@lem2613919 term48). Qed.
Lemma lem2613921 : term461 = term43.
Proof. exact (TRANS (@lem2613917) (@lem2613920)). Qed.
Lemma lem2613922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613923 : term463 = term464.
Proof. exact (MK_COMB (@lem2613922) (@lem2613921)). Qed.
Lemma lem2613924 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2613925 : term465 = term431.
Proof. exact (MK_COMB (@lem2613923) (@lem2613924)). Qed.
Lemma lem2613927 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613928 : term431 = term43.
Proof. exact (@lem2613927 term48). Qed.
Lemma lem2613929 : term465 = term43.
Proof. exact (TRANS (@lem2613925) (@lem2613928)). Qed.
Lemma lem2613931 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2613932 : term140 = term141.
Proof. exact (@lem2613931 term48 term48). Qed.
Lemma lem2613933 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2613934 : term143 = term48.
Proof. exact (EQ_MP (@lem2613933) (@lem940073)). Qed.
Lemma lem2613935 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2613936 : term141 = term47.
Proof. exact (MK_COMB (@lem2613935) (@lem2613934)). Qed.
Lemma lem2613937 : term140 = term47.
Proof. exact (TRANS (@lem2613932) (@lem2613936)). Qed.
Lemma lem2613938 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2613939 : term466 = term431.
Proof. exact (MK_COMB (@lem2613938) (@lem2613937)). Qed.
Lemma lem2613941 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2613942 : term431 = term43.
Proof. exact (@lem2613941 term48). Qed.
Lemma lem2613943 : term466 = term43.
Proof. exact (TRANS (@lem2613939) (@lem2613942)). Qed.
Lemma lem2613944 : term43 = term466.
Proof. exact (SYM (@lem2613943)). Qed.
Lemma lem2613945 : term465 = term466.
Proof. exact (TRANS (@lem2613929) (@lem2613944)). Qed.
Lemma lem2613946 : term455 = term243.
Proof. exact (@lem2613896 (@lem2613945)). Qed.
Lemma lem2613947 : term454 = term243.
Proof. exact (TRANS (@lem2613862) (@lem2613946)). Qed.
Lemma lem2613949 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2613950 : term243 = term43.
Proof. exact (@lem2613949 term43). Qed.
Lemma lem2613951 : term454 = term43.
Proof. exact (TRANS (@lem2613947) (@lem2613950)). Qed.
Lemma lem2613952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2613953 : term467 = term464.
Proof. exact (MK_COMB (@lem2613952) (@lem2613951)). Qed.
Lemma lem2613954 (m : int) (n : int) : (term58 m n) = (term58 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem2613955 (m : int) (n : int) : (term451 m n) = (term468 m n).
Proof. exact (MK_COMB (@lem2613953) (@lem2613954 m n)). Qed.
Lemma lem2613956 (m : int) (n : int) : (term450 m n) = (term468 m n).
Proof. exact (TRANS (@lem2613853 m n) (@lem2613955 m n)). Qed.
Lemma lem2613957 (m : int) (n : int) : (term468 m n) = term43.
Proof. exact (@lem1982719 (term58 m n)). Qed.
Lemma lem2613958 (m : int) (n : int) : (term450 m n) = term43.
Proof. exact (TRANS (@lem2613956 m n) (@lem2613957 m n)). Qed.
Lemma lem2613959 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613960 (m : int) (n : int) : (term469 m n) = term45.
Proof. exact (MK_COMB (@lem2613959) (@lem2613958 m n)). Qed.
Lemma lem2613961 (m : int) : (term507 m) = (term508 m).
Proof. exact (@lem1982763 (real_of_int m) (term198 m) term131). Qed.
Lemma lem2613962 (m : int) : (term509 m) = (term473 m).
Proof. exact (@lem1982715 term131 (real_of_int m)). Qed.
Lemma lem2613964 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2613965 : term47 = term128.
Proof. exact (@lem2613964 term48). Qed.
Lemma lem2613967 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2613968 : term131 = term132.
Proof. exact (@lem2613967 term48). Qed.
Lemma lem2613969 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2613970 : term452 = term453.
Proof. exact (MK_COMB (@lem2613969) (@lem2613968)). Qed.
Lemma lem2613971 : term454 = term455.
Proof. exact (MK_COMB (@lem2613970) (@lem2613965)). Qed.
Lemma lem2613972 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2613974 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613975 : term420 = term426.
Proof. exact (@lem2613974 (NUMERAL 0) term48). Qed.
Lemma lem2613976 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613977 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613978 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613977 h1) (fun h1 : term426 = True => @lem2613976)). Qed.
Lemma lem2613979 : term426 = True.
Proof. exact (EQ_MP (@lem2613978) (@lem2613976)). Qed.
Lemma lem2613980 : term420 = True.
Proof. exact (TRANS (@lem2613975) (@lem2613979)). Qed.
Lemma lem2613981 : True = term420.
Proof. exact (SYM (@lem2613980)). Qed.
Lemma lem2613982 : term420.
Proof. exact (EQ_MP (@lem2613981) (@lem0)). Qed.
Lemma lem2613983 : term457.
Proof. exact (@lem2613972 (@lem2613982)). Qed.
Lemma lem2613985 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613986 : term420 = term426.
Proof. exact (@lem2613985 (NUMERAL 0) term48). Qed.
Lemma lem2613987 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613988 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2613989 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613988 h1) (fun h1 : term426 = True => @lem2613987)). Qed.
Lemma lem2613990 : term426 = True.
Proof. exact (EQ_MP (@lem2613989) (@lem2613987)). Qed.
Lemma lem2613991 : term420 = True.
Proof. exact (TRANS (@lem2613986) (@lem2613990)). Qed.
Lemma lem2613992 : True = term420.
Proof. exact (SYM (@lem2613991)). Qed.
Lemma lem2613993 : term420.
Proof. exact (EQ_MP (@lem2613992) (@lem0)). Qed.
Lemma lem2613994 : term458.
Proof. exact (@lem2613983 (@lem2613993)). Qed.
Lemma lem2613996 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2613997 : term420 = term426.
Proof. exact (@lem2613996 (NUMERAL 0) term48). Qed.
Lemma lem2613998 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2613999 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614000 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2613999 h1) (fun h1 : term426 = True => @lem2613998)). Qed.
Lemma lem2614001 : term426 = True.
Proof. exact (EQ_MP (@lem2614000) (@lem2613998)). Qed.
Lemma lem2614002 : term420 = True.
Proof. exact (TRANS (@lem2613997) (@lem2614001)). Qed.
Lemma lem2614003 : True = term420.
Proof. exact (SYM (@lem2614002)). Qed.
Lemma lem2614004 : term420.
Proof. exact (EQ_MP (@lem2614003) (@lem0)). Qed.
Lemma lem2614005 : term459.
Proof. exact (@lem2613994 (@lem2614004)). Qed.
Lemma lem2614007 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614008 : term140 = term141.
Proof. exact (@lem2614007 term48 term48). Qed.
Lemma lem2614009 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614010 : term143 = term48.
Proof. exact (EQ_MP (@lem2614009) (@lem940073)). Qed.
Lemma lem2614011 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614012 : term141 = term47.
Proof. exact (MK_COMB (@lem2614011) (@lem2614010)). Qed.
Lemma lem2614013 : term140 = term47.
Proof. exact (TRANS (@lem2614008) (@lem2614012)). Qed.
Lemma lem2614015 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2614016 : term135 = term146.
Proof. exact (@lem2614015 term48 term48). Qed.
Lemma lem2614017 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614018 : term143 = term48.
Proof. exact (EQ_MP (@lem2614017) (@lem940073)). Qed.
Lemma lem2614019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614020 : term141 = term47.
Proof. exact (MK_COMB (@lem2614019) (@lem2614018)). Qed.
Lemma lem2614021 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2614022 : term146 = term131.
Proof. exact (MK_COMB (@lem2614021) (@lem2614020)). Qed.
Lemma lem2614023 : term135 = term131.
Proof. exact (TRANS (@lem2614016) (@lem2614022)). Qed.
Lemma lem2614024 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614025 : term460 = term452.
Proof. exact (MK_COMB (@lem2614024) (@lem2614023)). Qed.
Lemma lem2614026 : term461 = term454.
Proof. exact (MK_COMB (@lem2614025) (@lem2614013)). Qed.
Lemma lem2614028 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2614029 : term454 = term43.
Proof. exact (@lem2614028 term48). Qed.
Lemma lem2614030 : term461 = term43.
Proof. exact (TRANS (@lem2614026) (@lem2614029)). Qed.
Lemma lem2614031 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2614032 : term463 = term464.
Proof. exact (MK_COMB (@lem2614031) (@lem2614030)). Qed.
Lemma lem2614033 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2614034 : term465 = term431.
Proof. exact (MK_COMB (@lem2614032) (@lem2614033)). Qed.
Lemma lem2614036 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614037 : term431 = term43.
Proof. exact (@lem2614036 term48). Qed.
Lemma lem2614038 : term465 = term43.
Proof. exact (TRANS (@lem2614034) (@lem2614037)). Qed.
Lemma lem2614040 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614041 : term140 = term141.
Proof. exact (@lem2614040 term48 term48). Qed.
Lemma lem2614042 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614043 : term143 = term48.
Proof. exact (EQ_MP (@lem2614042) (@lem940073)). Qed.
Lemma lem2614044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614045 : term141 = term47.
Proof. exact (MK_COMB (@lem2614044) (@lem2614043)). Qed.
Lemma lem2614046 : term140 = term47.
Proof. exact (TRANS (@lem2614041) (@lem2614045)). Qed.
Lemma lem2614047 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2614048 : term466 = term431.
Proof. exact (MK_COMB (@lem2614047) (@lem2614046)). Qed.
Lemma lem2614050 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614051 : term431 = term43.
Proof. exact (@lem2614050 term48). Qed.
Lemma lem2614052 : term466 = term43.
Proof. exact (TRANS (@lem2614048) (@lem2614051)). Qed.
Lemma lem2614053 : term43 = term466.
Proof. exact (SYM (@lem2614052)). Qed.
Lemma lem2614054 : term465 = term466.
Proof. exact (TRANS (@lem2614038) (@lem2614053)). Qed.
Lemma lem2614055 : term455 = term243.
Proof. exact (@lem2614005 (@lem2614054)). Qed.
Lemma lem2614056 : term454 = term243.
Proof. exact (TRANS (@lem2613971) (@lem2614055)). Qed.
Lemma lem2614058 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2614059 : term243 = term43.
Proof. exact (@lem2614058 term43). Qed.
Lemma lem2614060 : term454 = term43.
Proof. exact (TRANS (@lem2614056) (@lem2614059)). Qed.
Lemma lem2614061 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2614062 : term467 = term464.
Proof. exact (MK_COMB (@lem2614061) (@lem2614060)). Qed.
Lemma lem2614063 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2614064 (m : int) : (term473 m) = (term474 m).
Proof. exact (MK_COMB (@lem2614062) (@lem2614063 m)). Qed.
Lemma lem2614065 (m : int) : (term509 m) = (term474 m).
Proof. exact (TRANS (@lem2613962 m) (@lem2614064 m)). Qed.
Lemma lem2614066 (m : int) : (term474 m) = term43.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2614067 (m : int) : (term509 m) = term43.
Proof. exact (TRANS (@lem2614065 m) (@lem2614066 m)). Qed.
Lemma lem2614068 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614069 (m : int) : (term510 m) = term45.
Proof. exact (MK_COMB (@lem2614068) (@lem2614067 m)). Qed.
Lemma lem2614070 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2614071 (m : int) : (term508 m) = term476.
Proof. exact (MK_COMB (@lem2614069 m) (@lem2614070)). Qed.
Lemma lem2614072 (m : int) : (term507 m) = term476.
Proof. exact (TRANS (@lem2613961 m) (@lem2614071 m)). Qed.
Lemma lem2614073 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2614074 (m : int) : (term507 m) = term131.
Proof. exact (TRANS (@lem2614072 m) (@lem2614073)). Qed.
Lemma lem2614075 (n : int) (m : int) : (term506 n m) = term476.
Proof. exact (MK_COMB (@lem2613960 m n) (@lem2614074 m)). Qed.
Lemma lem2614076 (n : int) (m : int) : (term505 n m) = term476.
Proof. exact (TRANS (@lem2613852 n m) (@lem2614075 n m)). Qed.
Lemma lem2614077 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2614078 (n : int) (m : int) : (term505 n m) = term131.
Proof. exact (TRANS (@lem2614076 n m) (@lem2614077)). Qed.
Lemma lem2614079 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2614080 (n : int) (m : int) : (term511 n m) = term478.
Proof. exact (MK_COMB (@lem2614079) (@lem2614078 n m)). Qed.
Lemma lem2614081 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2614082 (n : int) (m : int) : (term504 n m) = term479.
Proof. exact (MK_COMB (@lem2614080 n m) (@lem2614081)). Qed.
Lemma lem2614083 (n : int) (m : int) (h1 : term370 n m) : term479.
Proof. exact (EQ_MP (@lem2614082 n m) (@lem2613851 n m h1)). Qed.
Lemma lem2614085 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2614086 : term479 = term480.
Proof. exact (@lem2614085 term43 term131). Qed.
Lemma lem2614088 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2614089 : term131 = term132.
Proof. exact (@lem2614088 term48). Qed.
Lemma lem2614091 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614092 : term43 = term243.
Proof. exact (@lem2614091 (NUMERAL 0)). Qed.
Lemma lem2614093 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2614094 : term481 = term482.
Proof. exact (MK_COMB (@lem2614093) (@lem2614092)). Qed.
Lemma lem2614095 : term480 = term483.
Proof. exact (MK_COMB (@lem2614094) (@lem2614089)). Qed.
Lemma lem2614096 : term484.
Proof. exact (@lem1980026 term43 term47 term131 term47). Qed.
Lemma lem2614098 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614099 : term420 = term426.
Proof. exact (@lem2614098 (NUMERAL 0) term48). Qed.
Lemma lem2614100 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614101 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614102 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614101 h1) (fun h1 : term426 = True => @lem2614100)). Qed.
Lemma lem2614103 : term426 = True.
Proof. exact (EQ_MP (@lem2614102) (@lem2614100)). Qed.
Lemma lem2614104 : term420 = True.
Proof. exact (TRANS (@lem2614099) (@lem2614103)). Qed.
Lemma lem2614105 : True = term420.
Proof. exact (SYM (@lem2614104)). Qed.
Lemma lem2614106 : term420.
Proof. exact (EQ_MP (@lem2614105) (@lem0)). Qed.
Lemma lem2614107 : term485.
Proof. exact (@lem2614096 (@lem2614106)). Qed.
Lemma lem2614109 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614110 : term420 = term426.
Proof. exact (@lem2614109 (NUMERAL 0) term48). Qed.
Lemma lem2614111 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614112 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614113 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614112 h1) (fun h1 : term426 = True => @lem2614111)). Qed.
Lemma lem2614114 : term426 = True.
Proof. exact (EQ_MP (@lem2614113) (@lem2614111)). Qed.
Lemma lem2614115 : term420 = True.
Proof. exact (TRANS (@lem2614110) (@lem2614114)). Qed.
Lemma lem2614116 : True = term420.
Proof. exact (SYM (@lem2614115)). Qed.
Lemma lem2614117 : term420.
Proof. exact (EQ_MP (@lem2614116) (@lem0)). Qed.
Lemma lem2614118 : term483 = term486.
Proof. exact (@lem2614107 (@lem2614117)). Qed.
Lemma lem2614120 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2614121 : term135 = term146.
Proof. exact (@lem2614120 term48 term48). Qed.
Lemma lem2614122 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614123 : term143 = term48.
Proof. exact (EQ_MP (@lem2614122) (@lem940073)). Qed.
Lemma lem2614124 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614125 : term141 = term47.
Proof. exact (MK_COMB (@lem2614124) (@lem2614123)). Qed.
Lemma lem2614126 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2614127 : term146 = term131.
Proof. exact (MK_COMB (@lem2614126) (@lem2614125)). Qed.
Lemma lem2614128 : term135 = term131.
Proof. exact (TRANS (@lem2614121) (@lem2614127)). Qed.
Lemma lem2614130 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614131 : term431 = term43.
Proof. exact (@lem2614130 term48). Qed.
Lemma lem2614132 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2614133 : term487 = term481.
Proof. exact (MK_COMB (@lem2614132) (@lem2614131)). Qed.
Lemma lem2614134 : term486 = term480.
Proof. exact (MK_COMB (@lem2614133) (@lem2614128)). Qed.
Lemma lem2614136 (m : nat) (n : nat) : (term488 m n) = (term489 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2614137 : term480 = term490.
Proof. exact (@lem2614136 (NUMERAL 0) term48). Qed.
Lemma lem2614138 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614139 (h1 : term427 = (BIT1 0)) : (term48 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2614140 : (term427 = (BIT1 0)) = ((term48 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614139 h1) (fun h1 : (term48 = (NUMERAL 0)) = False => @lem2614138)). Qed.
Lemma lem2614141 : (term48 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2614140) (@lem2614138)). Qed.
Lemma lem2614142 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2614143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2614144 : term491 = (and True).
Proof. exact (MK_COMB (@lem2614143) (@lem2614142)). Qed.
Lemma lem2614145 : term490 = (True /\ False).
Proof. exact (MK_COMB (@lem2614144) (@lem2614141)). Qed.
Lemma lem2614147 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2614148 : term490 = False.
Proof. exact (TRANS (@lem2614145) (@lem2614147)). Qed.
Lemma lem2614149 : term480 = False.
Proof. exact (TRANS (@lem2614137) (@lem2614148)). Qed.
Lemma lem2614150 : term486 = False.
Proof. exact (TRANS (@lem2614134) (@lem2614149)). Qed.
Lemma lem2614151 : term483 = False.
Proof. exact (TRANS (@lem2614118) (@lem2614150)). Qed.
Lemma lem2614152 : term480 = False.
Proof. exact (TRANS (@lem2614095) (@lem2614151)). Qed.
Lemma lem2614153 : term479 = False.
Proof. exact (TRANS (@lem2614086) (@lem2614152)). Qed.
Lemma lem2614154 (n : int) (m : int) (h1 : term370 n m) : False.
Proof. exact (EQ_MP (@lem2614153) (@lem2614083 n m h1)). Qed.
Lemma lem2614155 (n : int) (m : int) (h1 : term371 n m) : False.
Proof. exact (or_elim (@lem2613224 n m h1) (fun h0 : term234 n m => @lem2613689 n m h0) (fun h0 : term370 n m => @lem2614154 n m h0)). Qed.
Lemma lem2614156 (m : int) (n : int) (h1 : term415 m n) : term415 m n.
Proof. exact (h1). Qed.
Lemma lem2614157 (m : int) (n : int) (h1 : term384 m n) : term384 m n.
Proof. exact (h1). Qed.
Lemma lem2614158 (m : int) (n : int) (h1 : term384 m n) : term382 m n.
Proof. exact (proj2 (@lem2614157 m n h1)). Qed.
Lemma lem2614160 (m : int) (n : int) (h1 : term384 m n) : term389 m n.
Proof. exact (proj2 (@lem2614158 m n h1)). Qed.
Lemma lem2614161 (m : int) (n : int) (h1 : term384 m n) : term279 n m.
Proof. exact (proj1 (@lem2614158 m n h1)). Qed.
Lemma lem2614162 (m : int) (n : int) (h1 : term384 m n) : term278 n m.
Proof. exact (proj2 (@lem2614161 m n h1)). Qed.
Lemma lem2614163 (m : int) (n : int) (h1 : term384 m n) : term153 n.
Proof. exact (proj1 (@lem2614161 m n h1)). Qed.
Lemma lem2614165 (m : int) (n : int) (h1 : term384 m n) : term259 n m.
Proof. exact (proj1 (@lem2614162 m n h1)). Qed.
Lemma lem2614167 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2614168 : term419 = term420.
Proof. exact (@lem2614167 term43 term47). Qed.
Lemma lem2614170 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614171 : term47 = term128.
Proof. exact (@lem2614170 term48). Qed.
Lemma lem2614173 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614174 : term43 = term243.
Proof. exact (@lem2614173 (NUMERAL 0)). Qed.
Lemma lem2614175 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614176 : term421 = term422.
Proof. exact (MK_COMB (@lem2614175) (@lem2614174)). Qed.
Lemma lem2614177 : term420 = term423.
Proof. exact (MK_COMB (@lem2614176) (@lem2614171)). Qed.
Lemma lem2614178 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2614180 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614181 : term420 = term426.
Proof. exact (@lem2614180 (NUMERAL 0) term48). Qed.
Lemma lem2614182 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614183 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614184 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614183 h1) (fun h1 : term426 = True => @lem2614182)). Qed.
Lemma lem2614185 : term426 = True.
Proof. exact (EQ_MP (@lem2614184) (@lem2614182)). Qed.
Lemma lem2614186 : term420 = True.
Proof. exact (TRANS (@lem2614181) (@lem2614185)). Qed.
Lemma lem2614187 : True = term420.
Proof. exact (SYM (@lem2614186)). Qed.
Lemma lem2614188 : term420.
Proof. exact (EQ_MP (@lem2614187) (@lem0)). Qed.
Lemma lem2614189 : term428.
Proof. exact (@lem2614178 (@lem2614188)). Qed.
Lemma lem2614191 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614192 : term420 = term426.
Proof. exact (@lem2614191 (NUMERAL 0) term48). Qed.
Lemma lem2614193 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614194 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614195 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614194 h1) (fun h1 : term426 = True => @lem2614193)). Qed.
Lemma lem2614196 : term426 = True.
Proof. exact (EQ_MP (@lem2614195) (@lem2614193)). Qed.
Lemma lem2614197 : term420 = True.
Proof. exact (TRANS (@lem2614192) (@lem2614196)). Qed.
Lemma lem2614198 : True = term420.
Proof. exact (SYM (@lem2614197)). Qed.
Lemma lem2614199 : term420.
Proof. exact (EQ_MP (@lem2614198) (@lem0)). Qed.
Lemma lem2614200 : term423 = term429.
Proof. exact (@lem2614189 (@lem2614199)). Qed.
Lemma lem2614202 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614203 : term140 = term141.
Proof. exact (@lem2614202 term48 term48). Qed.
Lemma lem2614204 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614205 : term143 = term48.
Proof. exact (EQ_MP (@lem2614204) (@lem940073)). Qed.
Lemma lem2614206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614207 : term141 = term47.
Proof. exact (MK_COMB (@lem2614206) (@lem2614205)). Qed.
Lemma lem2614208 : term140 = term47.
Proof. exact (TRANS (@lem2614203) (@lem2614207)). Qed.
Lemma lem2614210 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614211 : term431 = term43.
Proof. exact (@lem2614210 term48). Qed.
Lemma lem2614212 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614213 : term432 = term421.
Proof. exact (MK_COMB (@lem2614212) (@lem2614211)). Qed.
Lemma lem2614214 : term429 = term420.
Proof. exact (MK_COMB (@lem2614213) (@lem2614208)). Qed.
Lemma lem2614216 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614217 : term420 = term426.
Proof. exact (@lem2614216 (NUMERAL 0) term48). Qed.
Lemma lem2614218 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614219 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614220 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614219 h1) (fun h1 : term426 = True => @lem2614218)). Qed.
Lemma lem2614221 : term426 = True.
Proof. exact (EQ_MP (@lem2614220) (@lem2614218)). Qed.
Lemma lem2614222 : term420 = True.
Proof. exact (TRANS (@lem2614217) (@lem2614221)). Qed.
Lemma lem2614223 : term429 = True.
Proof. exact (TRANS (@lem2614214) (@lem2614222)). Qed.
Lemma lem2614224 : term423 = True.
Proof. exact (TRANS (@lem2614200) (@lem2614223)). Qed.
Lemma lem2614225 : term420 = True.
Proof. exact (TRANS (@lem2614177) (@lem2614224)). Qed.
Lemma lem2614226 : term419 = True.
Proof. exact (TRANS (@lem2614168) (@lem2614225)). Qed.
Lemma lem2614227 : True = term419.
Proof. exact (SYM (@lem2614226)). Qed.
Lemma lem2614228 : term419.
Proof. exact (EQ_MP (@lem2614227) (@lem0)). Qed.
Lemma lem2614229 (m : int) (n : int) (h1 : term384 m n) : term512 n m.
Proof. exact (conj (@lem2614228) (@lem2614165 m n h1)). Qed.
Lemma lem2614231 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2614232 (n : int) (m : int) : term513 n m.
Proof. exact (@lem2614231 term47 (term261 n m)). Qed.
Lemma lem2614233 (m : int) (n : int) (h1 : term384 m n) : term514 n m.
Proof. exact (@lem2614232 n m (@lem2614229 m n h1)). Qed.
Lemma lem2614234 (n : int) (m : int) : (term515 n m) = (term261 n m).
Proof. exact (@lem1982733 (term261 n m)). Qed.
Lemma lem2614235 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2614236 (n : int) (m : int) : (term516 n m) = (term267 n m).
Proof. exact (MK_COMB (@lem2614235) (@lem2614234 n m)). Qed.
Lemma lem2614237 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2614238 (n : int) (m : int) : (term514 n m) = (term259 n m).
Proof. exact (MK_COMB (@lem2614236 n m) (@lem2614237)). Qed.
Lemma lem2614239 (m : int) (n : int) (h1 : term384 m n) : term259 n m.
Proof. exact (EQ_MP (@lem2614238 n m) (@lem2614233 m n h1)). Qed.
Lemma lem2614241 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2614242 : term419 = term420.
Proof. exact (@lem2614241 term43 term47). Qed.
Lemma lem2614244 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614245 : term47 = term128.
Proof. exact (@lem2614244 term48). Qed.
Lemma lem2614247 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614248 : term43 = term243.
Proof. exact (@lem2614247 (NUMERAL 0)). Qed.
Lemma lem2614249 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614250 : term421 = term422.
Proof. exact (MK_COMB (@lem2614249) (@lem2614248)). Qed.
Lemma lem2614251 : term420 = term423.
Proof. exact (MK_COMB (@lem2614250) (@lem2614245)). Qed.
Lemma lem2614252 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2614254 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614255 : term420 = term426.
Proof. exact (@lem2614254 (NUMERAL 0) term48). Qed.
Lemma lem2614256 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614257 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614258 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614257 h1) (fun h1 : term426 = True => @lem2614256)). Qed.
Lemma lem2614259 : term426 = True.
Proof. exact (EQ_MP (@lem2614258) (@lem2614256)). Qed.
Lemma lem2614260 : term420 = True.
Proof. exact (TRANS (@lem2614255) (@lem2614259)). Qed.
Lemma lem2614261 : True = term420.
Proof. exact (SYM (@lem2614260)). Qed.
Lemma lem2614262 : term420.
Proof. exact (EQ_MP (@lem2614261) (@lem0)). Qed.
Lemma lem2614263 : term428.
Proof. exact (@lem2614252 (@lem2614262)). Qed.
Lemma lem2614265 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614266 : term420 = term426.
Proof. exact (@lem2614265 (NUMERAL 0) term48). Qed.
Lemma lem2614267 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614268 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614269 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614268 h1) (fun h1 : term426 = True => @lem2614267)). Qed.
Lemma lem2614270 : term426 = True.
Proof. exact (EQ_MP (@lem2614269) (@lem2614267)). Qed.
Lemma lem2614271 : term420 = True.
Proof. exact (TRANS (@lem2614266) (@lem2614270)). Qed.
Lemma lem2614272 : True = term420.
Proof. exact (SYM (@lem2614271)). Qed.
Lemma lem2614273 : term420.
Proof. exact (EQ_MP (@lem2614272) (@lem0)). Qed.
Lemma lem2614274 : term423 = term429.
Proof. exact (@lem2614263 (@lem2614273)). Qed.
Lemma lem2614276 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614277 : term140 = term141.
Proof. exact (@lem2614276 term48 term48). Qed.
Lemma lem2614278 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614279 : term143 = term48.
Proof. exact (EQ_MP (@lem2614278) (@lem940073)). Qed.
Lemma lem2614280 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614281 : term141 = term47.
Proof. exact (MK_COMB (@lem2614280) (@lem2614279)). Qed.
Lemma lem2614282 : term140 = term47.
Proof. exact (TRANS (@lem2614277) (@lem2614281)). Qed.
Lemma lem2614284 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614285 : term431 = term43.
Proof. exact (@lem2614284 term48). Qed.
Lemma lem2614286 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614287 : term432 = term421.
Proof. exact (MK_COMB (@lem2614286) (@lem2614285)). Qed.
Lemma lem2614288 : term429 = term420.
Proof. exact (MK_COMB (@lem2614287) (@lem2614282)). Qed.
Lemma lem2614290 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614291 : term420 = term426.
Proof. exact (@lem2614290 (NUMERAL 0) term48). Qed.
Lemma lem2614292 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614293 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614294 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614293 h1) (fun h1 : term426 = True => @lem2614292)). Qed.
Lemma lem2614295 : term426 = True.
Proof. exact (EQ_MP (@lem2614294) (@lem2614292)). Qed.
Lemma lem2614296 : term420 = True.
Proof. exact (TRANS (@lem2614291) (@lem2614295)). Qed.
Lemma lem2614297 : term429 = True.
Proof. exact (TRANS (@lem2614288) (@lem2614296)). Qed.
Lemma lem2614298 : term423 = True.
Proof. exact (TRANS (@lem2614274) (@lem2614297)). Qed.
Lemma lem2614299 : term420 = True.
Proof. exact (TRANS (@lem2614251) (@lem2614298)). Qed.
Lemma lem2614300 : term419 = True.
Proof. exact (TRANS (@lem2614242) (@lem2614299)). Qed.
Lemma lem2614301 : True = term419.
Proof. exact (SYM (@lem2614300)). Qed.
Lemma lem2614302 : term419.
Proof. exact (EQ_MP (@lem2614301) (@lem0)). Qed.
Lemma lem2614303 (m : int) (n : int) (h1 : term384 m n) : term517 n.
Proof. exact (conj (@lem2614302) (@lem2614163 m n h1)). Qed.
Lemma lem2614305 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2614306 (n : int) : term518 n.
Proof. exact (@lem2614305 term47 (term150 n)). Qed.
Lemma lem2614307 (m : int) (n : int) (h1 : term384 m n) : term519 n.
Proof. exact (@lem2614306 n (@lem2614303 m n h1)). Qed.
Lemma lem2614308 (n : int) : (term520 n) = (term150 n).
Proof. exact (@lem1982733 (term150 n)). Qed.
Lemma lem2614309 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2614310 (n : int) : (term521 n) = (term152 n).
Proof. exact (MK_COMB (@lem2614309) (@lem2614308 n)). Qed.
Lemma lem2614311 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2614312 (n : int) : (term519 n) = (term153 n).
Proof. exact (MK_COMB (@lem2614310 n) (@lem2614311)). Qed.
Lemma lem2614313 (m : int) (n : int) (h1 : term384 m n) : term153 n.
Proof. exact (EQ_MP (@lem2614312 n) (@lem2614307 m n h1)). Qed.
Lemma lem2614315 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2614316 : term419 = term420.
Proof. exact (@lem2614315 term43 term47). Qed.
Lemma lem2614318 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614319 : term47 = term128.
Proof. exact (@lem2614318 term48). Qed.
Lemma lem2614321 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614322 : term43 = term243.
Proof. exact (@lem2614321 (NUMERAL 0)). Qed.
Lemma lem2614323 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614324 : term421 = term422.
Proof. exact (MK_COMB (@lem2614323) (@lem2614322)). Qed.
Lemma lem2614325 : term420 = term423.
Proof. exact (MK_COMB (@lem2614324) (@lem2614319)). Qed.
Lemma lem2614326 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2614328 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614329 : term420 = term426.
Proof. exact (@lem2614328 (NUMERAL 0) term48). Qed.
Lemma lem2614330 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614331 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614332 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614331 h1) (fun h1 : term426 = True => @lem2614330)). Qed.
Lemma lem2614333 : term426 = True.
Proof. exact (EQ_MP (@lem2614332) (@lem2614330)). Qed.
Lemma lem2614334 : term420 = True.
Proof. exact (TRANS (@lem2614329) (@lem2614333)). Qed.
Lemma lem2614335 : True = term420.
Proof. exact (SYM (@lem2614334)). Qed.
Lemma lem2614336 : term420.
Proof. exact (EQ_MP (@lem2614335) (@lem0)). Qed.
Lemma lem2614337 : term428.
Proof. exact (@lem2614326 (@lem2614336)). Qed.
Lemma lem2614339 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614340 : term420 = term426.
Proof. exact (@lem2614339 (NUMERAL 0) term48). Qed.
Lemma lem2614341 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614342 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614343 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614342 h1) (fun h1 : term426 = True => @lem2614341)). Qed.
Lemma lem2614344 : term426 = True.
Proof. exact (EQ_MP (@lem2614343) (@lem2614341)). Qed.
Lemma lem2614345 : term420 = True.
Proof. exact (TRANS (@lem2614340) (@lem2614344)). Qed.
Lemma lem2614346 : True = term420.
Proof. exact (SYM (@lem2614345)). Qed.
Lemma lem2614347 : term420.
Proof. exact (EQ_MP (@lem2614346) (@lem0)). Qed.
Lemma lem2614348 : term423 = term429.
Proof. exact (@lem2614337 (@lem2614347)). Qed.
Lemma lem2614350 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614351 : term140 = term141.
Proof. exact (@lem2614350 term48 term48). Qed.
Lemma lem2614352 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614353 : term143 = term48.
Proof. exact (EQ_MP (@lem2614352) (@lem940073)). Qed.
Lemma lem2614354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614355 : term141 = term47.
Proof. exact (MK_COMB (@lem2614354) (@lem2614353)). Qed.
Lemma lem2614356 : term140 = term47.
Proof. exact (TRANS (@lem2614351) (@lem2614355)). Qed.
Lemma lem2614358 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614359 : term431 = term43.
Proof. exact (@lem2614358 term48). Qed.
Lemma lem2614360 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614361 : term432 = term421.
Proof. exact (MK_COMB (@lem2614360) (@lem2614359)). Qed.
Lemma lem2614362 : term429 = term420.
Proof. exact (MK_COMB (@lem2614361) (@lem2614356)). Qed.
Lemma lem2614364 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614365 : term420 = term426.
Proof. exact (@lem2614364 (NUMERAL 0) term48). Qed.
Lemma lem2614366 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614367 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614368 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614367 h1) (fun h1 : term426 = True => @lem2614366)). Qed.
Lemma lem2614369 : term426 = True.
Proof. exact (EQ_MP (@lem2614368) (@lem2614366)). Qed.
Lemma lem2614370 : term420 = True.
Proof. exact (TRANS (@lem2614365) (@lem2614369)). Qed.
Lemma lem2614371 : term429 = True.
Proof. exact (TRANS (@lem2614362) (@lem2614370)). Qed.
Lemma lem2614372 : term423 = True.
Proof. exact (TRANS (@lem2614348) (@lem2614371)). Qed.
Lemma lem2614373 : term420 = True.
Proof. exact (TRANS (@lem2614325) (@lem2614372)). Qed.
Lemma lem2614374 : term419 = True.
Proof. exact (TRANS (@lem2614316) (@lem2614373)). Qed.
Lemma lem2614375 : True = term419.
Proof. exact (SYM (@lem2614374)). Qed.
Lemma lem2614376 : term419.
Proof. exact (EQ_MP (@lem2614375) (@lem0)). Qed.
Lemma lem2614377 (m : int) (n : int) (h1 : term384 m n) : term522 m n.
Proof. exact (conj (@lem2614376) (@lem2614160 m n h1)). Qed.
Lemma lem2614379 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2614380 (m : int) (n : int) : term523 m n.
Proof. exact (@lem2614379 term47 (term391 m n)). Qed.
Lemma lem2614381 (m : int) (n : int) (h1 : term384 m n) : term524 m n.
Proof. exact (@lem2614380 m n (@lem2614377 m n h1)). Qed.
Lemma lem2614382 (m : int) (n : int) : (term525 m n) = (term391 m n).
Proof. exact (@lem1982733 (term391 m n)). Qed.
Lemma lem2614383 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2614384 (m : int) (n : int) : (term526 m n) = (term397 m n).
Proof. exact (MK_COMB (@lem2614383) (@lem2614382 m n)). Qed.
Lemma lem2614385 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2614386 (m : int) (n : int) : (term524 m n) = (term389 m n).
Proof. exact (MK_COMB (@lem2614384 m n) (@lem2614385)). Qed.
Lemma lem2614387 (m : int) (n : int) (h1 : term384 m n) : term389 m n.
Proof. exact (EQ_MP (@lem2614386 m n) (@lem2614381 m n h1)). Qed.
Lemma lem2614388 (m : int) (n : int) (h1 : term384 m n) : term527 m n.
Proof. exact (conj (@lem2614387 m n h1) (@lem2614313 m n h1)). Qed.
Lemma lem2614390 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2614391 (m : int) (n : int) : term528 m n.
Proof. exact (@lem2614390 (term391 m n) (term150 n)). Qed.
Lemma lem2614392 (m : int) (n : int) (h1 : term384 m n) : term529 m n.
Proof. exact (@lem2614391 m n (@lem2614388 m n h1)). Qed.
Lemma lem2614393 (m : int) (n : int) : (term530 m n) = (term531 m n).
Proof. exact (@lem1982755 (term304 m n) (term401 m n) (term150 n)). Qed.
Lemma lem2614394 (m : int) (n : int) : (term532 m n) = (term533 m n).
Proof. exact (@lem1982755 (real_of_int m) (term198 n) (term150 n)). Qed.
Lemma lem2614395 (n : int) : (term534 n) = (term471 n).
Proof. exact (@lem1982763 (term198 n) (real_of_int n) term131). Qed.
Lemma lem2614396 (n : int) : (term472 n) = (term473 n).
Proof. exact (@lem1982713 term131 (real_of_int n)). Qed.
Lemma lem2614398 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614399 : term47 = term128.
Proof. exact (@lem2614398 term48). Qed.
Lemma lem2614401 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2614402 : term131 = term132.
Proof. exact (@lem2614401 term48). Qed.
Lemma lem2614403 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614404 : term452 = term453.
Proof. exact (MK_COMB (@lem2614403) (@lem2614402)). Qed.
Lemma lem2614405 : term454 = term455.
Proof. exact (MK_COMB (@lem2614404) (@lem2614399)). Qed.
Lemma lem2614406 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2614408 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614409 : term420 = term426.
Proof. exact (@lem2614408 (NUMERAL 0) term48). Qed.
Lemma lem2614410 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614411 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614412 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614411 h1) (fun h1 : term426 = True => @lem2614410)). Qed.
Lemma lem2614413 : term426 = True.
Proof. exact (EQ_MP (@lem2614412) (@lem2614410)). Qed.
Lemma lem2614414 : term420 = True.
Proof. exact (TRANS (@lem2614409) (@lem2614413)). Qed.
Lemma lem2614415 : True = term420.
Proof. exact (SYM (@lem2614414)). Qed.
Lemma lem2614416 : term420.
Proof. exact (EQ_MP (@lem2614415) (@lem0)). Qed.
Lemma lem2614417 : term457.
Proof. exact (@lem2614406 (@lem2614416)). Qed.
Lemma lem2614419 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614420 : term420 = term426.
Proof. exact (@lem2614419 (NUMERAL 0) term48). Qed.
Lemma lem2614421 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614422 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614423 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614422 h1) (fun h1 : term426 = True => @lem2614421)). Qed.
Lemma lem2614424 : term426 = True.
Proof. exact (EQ_MP (@lem2614423) (@lem2614421)). Qed.
Lemma lem2614425 : term420 = True.
Proof. exact (TRANS (@lem2614420) (@lem2614424)). Qed.
Lemma lem2614426 : True = term420.
Proof. exact (SYM (@lem2614425)). Qed.
Lemma lem2614427 : term420.
Proof. exact (EQ_MP (@lem2614426) (@lem0)). Qed.
Lemma lem2614428 : term458.
Proof. exact (@lem2614417 (@lem2614427)). Qed.
Lemma lem2614430 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614431 : term420 = term426.
Proof. exact (@lem2614430 (NUMERAL 0) term48). Qed.
Lemma lem2614432 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614433 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614434 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614433 h1) (fun h1 : term426 = True => @lem2614432)). Qed.
Lemma lem2614435 : term426 = True.
Proof. exact (EQ_MP (@lem2614434) (@lem2614432)). Qed.
Lemma lem2614436 : term420 = True.
Proof. exact (TRANS (@lem2614431) (@lem2614435)). Qed.
Lemma lem2614437 : True = term420.
Proof. exact (SYM (@lem2614436)). Qed.
Lemma lem2614438 : term420.
Proof. exact (EQ_MP (@lem2614437) (@lem0)). Qed.
Lemma lem2614439 : term459.
Proof. exact (@lem2614428 (@lem2614438)). Qed.
Lemma lem2614441 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614442 : term140 = term141.
Proof. exact (@lem2614441 term48 term48). Qed.
Lemma lem2614443 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614444 : term143 = term48.
Proof. exact (EQ_MP (@lem2614443) (@lem940073)). Qed.
Lemma lem2614445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614446 : term141 = term47.
Proof. exact (MK_COMB (@lem2614445) (@lem2614444)). Qed.
Lemma lem2614447 : term140 = term47.
Proof. exact (TRANS (@lem2614442) (@lem2614446)). Qed.
Lemma lem2614449 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2614450 : term135 = term146.
Proof. exact (@lem2614449 term48 term48). Qed.
Lemma lem2614451 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614452 : term143 = term48.
Proof. exact (EQ_MP (@lem2614451) (@lem940073)). Qed.
Lemma lem2614453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614454 : term141 = term47.
Proof. exact (MK_COMB (@lem2614453) (@lem2614452)). Qed.
Lemma lem2614455 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2614456 : term146 = term131.
Proof. exact (MK_COMB (@lem2614455) (@lem2614454)). Qed.
Lemma lem2614457 : term135 = term131.
Proof. exact (TRANS (@lem2614450) (@lem2614456)). Qed.
Lemma lem2614458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614459 : term460 = term452.
Proof. exact (MK_COMB (@lem2614458) (@lem2614457)). Qed.
Lemma lem2614460 : term461 = term454.
Proof. exact (MK_COMB (@lem2614459) (@lem2614447)). Qed.
Lemma lem2614462 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2614463 : term454 = term43.
Proof. exact (@lem2614462 term48). Qed.
Lemma lem2614464 : term461 = term43.
Proof. exact (TRANS (@lem2614460) (@lem2614463)). Qed.
Lemma lem2614465 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2614466 : term463 = term464.
Proof. exact (MK_COMB (@lem2614465) (@lem2614464)). Qed.
Lemma lem2614467 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2614468 : term465 = term431.
Proof. exact (MK_COMB (@lem2614466) (@lem2614467)). Qed.
Lemma lem2614470 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614471 : term431 = term43.
Proof. exact (@lem2614470 term48). Qed.
Lemma lem2614472 : term465 = term43.
Proof. exact (TRANS (@lem2614468) (@lem2614471)). Qed.
Lemma lem2614474 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614475 : term140 = term141.
Proof. exact (@lem2614474 term48 term48). Qed.
Lemma lem2614476 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614477 : term143 = term48.
Proof. exact (EQ_MP (@lem2614476) (@lem940073)). Qed.
Lemma lem2614478 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614479 : term141 = term47.
Proof. exact (MK_COMB (@lem2614478) (@lem2614477)). Qed.
Lemma lem2614480 : term140 = term47.
Proof. exact (TRANS (@lem2614475) (@lem2614479)). Qed.
Lemma lem2614481 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2614482 : term466 = term431.
Proof. exact (MK_COMB (@lem2614481) (@lem2614480)). Qed.
Lemma lem2614484 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614485 : term431 = term43.
Proof. exact (@lem2614484 term48). Qed.
Lemma lem2614486 : term466 = term43.
Proof. exact (TRANS (@lem2614482) (@lem2614485)). Qed.
Lemma lem2614487 : term43 = term466.
Proof. exact (SYM (@lem2614486)). Qed.
Lemma lem2614488 : term465 = term466.
Proof. exact (TRANS (@lem2614472) (@lem2614487)). Qed.
Lemma lem2614489 : term455 = term243.
Proof. exact (@lem2614439 (@lem2614488)). Qed.
Lemma lem2614490 : term454 = term243.
Proof. exact (TRANS (@lem2614405) (@lem2614489)). Qed.
Lemma lem2614492 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2614493 : term243 = term43.
Proof. exact (@lem2614492 term43). Qed.
Lemma lem2614494 : term454 = term43.
Proof. exact (TRANS (@lem2614490) (@lem2614493)). Qed.
Lemma lem2614495 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2614496 : term467 = term464.
Proof. exact (MK_COMB (@lem2614495) (@lem2614494)). Qed.
Lemma lem2614497 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2614498 (n : int) : (term473 n) = (term474 n).
Proof. exact (MK_COMB (@lem2614496) (@lem2614497 n)). Qed.
Lemma lem2614499 (n : int) : (term472 n) = (term474 n).
Proof. exact (TRANS (@lem2614396 n) (@lem2614498 n)). Qed.
Lemma lem2614500 (n : int) : (term474 n) = term43.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2614501 (n : int) : (term472 n) = term43.
Proof. exact (TRANS (@lem2614499 n) (@lem2614500 n)). Qed.
Lemma lem2614502 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614503 (n : int) : (term475 n) = term45.
Proof. exact (MK_COMB (@lem2614502) (@lem2614501 n)). Qed.
Lemma lem2614504 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2614505 (n : int) : (term471 n) = term476.
Proof. exact (MK_COMB (@lem2614503 n) (@lem2614504)). Qed.
Lemma lem2614506 (n : int) : (term534 n) = term476.
Proof. exact (TRANS (@lem2614395 n) (@lem2614505 n)). Qed.
Lemma lem2614507 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2614508 (n : int) : (term534 n) = term131.
Proof. exact (TRANS (@lem2614506 n) (@lem2614507)). Qed.
Lemma lem2614509 (m : int) : (term83 m) = (term83 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem2614510 (n : int) (m : int) : (term533 m n) = (term150 m).
Proof. exact (MK_COMB (@lem2614509 m) (@lem2614508 n)). Qed.
Lemma lem2614511 (n : int) (m : int) : (term532 m n) = (term150 m).
Proof. exact (TRANS (@lem2614394 m n) (@lem2614510 n m)). Qed.
Lemma lem2614512 (m : int) (n : int) : (term306 m n) = (term306 m n).
Proof. exact (eq_refl (term306 m n)). Qed.
Lemma lem2614513 (n : int) (m : int) : (term531 m n) = (term535 n m).
Proof. exact (MK_COMB (@lem2614512 m n) (@lem2614511 n m)). Qed.
Lemma lem2614514 (n : int) (m : int) : (term530 m n) = (term535 n m).
Proof. exact (TRANS (@lem2614393 m n) (@lem2614513 n m)). Qed.
Lemma lem2614515 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2614516 (n : int) (m : int) : (term536 m n) = (term537 n m).
Proof. exact (MK_COMB (@lem2614515) (@lem2614514 n m)). Qed.
Lemma lem2614517 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2614518 (n : int) (m : int) : (term529 m n) = (term538 n m).
Proof. exact (MK_COMB (@lem2614516 n m) (@lem2614517)). Qed.
Lemma lem2614519 (m : int) (n : int) (h1 : term384 m n) : term538 n m.
Proof. exact (EQ_MP (@lem2614518 n m) (@lem2614392 m n h1)). Qed.
Lemma lem2614521 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2614522 : term419 = term420.
Proof. exact (@lem2614521 term43 term47). Qed.
Lemma lem2614524 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614525 : term47 = term128.
Proof. exact (@lem2614524 term48). Qed.
Lemma lem2614527 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614528 : term43 = term243.
Proof. exact (@lem2614527 (NUMERAL 0)). Qed.
Lemma lem2614529 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614530 : term421 = term422.
Proof. exact (MK_COMB (@lem2614529) (@lem2614528)). Qed.
Lemma lem2614531 : term420 = term423.
Proof. exact (MK_COMB (@lem2614530) (@lem2614525)). Qed.
Lemma lem2614532 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2614534 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614535 : term420 = term426.
Proof. exact (@lem2614534 (NUMERAL 0) term48). Qed.
Lemma lem2614536 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614537 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614538 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614537 h1) (fun h1 : term426 = True => @lem2614536)). Qed.
Lemma lem2614539 : term426 = True.
Proof. exact (EQ_MP (@lem2614538) (@lem2614536)). Qed.
Lemma lem2614540 : term420 = True.
Proof. exact (TRANS (@lem2614535) (@lem2614539)). Qed.
Lemma lem2614541 : True = term420.
Proof. exact (SYM (@lem2614540)). Qed.
Lemma lem2614542 : term420.
Proof. exact (EQ_MP (@lem2614541) (@lem0)). Qed.
Lemma lem2614543 : term428.
Proof. exact (@lem2614532 (@lem2614542)). Qed.
Lemma lem2614545 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614546 : term420 = term426.
Proof. exact (@lem2614545 (NUMERAL 0) term48). Qed.
Lemma lem2614547 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614548 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614549 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614548 h1) (fun h1 : term426 = True => @lem2614547)). Qed.
Lemma lem2614550 : term426 = True.
Proof. exact (EQ_MP (@lem2614549) (@lem2614547)). Qed.
Lemma lem2614551 : term420 = True.
Proof. exact (TRANS (@lem2614546) (@lem2614550)). Qed.
Lemma lem2614552 : True = term420.
Proof. exact (SYM (@lem2614551)). Qed.
Lemma lem2614553 : term420.
Proof. exact (EQ_MP (@lem2614552) (@lem0)). Qed.
Lemma lem2614554 : term423 = term429.
Proof. exact (@lem2614543 (@lem2614553)). Qed.
Lemma lem2614556 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614557 : term140 = term141.
Proof. exact (@lem2614556 term48 term48). Qed.
Lemma lem2614558 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614559 : term143 = term48.
Proof. exact (EQ_MP (@lem2614558) (@lem940073)). Qed.
Lemma lem2614560 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614561 : term141 = term47.
Proof. exact (MK_COMB (@lem2614560) (@lem2614559)). Qed.
Lemma lem2614562 : term140 = term47.
Proof. exact (TRANS (@lem2614557) (@lem2614561)). Qed.
Lemma lem2614564 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614565 : term431 = term43.
Proof. exact (@lem2614564 term48). Qed.
Lemma lem2614566 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614567 : term432 = term421.
Proof. exact (MK_COMB (@lem2614566) (@lem2614565)). Qed.
Lemma lem2614568 : term429 = term420.
Proof. exact (MK_COMB (@lem2614567) (@lem2614562)). Qed.
Lemma lem2614570 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614571 : term420 = term426.
Proof. exact (@lem2614570 (NUMERAL 0) term48). Qed.
Lemma lem2614572 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614573 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614574 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614573 h1) (fun h1 : term426 = True => @lem2614572)). Qed.
Lemma lem2614575 : term426 = True.
Proof. exact (EQ_MP (@lem2614574) (@lem2614572)). Qed.
Lemma lem2614576 : term420 = True.
Proof. exact (TRANS (@lem2614571) (@lem2614575)). Qed.
Lemma lem2614577 : term429 = True.
Proof. exact (TRANS (@lem2614568) (@lem2614576)). Qed.
Lemma lem2614578 : term423 = True.
Proof. exact (TRANS (@lem2614554) (@lem2614577)). Qed.
Lemma lem2614579 : term420 = True.
Proof. exact (TRANS (@lem2614531) (@lem2614578)). Qed.
Lemma lem2614580 : term419 = True.
Proof. exact (TRANS (@lem2614522) (@lem2614579)). Qed.
Lemma lem2614581 : True = term419.
Proof. exact (SYM (@lem2614580)). Qed.
Lemma lem2614582 : term419.
Proof. exact (EQ_MP (@lem2614581) (@lem0)). Qed.
Lemma lem2614583 (m : int) (n : int) (h1 : term384 m n) : term539 n m.
Proof. exact (conj (@lem2614582) (@lem2614519 m n h1)). Qed.
Lemma lem2614585 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2614586 (n : int) (m : int) : term540 n m.
Proof. exact (@lem2614585 term47 (term535 n m)). Qed.
Lemma lem2614587 (m : int) (n : int) (h1 : term384 m n) : term541 n m.
Proof. exact (@lem2614586 n m (@lem2614583 m n h1)). Qed.
Lemma lem2614588 (n : int) (m : int) : (term542 n m) = (term535 n m).
Proof. exact (@lem1982733 (term535 n m)). Qed.
Lemma lem2614589 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2614590 (n : int) (m : int) : (term543 n m) = (term537 n m).
Proof. exact (MK_COMB (@lem2614589) (@lem2614588 n m)). Qed.
Lemma lem2614591 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2614592 (n : int) (m : int) : (term541 n m) = (term538 n m).
Proof. exact (MK_COMB (@lem2614590 n m) (@lem2614591)). Qed.
Lemma lem2614593 (m : int) (n : int) (h1 : term384 m n) : term538 n m.
Proof. exact (EQ_MP (@lem2614592 n m) (@lem2614587 m n h1)). Qed.
Lemma lem2614594 (m : int) (n : int) (h1 : term384 m n) : term544 n m.
Proof. exact (conj (@lem2614593 m n h1) (@lem2614239 m n h1)). Qed.
Lemma lem2614596 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2614597 (n : int) (m : int) : term545 n m.
Proof. exact (@lem2614596 (term535 n m) (term261 n m)). Qed.
Lemma lem2614598 (m : int) (n : int) (h1 : term384 m n) : term546 n m.
Proof. exact (@lem2614597 n m (@lem2614594 m n h1)). Qed.
Lemma lem2614599 (n : int) (m : int) : (term547 n m) = (term548 n m).
Proof. exact (@lem1982753 (term304 m n) (term58 m n) (term150 m) (term198 m)). Qed.
Lemma lem2614600 (m : int) (n : int) : (term450 m n) = (term451 m n).
Proof. exact (@lem1982713 term131 (term58 m n)). Qed.
Lemma lem2614602 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614603 : term47 = term128.
Proof. exact (@lem2614602 term48). Qed.
Lemma lem2614605 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2614606 : term131 = term132.
Proof. exact (@lem2614605 term48). Qed.
Lemma lem2614607 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614608 : term452 = term453.
Proof. exact (MK_COMB (@lem2614607) (@lem2614606)). Qed.
Lemma lem2614609 : term454 = term455.
Proof. exact (MK_COMB (@lem2614608) (@lem2614603)). Qed.
Lemma lem2614610 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2614612 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614613 : term420 = term426.
Proof. exact (@lem2614612 (NUMERAL 0) term48). Qed.
Lemma lem2614614 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614615 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614616 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614615 h1) (fun h1 : term426 = True => @lem2614614)). Qed.
Lemma lem2614617 : term426 = True.
Proof. exact (EQ_MP (@lem2614616) (@lem2614614)). Qed.
Lemma lem2614618 : term420 = True.
Proof. exact (TRANS (@lem2614613) (@lem2614617)). Qed.
Lemma lem2614619 : True = term420.
Proof. exact (SYM (@lem2614618)). Qed.
Lemma lem2614620 : term420.
Proof. exact (EQ_MP (@lem2614619) (@lem0)). Qed.
Lemma lem2614621 : term457.
Proof. exact (@lem2614610 (@lem2614620)). Qed.
Lemma lem2614623 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614624 : term420 = term426.
Proof. exact (@lem2614623 (NUMERAL 0) term48). Qed.
Lemma lem2614625 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614626 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614627 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614626 h1) (fun h1 : term426 = True => @lem2614625)). Qed.
Lemma lem2614628 : term426 = True.
Proof. exact (EQ_MP (@lem2614627) (@lem2614625)). Qed.
Lemma lem2614629 : term420 = True.
Proof. exact (TRANS (@lem2614624) (@lem2614628)). Qed.
Lemma lem2614630 : True = term420.
Proof. exact (SYM (@lem2614629)). Qed.
Lemma lem2614631 : term420.
Proof. exact (EQ_MP (@lem2614630) (@lem0)). Qed.
Lemma lem2614632 : term458.
Proof. exact (@lem2614621 (@lem2614631)). Qed.
Lemma lem2614634 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614635 : term420 = term426.
Proof. exact (@lem2614634 (NUMERAL 0) term48). Qed.
Lemma lem2614636 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614637 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614638 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614637 h1) (fun h1 : term426 = True => @lem2614636)). Qed.
Lemma lem2614639 : term426 = True.
Proof. exact (EQ_MP (@lem2614638) (@lem2614636)). Qed.
Lemma lem2614640 : term420 = True.
Proof. exact (TRANS (@lem2614635) (@lem2614639)). Qed.
Lemma lem2614641 : True = term420.
Proof. exact (SYM (@lem2614640)). Qed.
Lemma lem2614642 : term420.
Proof. exact (EQ_MP (@lem2614641) (@lem0)). Qed.
Lemma lem2614643 : term459.
Proof. exact (@lem2614632 (@lem2614642)). Qed.
Lemma lem2614645 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614646 : term140 = term141.
Proof. exact (@lem2614645 term48 term48). Qed.
Lemma lem2614647 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614648 : term143 = term48.
Proof. exact (EQ_MP (@lem2614647) (@lem940073)). Qed.
Lemma lem2614649 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614650 : term141 = term47.
Proof. exact (MK_COMB (@lem2614649) (@lem2614648)). Qed.
Lemma lem2614651 : term140 = term47.
Proof. exact (TRANS (@lem2614646) (@lem2614650)). Qed.
Lemma lem2614653 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2614654 : term135 = term146.
Proof. exact (@lem2614653 term48 term48). Qed.
Lemma lem2614655 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614656 : term143 = term48.
Proof. exact (EQ_MP (@lem2614655) (@lem940073)). Qed.
Lemma lem2614657 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614658 : term141 = term47.
Proof. exact (MK_COMB (@lem2614657) (@lem2614656)). Qed.
Lemma lem2614659 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2614660 : term146 = term131.
Proof. exact (MK_COMB (@lem2614659) (@lem2614658)). Qed.
Lemma lem2614661 : term135 = term131.
Proof. exact (TRANS (@lem2614654) (@lem2614660)). Qed.
Lemma lem2614662 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614663 : term460 = term452.
Proof. exact (MK_COMB (@lem2614662) (@lem2614661)). Qed.
Lemma lem2614664 : term461 = term454.
Proof. exact (MK_COMB (@lem2614663) (@lem2614651)). Qed.
Lemma lem2614666 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2614667 : term454 = term43.
Proof. exact (@lem2614666 term48). Qed.
Lemma lem2614668 : term461 = term43.
Proof. exact (TRANS (@lem2614664) (@lem2614667)). Qed.
Lemma lem2614669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2614670 : term463 = term464.
Proof. exact (MK_COMB (@lem2614669) (@lem2614668)). Qed.
Lemma lem2614671 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2614672 : term465 = term431.
Proof. exact (MK_COMB (@lem2614670) (@lem2614671)). Qed.
Lemma lem2614674 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614675 : term431 = term43.
Proof. exact (@lem2614674 term48). Qed.
Lemma lem2614676 : term465 = term43.
Proof. exact (TRANS (@lem2614672) (@lem2614675)). Qed.
Lemma lem2614678 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614679 : term140 = term141.
Proof. exact (@lem2614678 term48 term48). Qed.
Lemma lem2614680 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614681 : term143 = term48.
Proof. exact (EQ_MP (@lem2614680) (@lem940073)). Qed.
Lemma lem2614682 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614683 : term141 = term47.
Proof. exact (MK_COMB (@lem2614682) (@lem2614681)). Qed.
Lemma lem2614684 : term140 = term47.
Proof. exact (TRANS (@lem2614679) (@lem2614683)). Qed.
Lemma lem2614685 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2614686 : term466 = term431.
Proof. exact (MK_COMB (@lem2614685) (@lem2614684)). Qed.
Lemma lem2614688 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614689 : term431 = term43.
Proof. exact (@lem2614688 term48). Qed.
Lemma lem2614690 : term466 = term43.
Proof. exact (TRANS (@lem2614686) (@lem2614689)). Qed.
Lemma lem2614691 : term43 = term466.
Proof. exact (SYM (@lem2614690)). Qed.
Lemma lem2614692 : term465 = term466.
Proof. exact (TRANS (@lem2614676) (@lem2614691)). Qed.
Lemma lem2614693 : term455 = term243.
Proof. exact (@lem2614643 (@lem2614692)). Qed.
Lemma lem2614694 : term454 = term243.
Proof. exact (TRANS (@lem2614609) (@lem2614693)). Qed.
Lemma lem2614696 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2614697 : term243 = term43.
Proof. exact (@lem2614696 term43). Qed.
Lemma lem2614698 : term454 = term43.
Proof. exact (TRANS (@lem2614694) (@lem2614697)). Qed.
Lemma lem2614699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2614700 : term467 = term464.
Proof. exact (MK_COMB (@lem2614699) (@lem2614698)). Qed.
Lemma lem2614701 (m : int) (n : int) : (term58 m n) = (term58 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem2614702 (m : int) (n : int) : (term451 m n) = (term468 m n).
Proof. exact (MK_COMB (@lem2614700) (@lem2614701 m n)). Qed.
Lemma lem2614703 (m : int) (n : int) : (term450 m n) = (term468 m n).
Proof. exact (TRANS (@lem2614600 m n) (@lem2614702 m n)). Qed.
Lemma lem2614704 (m : int) (n : int) : (term468 m n) = term43.
Proof. exact (@lem1982719 (term58 m n)). Qed.
Lemma lem2614705 (m : int) (n : int) : (term450 m n) = term43.
Proof. exact (TRANS (@lem2614703 m n) (@lem2614704 m n)). Qed.
Lemma lem2614706 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614707 (m : int) (n : int) : (term469 m n) = term45.
Proof. exact (MK_COMB (@lem2614706) (@lem2614705 m n)). Qed.
Lemma lem2614708 (m : int) : (term549 m) = (term508 m).
Proof. exact (@lem1982759 (real_of_int m) (term198 m) term131). Qed.
Lemma lem2614709 (m : int) : (term509 m) = (term473 m).
Proof. exact (@lem1982715 term131 (real_of_int m)). Qed.
Lemma lem2614711 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614712 : term47 = term128.
Proof. exact (@lem2614711 term48). Qed.
Lemma lem2614714 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2614715 : term131 = term132.
Proof. exact (@lem2614714 term48). Qed.
Lemma lem2614716 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614717 : term452 = term453.
Proof. exact (MK_COMB (@lem2614716) (@lem2614715)). Qed.
Lemma lem2614718 : term454 = term455.
Proof. exact (MK_COMB (@lem2614717) (@lem2614712)). Qed.
Lemma lem2614719 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2614721 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614722 : term420 = term426.
Proof. exact (@lem2614721 (NUMERAL 0) term48). Qed.
Lemma lem2614723 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614724 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614725 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614724 h1) (fun h1 : term426 = True => @lem2614723)). Qed.
Lemma lem2614726 : term426 = True.
Proof. exact (EQ_MP (@lem2614725) (@lem2614723)). Qed.
Lemma lem2614727 : term420 = True.
Proof. exact (TRANS (@lem2614722) (@lem2614726)). Qed.
Lemma lem2614728 : True = term420.
Proof. exact (SYM (@lem2614727)). Qed.
Lemma lem2614729 : term420.
Proof. exact (EQ_MP (@lem2614728) (@lem0)). Qed.
Lemma lem2614730 : term457.
Proof. exact (@lem2614719 (@lem2614729)). Qed.
Lemma lem2614732 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614733 : term420 = term426.
Proof. exact (@lem2614732 (NUMERAL 0) term48). Qed.
Lemma lem2614734 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614735 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614736 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614735 h1) (fun h1 : term426 = True => @lem2614734)). Qed.
Lemma lem2614737 : term426 = True.
Proof. exact (EQ_MP (@lem2614736) (@lem2614734)). Qed.
Lemma lem2614738 : term420 = True.
Proof. exact (TRANS (@lem2614733) (@lem2614737)). Qed.
Lemma lem2614739 : True = term420.
Proof. exact (SYM (@lem2614738)). Qed.
Lemma lem2614740 : term420.
Proof. exact (EQ_MP (@lem2614739) (@lem0)). Qed.
Lemma lem2614741 : term458.
Proof. exact (@lem2614730 (@lem2614740)). Qed.
Lemma lem2614743 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614744 : term420 = term426.
Proof. exact (@lem2614743 (NUMERAL 0) term48). Qed.
Lemma lem2614745 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614746 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614747 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614746 h1) (fun h1 : term426 = True => @lem2614745)). Qed.
Lemma lem2614748 : term426 = True.
Proof. exact (EQ_MP (@lem2614747) (@lem2614745)). Qed.
Lemma lem2614749 : term420 = True.
Proof. exact (TRANS (@lem2614744) (@lem2614748)). Qed.
Lemma lem2614750 : True = term420.
Proof. exact (SYM (@lem2614749)). Qed.
Lemma lem2614751 : term420.
Proof. exact (EQ_MP (@lem2614750) (@lem0)). Qed.
Lemma lem2614752 : term459.
Proof. exact (@lem2614741 (@lem2614751)). Qed.
Lemma lem2614754 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614755 : term140 = term141.
Proof. exact (@lem2614754 term48 term48). Qed.
Lemma lem2614756 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614757 : term143 = term48.
Proof. exact (EQ_MP (@lem2614756) (@lem940073)). Qed.
Lemma lem2614758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614759 : term141 = term47.
Proof. exact (MK_COMB (@lem2614758) (@lem2614757)). Qed.
Lemma lem2614760 : term140 = term47.
Proof. exact (TRANS (@lem2614755) (@lem2614759)). Qed.
Lemma lem2614762 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2614763 : term135 = term146.
Proof. exact (@lem2614762 term48 term48). Qed.
Lemma lem2614764 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614765 : term143 = term48.
Proof. exact (EQ_MP (@lem2614764) (@lem940073)). Qed.
Lemma lem2614766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614767 : term141 = term47.
Proof. exact (MK_COMB (@lem2614766) (@lem2614765)). Qed.
Lemma lem2614768 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2614769 : term146 = term131.
Proof. exact (MK_COMB (@lem2614768) (@lem2614767)). Qed.
Lemma lem2614770 : term135 = term131.
Proof. exact (TRANS (@lem2614763) (@lem2614769)). Qed.
Lemma lem2614771 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614772 : term460 = term452.
Proof. exact (MK_COMB (@lem2614771) (@lem2614770)). Qed.
Lemma lem2614773 : term461 = term454.
Proof. exact (MK_COMB (@lem2614772) (@lem2614760)). Qed.
Lemma lem2614775 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2614776 : term454 = term43.
Proof. exact (@lem2614775 term48). Qed.
Lemma lem2614777 : term461 = term43.
Proof. exact (TRANS (@lem2614773) (@lem2614776)). Qed.
Lemma lem2614778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2614779 : term463 = term464.
Proof. exact (MK_COMB (@lem2614778) (@lem2614777)). Qed.
Lemma lem2614780 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2614781 : term465 = term431.
Proof. exact (MK_COMB (@lem2614779) (@lem2614780)). Qed.
Lemma lem2614783 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614784 : term431 = term43.
Proof. exact (@lem2614783 term48). Qed.
Lemma lem2614785 : term465 = term43.
Proof. exact (TRANS (@lem2614781) (@lem2614784)). Qed.
Lemma lem2614787 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614788 : term140 = term141.
Proof. exact (@lem2614787 term48 term48). Qed.
Lemma lem2614789 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614790 : term143 = term48.
Proof. exact (EQ_MP (@lem2614789) (@lem940073)). Qed.
Lemma lem2614791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614792 : term141 = term47.
Proof. exact (MK_COMB (@lem2614791) (@lem2614790)). Qed.
Lemma lem2614793 : term140 = term47.
Proof. exact (TRANS (@lem2614788) (@lem2614792)). Qed.
Lemma lem2614794 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2614795 : term466 = term431.
Proof. exact (MK_COMB (@lem2614794) (@lem2614793)). Qed.
Lemma lem2614797 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614798 : term431 = term43.
Proof. exact (@lem2614797 term48). Qed.
Lemma lem2614799 : term466 = term43.
Proof. exact (TRANS (@lem2614795) (@lem2614798)). Qed.
Lemma lem2614800 : term43 = term466.
Proof. exact (SYM (@lem2614799)). Qed.
Lemma lem2614801 : term465 = term466.
Proof. exact (TRANS (@lem2614785) (@lem2614800)). Qed.
Lemma lem2614802 : term455 = term243.
Proof. exact (@lem2614752 (@lem2614801)). Qed.
Lemma lem2614803 : term454 = term243.
Proof. exact (TRANS (@lem2614718) (@lem2614802)). Qed.
Lemma lem2614805 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2614806 : term243 = term43.
Proof. exact (@lem2614805 term43). Qed.
Lemma lem2614807 : term454 = term43.
Proof. exact (TRANS (@lem2614803) (@lem2614806)). Qed.
Lemma lem2614808 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2614809 : term467 = term464.
Proof. exact (MK_COMB (@lem2614808) (@lem2614807)). Qed.
Lemma lem2614810 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2614811 (m : int) : (term473 m) = (term474 m).
Proof. exact (MK_COMB (@lem2614809) (@lem2614810 m)). Qed.
Lemma lem2614812 (m : int) : (term509 m) = (term474 m).
Proof. exact (TRANS (@lem2614709 m) (@lem2614811 m)). Qed.
Lemma lem2614813 (m : int) : (term474 m) = term43.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2614814 (m : int) : (term509 m) = term43.
Proof. exact (TRANS (@lem2614812 m) (@lem2614813 m)). Qed.
Lemma lem2614815 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2614816 (m : int) : (term510 m) = term45.
Proof. exact (MK_COMB (@lem2614815) (@lem2614814 m)). Qed.
Lemma lem2614817 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2614818 (m : int) : (term508 m) = term476.
Proof. exact (MK_COMB (@lem2614816 m) (@lem2614817)). Qed.
Lemma lem2614819 (m : int) : (term549 m) = term476.
Proof. exact (TRANS (@lem2614708 m) (@lem2614818 m)). Qed.
Lemma lem2614820 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2614821 (m : int) : (term549 m) = term131.
Proof. exact (TRANS (@lem2614819 m) (@lem2614820)). Qed.
Lemma lem2614822 (n : int) (m : int) : (term548 n m) = term476.
Proof. exact (MK_COMB (@lem2614707 m n) (@lem2614821 m)). Qed.
Lemma lem2614823 (n : int) (m : int) : (term547 n m) = term476.
Proof. exact (TRANS (@lem2614599 n m) (@lem2614822 n m)). Qed.
Lemma lem2614824 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2614825 (n : int) (m : int) : (term547 n m) = term131.
Proof. exact (TRANS (@lem2614823 n m) (@lem2614824)). Qed.
Lemma lem2614826 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2614827 (n : int) (m : int) : (term550 n m) = term478.
Proof. exact (MK_COMB (@lem2614826) (@lem2614825 n m)). Qed.
Lemma lem2614828 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2614829 (n : int) (m : int) : (term546 n m) = term479.
Proof. exact (MK_COMB (@lem2614827 n m) (@lem2614828)). Qed.
Lemma lem2614830 (m : int) (n : int) (h1 : term384 m n) : term479.
Proof. exact (EQ_MP (@lem2614829 n m) (@lem2614598 m n h1)). Qed.
Lemma lem2614832 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2614833 : term479 = term480.
Proof. exact (@lem2614832 term43 term131). Qed.
Lemma lem2614835 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2614836 : term131 = term132.
Proof. exact (@lem2614835 term48). Qed.
Lemma lem2614838 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614839 : term43 = term243.
Proof. exact (@lem2614838 (NUMERAL 0)). Qed.
Lemma lem2614840 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2614841 : term481 = term482.
Proof. exact (MK_COMB (@lem2614840) (@lem2614839)). Qed.
Lemma lem2614842 : term480 = term483.
Proof. exact (MK_COMB (@lem2614841) (@lem2614836)). Qed.
Lemma lem2614843 : term484.
Proof. exact (@lem1980026 term43 term47 term131 term47). Qed.
Lemma lem2614845 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614846 : term420 = term426.
Proof. exact (@lem2614845 (NUMERAL 0) term48). Qed.
Lemma lem2614847 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614848 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614849 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614848 h1) (fun h1 : term426 = True => @lem2614847)). Qed.
Lemma lem2614850 : term426 = True.
Proof. exact (EQ_MP (@lem2614849) (@lem2614847)). Qed.
Lemma lem2614851 : term420 = True.
Proof. exact (TRANS (@lem2614846) (@lem2614850)). Qed.
Lemma lem2614852 : True = term420.
Proof. exact (SYM (@lem2614851)). Qed.
Lemma lem2614853 : term420.
Proof. exact (EQ_MP (@lem2614852) (@lem0)). Qed.
Lemma lem2614854 : term485.
Proof. exact (@lem2614843 (@lem2614853)). Qed.
Lemma lem2614856 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614857 : term420 = term426.
Proof. exact (@lem2614856 (NUMERAL 0) term48). Qed.
Lemma lem2614858 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614859 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614860 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614859 h1) (fun h1 : term426 = True => @lem2614858)). Qed.
Lemma lem2614861 : term426 = True.
Proof. exact (EQ_MP (@lem2614860) (@lem2614858)). Qed.
Lemma lem2614862 : term420 = True.
Proof. exact (TRANS (@lem2614857) (@lem2614861)). Qed.
Lemma lem2614863 : True = term420.
Proof. exact (SYM (@lem2614862)). Qed.
Lemma lem2614864 : term420.
Proof. exact (EQ_MP (@lem2614863) (@lem0)). Qed.
Lemma lem2614865 : term483 = term486.
Proof. exact (@lem2614854 (@lem2614864)). Qed.
Lemma lem2614867 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2614868 : term135 = term146.
Proof. exact (@lem2614867 term48 term48). Qed.
Lemma lem2614869 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614870 : term143 = term48.
Proof. exact (EQ_MP (@lem2614869) (@lem940073)). Qed.
Lemma lem2614871 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614872 : term141 = term47.
Proof. exact (MK_COMB (@lem2614871) (@lem2614870)). Qed.
Lemma lem2614873 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2614874 : term146 = term131.
Proof. exact (MK_COMB (@lem2614873) (@lem2614872)). Qed.
Lemma lem2614875 : term135 = term131.
Proof. exact (TRANS (@lem2614868) (@lem2614874)). Qed.
Lemma lem2614877 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614878 : term431 = term43.
Proof. exact (@lem2614877 term48). Qed.
Lemma lem2614879 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2614880 : term487 = term481.
Proof. exact (MK_COMB (@lem2614879) (@lem2614878)). Qed.
Lemma lem2614881 : term486 = term480.
Proof. exact (MK_COMB (@lem2614880) (@lem2614875)). Qed.
Lemma lem2614883 (m : nat) (n : nat) : (term488 m n) = (term489 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2614884 : term480 = term490.
Proof. exact (@lem2614883 (NUMERAL 0) term48). Qed.
Lemma lem2614885 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614886 (h1 : term427 = (BIT1 0)) : (term48 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2614887 : (term427 = (BIT1 0)) = ((term48 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614886 h1) (fun h1 : (term48 = (NUMERAL 0)) = False => @lem2614885)). Qed.
Lemma lem2614888 : (term48 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2614887) (@lem2614885)). Qed.
Lemma lem2614889 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2614890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2614891 : term491 = (and True).
Proof. exact (MK_COMB (@lem2614890) (@lem2614889)). Qed.
Lemma lem2614892 : term490 = (True /\ False).
Proof. exact (MK_COMB (@lem2614891) (@lem2614888)). Qed.
Lemma lem2614894 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2614895 : term490 = False.
Proof. exact (TRANS (@lem2614892) (@lem2614894)). Qed.
Lemma lem2614896 : term480 = False.
Proof. exact (TRANS (@lem2614884) (@lem2614895)). Qed.
Lemma lem2614897 : term486 = False.
Proof. exact (TRANS (@lem2614881) (@lem2614896)). Qed.
Lemma lem2614898 : term483 = False.
Proof. exact (TRANS (@lem2614865) (@lem2614897)). Qed.
Lemma lem2614899 : term480 = False.
Proof. exact (TRANS (@lem2614842) (@lem2614898)). Qed.
Lemma lem2614900 : term479 = False.
Proof. exact (TRANS (@lem2614833) (@lem2614899)). Qed.
Lemma lem2614901 (m : int) (n : int) (h1 : term384 m n) : False.
Proof. exact (EQ_MP (@lem2614900) (@lem2614830 m n h1)). Qed.
Lemma lem2614902 (m : int) (n : int) (h1 : term414 m n) : term414 m n.
Proof. exact (h1). Qed.
Lemma lem2614903 (m : int) (n : int) (h1 : term414 m n) : term413 m n.
Proof. exact (proj2 (@lem2614902 m n h1)). Qed.
Lemma lem2614905 (m : int) (n : int) (h1 : term414 m n) : term412 m n.
Proof. exact (proj2 (@lem2614903 m n h1)). Qed.
Lemma lem2614906 (m : int) (n : int) (h1 : term414 m n) : term337 n m.
Proof. exact (proj1 (@lem2614903 m n h1)). Qed.
Lemma lem2614907 (m : int) (n : int) (h1 : term414 m n) : term335 n m.
Proof. exact (proj2 (@lem2614906 m n h1)). Qed.
Lemma lem2614908 (m : int) (n : int) (h1 : term414 m n) : term153 n.
Proof. exact (proj1 (@lem2614906 m n h1)). Qed.
Lemma lem2614910 (m : int) (n : int) (h1 : term414 m n) : term317 n m.
Proof. exact (proj1 (@lem2614907 m n h1)). Qed.
Lemma lem2614912 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2614913 : term419 = term420.
Proof. exact (@lem2614912 term43 term47). Qed.
Lemma lem2614915 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614916 : term47 = term128.
Proof. exact (@lem2614915 term48). Qed.
Lemma lem2614918 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614919 : term43 = term243.
Proof. exact (@lem2614918 (NUMERAL 0)). Qed.
Lemma lem2614920 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614921 : term421 = term422.
Proof. exact (MK_COMB (@lem2614920) (@lem2614919)). Qed.
Lemma lem2614922 : term420 = term423.
Proof. exact (MK_COMB (@lem2614921) (@lem2614916)). Qed.
Lemma lem2614923 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2614925 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614926 : term420 = term426.
Proof. exact (@lem2614925 (NUMERAL 0) term48). Qed.
Lemma lem2614927 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614928 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614929 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614928 h1) (fun h1 : term426 = True => @lem2614927)). Qed.
Lemma lem2614930 : term426 = True.
Proof. exact (EQ_MP (@lem2614929) (@lem2614927)). Qed.
Lemma lem2614931 : term420 = True.
Proof. exact (TRANS (@lem2614926) (@lem2614930)). Qed.
Lemma lem2614932 : True = term420.
Proof. exact (SYM (@lem2614931)). Qed.
Lemma lem2614933 : term420.
Proof. exact (EQ_MP (@lem2614932) (@lem0)). Qed.
Lemma lem2614934 : term428.
Proof. exact (@lem2614923 (@lem2614933)). Qed.
Lemma lem2614936 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614937 : term420 = term426.
Proof. exact (@lem2614936 (NUMERAL 0) term48). Qed.
Lemma lem2614938 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614939 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614940 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614939 h1) (fun h1 : term426 = True => @lem2614938)). Qed.
Lemma lem2614941 : term426 = True.
Proof. exact (EQ_MP (@lem2614940) (@lem2614938)). Qed.
Lemma lem2614942 : term420 = True.
Proof. exact (TRANS (@lem2614937) (@lem2614941)). Qed.
Lemma lem2614943 : True = term420.
Proof. exact (SYM (@lem2614942)). Qed.
Lemma lem2614944 : term420.
Proof. exact (EQ_MP (@lem2614943) (@lem0)). Qed.
Lemma lem2614945 : term423 = term429.
Proof. exact (@lem2614934 (@lem2614944)). Qed.
Lemma lem2614947 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2614948 : term140 = term141.
Proof. exact (@lem2614947 term48 term48). Qed.
Lemma lem2614949 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2614950 : term143 = term48.
Proof. exact (EQ_MP (@lem2614949) (@lem940073)). Qed.
Lemma lem2614951 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2614952 : term141 = term47.
Proof. exact (MK_COMB (@lem2614951) (@lem2614950)). Qed.
Lemma lem2614953 : term140 = term47.
Proof. exact (TRANS (@lem2614948) (@lem2614952)). Qed.
Lemma lem2614955 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2614956 : term431 = term43.
Proof. exact (@lem2614955 term48). Qed.
Lemma lem2614957 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614958 : term432 = term421.
Proof. exact (MK_COMB (@lem2614957) (@lem2614956)). Qed.
Lemma lem2614959 : term429 = term420.
Proof. exact (MK_COMB (@lem2614958) (@lem2614953)). Qed.
Lemma lem2614961 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2614962 : term420 = term426.
Proof. exact (@lem2614961 (NUMERAL 0) term48). Qed.
Lemma lem2614963 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2614964 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2614965 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2614964 h1) (fun h1 : term426 = True => @lem2614963)). Qed.
Lemma lem2614966 : term426 = True.
Proof. exact (EQ_MP (@lem2614965) (@lem2614963)). Qed.
Lemma lem2614967 : term420 = True.
Proof. exact (TRANS (@lem2614962) (@lem2614966)). Qed.
Lemma lem2614968 : term429 = True.
Proof. exact (TRANS (@lem2614959) (@lem2614967)). Qed.
Lemma lem2614969 : term423 = True.
Proof. exact (TRANS (@lem2614945) (@lem2614968)). Qed.
Lemma lem2614970 : term420 = True.
Proof. exact (TRANS (@lem2614922) (@lem2614969)). Qed.
Lemma lem2614971 : term419 = True.
Proof. exact (TRANS (@lem2614913) (@lem2614970)). Qed.
Lemma lem2614972 : True = term419.
Proof. exact (SYM (@lem2614971)). Qed.
Lemma lem2614973 : term419.
Proof. exact (EQ_MP (@lem2614972) (@lem0)). Qed.
Lemma lem2614974 (m : int) (n : int) (h1 : term414 m n) : term517 n.
Proof. exact (conj (@lem2614973) (@lem2614908 m n h1)). Qed.
Lemma lem2614976 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2614977 (n : int) : term518 n.
Proof. exact (@lem2614976 term47 (term150 n)). Qed.
Lemma lem2614978 (m : int) (n : int) (h1 : term414 m n) : term519 n.
Proof. exact (@lem2614977 n (@lem2614974 m n h1)). Qed.
Lemma lem2614979 (n : int) : (term520 n) = (term150 n).
Proof. exact (@lem1982733 (term150 n)). Qed.
Lemma lem2614980 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2614981 (n : int) : (term521 n) = (term152 n).
Proof. exact (MK_COMB (@lem2614980) (@lem2614979 n)). Qed.
Lemma lem2614982 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2614983 (n : int) : (term519 n) = (term153 n).
Proof. exact (MK_COMB (@lem2614981 n) (@lem2614982)). Qed.
Lemma lem2614984 (m : int) (n : int) (h1 : term414 m n) : term153 n.
Proof. exact (EQ_MP (@lem2614983 n) (@lem2614978 m n h1)). Qed.
Lemma lem2614986 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2614987 : term419 = term420.
Proof. exact (@lem2614986 term43 term47). Qed.
Lemma lem2614989 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614990 : term47 = term128.
Proof. exact (@lem2614989 term48). Qed.
Lemma lem2614992 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2614993 : term43 = term243.
Proof. exact (@lem2614992 (NUMERAL 0)). Qed.
Lemma lem2614994 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2614995 : term421 = term422.
Proof. exact (MK_COMB (@lem2614994) (@lem2614993)). Qed.
Lemma lem2614996 : term420 = term423.
Proof. exact (MK_COMB (@lem2614995) (@lem2614990)). Qed.
Lemma lem2614997 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2614999 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615000 : term420 = term426.
Proof. exact (@lem2614999 (NUMERAL 0) term48). Qed.
Lemma lem2615001 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615002 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615003 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615002 h1) (fun h1 : term426 = True => @lem2615001)). Qed.
Lemma lem2615004 : term426 = True.
Proof. exact (EQ_MP (@lem2615003) (@lem2615001)). Qed.
Lemma lem2615005 : term420 = True.
Proof. exact (TRANS (@lem2615000) (@lem2615004)). Qed.
Lemma lem2615006 : True = term420.
Proof. exact (SYM (@lem2615005)). Qed.
Lemma lem2615007 : term420.
Proof. exact (EQ_MP (@lem2615006) (@lem0)). Qed.
Lemma lem2615008 : term428.
Proof. exact (@lem2614997 (@lem2615007)). Qed.
Lemma lem2615010 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615011 : term420 = term426.
Proof. exact (@lem2615010 (NUMERAL 0) term48). Qed.
Lemma lem2615012 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615013 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615014 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615013 h1) (fun h1 : term426 = True => @lem2615012)). Qed.
Lemma lem2615015 : term426 = True.
Proof. exact (EQ_MP (@lem2615014) (@lem2615012)). Qed.
Lemma lem2615016 : term420 = True.
Proof. exact (TRANS (@lem2615011) (@lem2615015)). Qed.
Lemma lem2615017 : True = term420.
Proof. exact (SYM (@lem2615016)). Qed.
Lemma lem2615018 : term420.
Proof. exact (EQ_MP (@lem2615017) (@lem0)). Qed.
Lemma lem2615019 : term423 = term429.
Proof. exact (@lem2615008 (@lem2615018)). Qed.
Lemma lem2615021 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615022 : term140 = term141.
Proof. exact (@lem2615021 term48 term48). Qed.
Lemma lem2615023 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615024 : term143 = term48.
Proof. exact (EQ_MP (@lem2615023) (@lem940073)). Qed.
Lemma lem2615025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615026 : term141 = term47.
Proof. exact (MK_COMB (@lem2615025) (@lem2615024)). Qed.
Lemma lem2615027 : term140 = term47.
Proof. exact (TRANS (@lem2615022) (@lem2615026)). Qed.
Lemma lem2615029 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615030 : term431 = term43.
Proof. exact (@lem2615029 term48). Qed.
Lemma lem2615031 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2615032 : term432 = term421.
Proof. exact (MK_COMB (@lem2615031) (@lem2615030)). Qed.
Lemma lem2615033 : term429 = term420.
Proof. exact (MK_COMB (@lem2615032) (@lem2615027)). Qed.
Lemma lem2615035 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615036 : term420 = term426.
Proof. exact (@lem2615035 (NUMERAL 0) term48). Qed.
Lemma lem2615037 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615038 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615039 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615038 h1) (fun h1 : term426 = True => @lem2615037)). Qed.
Lemma lem2615040 : term426 = True.
Proof. exact (EQ_MP (@lem2615039) (@lem2615037)). Qed.
Lemma lem2615041 : term420 = True.
Proof. exact (TRANS (@lem2615036) (@lem2615040)). Qed.
Lemma lem2615042 : term429 = True.
Proof. exact (TRANS (@lem2615033) (@lem2615041)). Qed.
Lemma lem2615043 : term423 = True.
Proof. exact (TRANS (@lem2615019) (@lem2615042)). Qed.
Lemma lem2615044 : term420 = True.
Proof. exact (TRANS (@lem2614996) (@lem2615043)). Qed.
Lemma lem2615045 : term419 = True.
Proof. exact (TRANS (@lem2614987) (@lem2615044)). Qed.
Lemma lem2615046 : True = term419.
Proof. exact (SYM (@lem2615045)). Qed.
Lemma lem2615047 : term419.
Proof. exact (EQ_MP (@lem2615046) (@lem0)). Qed.
Lemma lem2615048 (m : int) (n : int) (h1 : term414 m n) : term551 m n.
Proof. exact (conj (@lem2615047) (@lem2614905 m n h1)). Qed.
Lemma lem2615050 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2615051 (m : int) (n : int) : term552 m n.
Proof. exact (@lem2615050 term47 (term402 m n)). Qed.
Lemma lem2615052 (m : int) (n : int) (h1 : term414 m n) : term553 m n.
Proof. exact (@lem2615051 m n (@lem2615048 m n h1)). Qed.
Lemma lem2615053 (m : int) (n : int) : (term554 m n) = (term402 m n).
Proof. exact (@lem1982733 (term402 m n)). Qed.
Lemma lem2615054 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2615055 (m : int) (n : int) : (term555 m n) = (term411 m n).
Proof. exact (MK_COMB (@lem2615054) (@lem2615053 m n)). Qed.
Lemma lem2615056 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2615057 (m : int) (n : int) : (term553 m n) = (term412 m n).
Proof. exact (MK_COMB (@lem2615055 m n) (@lem2615056)). Qed.
Lemma lem2615058 (m : int) (n : int) (h1 : term414 m n) : term412 m n.
Proof. exact (EQ_MP (@lem2615057 m n) (@lem2615052 m n h1)). Qed.
Lemma lem2615059 (m : int) (n : int) (h1 : term414 m n) : term556 m n.
Proof. exact (conj (@lem2615058 m n h1) (@lem2614984 m n h1)). Qed.
Lemma lem2615061 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2615062 (m : int) (n : int) : term557 m n.
Proof. exact (@lem2615061 (term402 m n) (term150 n)). Qed.
Lemma lem2615063 (m : int) (n : int) (h1 : term414 m n) : term558 m n.
Proof. exact (@lem2615062 m n (@lem2615059 m n h1)). Qed.
Lemma lem2615064 (m : int) (n : int) : (term559 m n) = (term560 m n).
Proof. exact (@lem1982755 (term58 m n) (term401 m n) (term150 n)). Qed.
Lemma lem2615065 (m : int) (n : int) : (term532 m n) = (term533 m n).
Proof. exact (@lem1982755 (real_of_int m) (term198 n) (term150 n)). Qed.
Lemma lem2615066 (n : int) : (term534 n) = (term471 n).
Proof. exact (@lem1982763 (term198 n) (real_of_int n) term131). Qed.
Lemma lem2615067 (n : int) : (term472 n) = (term473 n).
Proof. exact (@lem1982713 term131 (real_of_int n)). Qed.
Lemma lem2615069 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615070 : term47 = term128.
Proof. exact (@lem2615069 term48). Qed.
Lemma lem2615072 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2615073 : term131 = term132.
Proof. exact (@lem2615072 term48). Qed.
Lemma lem2615074 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615075 : term452 = term453.
Proof. exact (MK_COMB (@lem2615074) (@lem2615073)). Qed.
Lemma lem2615076 : term454 = term455.
Proof. exact (MK_COMB (@lem2615075) (@lem2615070)). Qed.
Lemma lem2615077 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2615079 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615080 : term420 = term426.
Proof. exact (@lem2615079 (NUMERAL 0) term48). Qed.
Lemma lem2615081 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615082 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615083 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615082 h1) (fun h1 : term426 = True => @lem2615081)). Qed.
Lemma lem2615084 : term426 = True.
Proof. exact (EQ_MP (@lem2615083) (@lem2615081)). Qed.
Lemma lem2615085 : term420 = True.
Proof. exact (TRANS (@lem2615080) (@lem2615084)). Qed.
Lemma lem2615086 : True = term420.
Proof. exact (SYM (@lem2615085)). Qed.
Lemma lem2615087 : term420.
Proof. exact (EQ_MP (@lem2615086) (@lem0)). Qed.
Lemma lem2615088 : term457.
Proof. exact (@lem2615077 (@lem2615087)). Qed.
Lemma lem2615090 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615091 : term420 = term426.
Proof. exact (@lem2615090 (NUMERAL 0) term48). Qed.
Lemma lem2615092 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615093 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615094 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615093 h1) (fun h1 : term426 = True => @lem2615092)). Qed.
Lemma lem2615095 : term426 = True.
Proof. exact (EQ_MP (@lem2615094) (@lem2615092)). Qed.
Lemma lem2615096 : term420 = True.
Proof. exact (TRANS (@lem2615091) (@lem2615095)). Qed.
Lemma lem2615097 : True = term420.
Proof. exact (SYM (@lem2615096)). Qed.
Lemma lem2615098 : term420.
Proof. exact (EQ_MP (@lem2615097) (@lem0)). Qed.
Lemma lem2615099 : term458.
Proof. exact (@lem2615088 (@lem2615098)). Qed.
Lemma lem2615101 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615102 : term420 = term426.
Proof. exact (@lem2615101 (NUMERAL 0) term48). Qed.
Lemma lem2615103 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615104 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615105 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615104 h1) (fun h1 : term426 = True => @lem2615103)). Qed.
Lemma lem2615106 : term426 = True.
Proof. exact (EQ_MP (@lem2615105) (@lem2615103)). Qed.
Lemma lem2615107 : term420 = True.
Proof. exact (TRANS (@lem2615102) (@lem2615106)). Qed.
Lemma lem2615108 : True = term420.
Proof. exact (SYM (@lem2615107)). Qed.
Lemma lem2615109 : term420.
Proof. exact (EQ_MP (@lem2615108) (@lem0)). Qed.
Lemma lem2615110 : term459.
Proof. exact (@lem2615099 (@lem2615109)). Qed.
Lemma lem2615112 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615113 : term140 = term141.
Proof. exact (@lem2615112 term48 term48). Qed.
Lemma lem2615114 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615115 : term143 = term48.
Proof. exact (EQ_MP (@lem2615114) (@lem940073)). Qed.
Lemma lem2615116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615117 : term141 = term47.
Proof. exact (MK_COMB (@lem2615116) (@lem2615115)). Qed.
Lemma lem2615118 : term140 = term47.
Proof. exact (TRANS (@lem2615113) (@lem2615117)). Qed.
Lemma lem2615120 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2615121 : term135 = term146.
Proof. exact (@lem2615120 term48 term48). Qed.
Lemma lem2615122 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615123 : term143 = term48.
Proof. exact (EQ_MP (@lem2615122) (@lem940073)). Qed.
Lemma lem2615124 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615125 : term141 = term47.
Proof. exact (MK_COMB (@lem2615124) (@lem2615123)). Qed.
Lemma lem2615126 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2615127 : term146 = term131.
Proof. exact (MK_COMB (@lem2615126) (@lem2615125)). Qed.
Lemma lem2615128 : term135 = term131.
Proof. exact (TRANS (@lem2615121) (@lem2615127)). Qed.
Lemma lem2615129 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615130 : term460 = term452.
Proof. exact (MK_COMB (@lem2615129) (@lem2615128)). Qed.
Lemma lem2615131 : term461 = term454.
Proof. exact (MK_COMB (@lem2615130) (@lem2615118)). Qed.
Lemma lem2615133 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2615134 : term454 = term43.
Proof. exact (@lem2615133 term48). Qed.
Lemma lem2615135 : term461 = term43.
Proof. exact (TRANS (@lem2615131) (@lem2615134)). Qed.
Lemma lem2615136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2615137 : term463 = term464.
Proof. exact (MK_COMB (@lem2615136) (@lem2615135)). Qed.
Lemma lem2615138 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2615139 : term465 = term431.
Proof. exact (MK_COMB (@lem2615137) (@lem2615138)). Qed.
Lemma lem2615141 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615142 : term431 = term43.
Proof. exact (@lem2615141 term48). Qed.
Lemma lem2615143 : term465 = term43.
Proof. exact (TRANS (@lem2615139) (@lem2615142)). Qed.
Lemma lem2615145 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615146 : term140 = term141.
Proof. exact (@lem2615145 term48 term48). Qed.
Lemma lem2615147 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615148 : term143 = term48.
Proof. exact (EQ_MP (@lem2615147) (@lem940073)). Qed.
Lemma lem2615149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615150 : term141 = term47.
Proof. exact (MK_COMB (@lem2615149) (@lem2615148)). Qed.
Lemma lem2615151 : term140 = term47.
Proof. exact (TRANS (@lem2615146) (@lem2615150)). Qed.
Lemma lem2615152 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2615153 : term466 = term431.
Proof. exact (MK_COMB (@lem2615152) (@lem2615151)). Qed.
Lemma lem2615155 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615156 : term431 = term43.
Proof. exact (@lem2615155 term48). Qed.
Lemma lem2615157 : term466 = term43.
Proof. exact (TRANS (@lem2615153) (@lem2615156)). Qed.
Lemma lem2615158 : term43 = term466.
Proof. exact (SYM (@lem2615157)). Qed.
Lemma lem2615159 : term465 = term466.
Proof. exact (TRANS (@lem2615143) (@lem2615158)). Qed.
Lemma lem2615160 : term455 = term243.
Proof. exact (@lem2615110 (@lem2615159)). Qed.
Lemma lem2615161 : term454 = term243.
Proof. exact (TRANS (@lem2615076) (@lem2615160)). Qed.
Lemma lem2615163 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2615164 : term243 = term43.
Proof. exact (@lem2615163 term43). Qed.
Lemma lem2615165 : term454 = term43.
Proof. exact (TRANS (@lem2615161) (@lem2615164)). Qed.
Lemma lem2615166 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2615167 : term467 = term464.
Proof. exact (MK_COMB (@lem2615166) (@lem2615165)). Qed.
Lemma lem2615168 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2615169 (n : int) : (term473 n) = (term474 n).
Proof. exact (MK_COMB (@lem2615167) (@lem2615168 n)). Qed.
Lemma lem2615170 (n : int) : (term472 n) = (term474 n).
Proof. exact (TRANS (@lem2615067 n) (@lem2615169 n)). Qed.
Lemma lem2615171 (n : int) : (term474 n) = term43.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2615172 (n : int) : (term472 n) = term43.
Proof. exact (TRANS (@lem2615170 n) (@lem2615171 n)). Qed.
Lemma lem2615173 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615174 (n : int) : (term475 n) = term45.
Proof. exact (MK_COMB (@lem2615173) (@lem2615172 n)). Qed.
Lemma lem2615175 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2615176 (n : int) : (term471 n) = term476.
Proof. exact (MK_COMB (@lem2615174 n) (@lem2615175)). Qed.
Lemma lem2615177 (n : int) : (term534 n) = term476.
Proof. exact (TRANS (@lem2615066 n) (@lem2615176 n)). Qed.
Lemma lem2615178 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2615179 (n : int) : (term534 n) = term131.
Proof. exact (TRANS (@lem2615177 n) (@lem2615178)). Qed.
Lemma lem2615180 (m : int) : (term83 m) = (term83 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem2615181 (n : int) (m : int) : (term533 m n) = (term150 m).
Proof. exact (MK_COMB (@lem2615180 m) (@lem2615179 n)). Qed.
Lemma lem2615182 (n : int) (m : int) : (term532 m n) = (term150 m).
Proof. exact (TRANS (@lem2615065 m n) (@lem2615181 n m)). Qed.
Lemma lem2615183 (m : int) (n : int) : (term354 m n) = (term354 m n).
Proof. exact (eq_refl (term354 m n)). Qed.
Lemma lem2615184 (n : int) (m : int) : (term560 m n) = (term561 n m).
Proof. exact (MK_COMB (@lem2615183 m n) (@lem2615182 n m)). Qed.
Lemma lem2615185 (n : int) (m : int) : (term559 m n) = (term561 n m).
Proof. exact (TRANS (@lem2615064 m n) (@lem2615184 n m)). Qed.
Lemma lem2615186 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2615187 (n : int) (m : int) : (term562 m n) = (term563 n m).
Proof. exact (MK_COMB (@lem2615186) (@lem2615185 n m)). Qed.
Lemma lem2615188 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2615189 (n : int) (m : int) : (term558 m n) = (term564 n m).
Proof. exact (MK_COMB (@lem2615187 n m) (@lem2615188)). Qed.
Lemma lem2615190 (m : int) (n : int) (h1 : term414 m n) : term564 n m.
Proof. exact (EQ_MP (@lem2615189 n m) (@lem2615063 m n h1)). Qed.
Lemma lem2615192 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2615193 : term419 = term420.
Proof. exact (@lem2615192 term43 term47). Qed.
Lemma lem2615195 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615196 : term47 = term128.
Proof. exact (@lem2615195 term48). Qed.
Lemma lem2615198 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615199 : term43 = term243.
Proof. exact (@lem2615198 (NUMERAL 0)). Qed.
Lemma lem2615200 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2615201 : term421 = term422.
Proof. exact (MK_COMB (@lem2615200) (@lem2615199)). Qed.
Lemma lem2615202 : term420 = term423.
Proof. exact (MK_COMB (@lem2615201) (@lem2615196)). Qed.
Lemma lem2615203 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2615205 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615206 : term420 = term426.
Proof. exact (@lem2615205 (NUMERAL 0) term48). Qed.
Lemma lem2615207 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615208 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615209 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615208 h1) (fun h1 : term426 = True => @lem2615207)). Qed.
Lemma lem2615210 : term426 = True.
Proof. exact (EQ_MP (@lem2615209) (@lem2615207)). Qed.
Lemma lem2615211 : term420 = True.
Proof. exact (TRANS (@lem2615206) (@lem2615210)). Qed.
Lemma lem2615212 : True = term420.
Proof. exact (SYM (@lem2615211)). Qed.
Lemma lem2615213 : term420.
Proof. exact (EQ_MP (@lem2615212) (@lem0)). Qed.
Lemma lem2615214 : term428.
Proof. exact (@lem2615203 (@lem2615213)). Qed.
Lemma lem2615216 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615217 : term420 = term426.
Proof. exact (@lem2615216 (NUMERAL 0) term48). Qed.
Lemma lem2615218 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615219 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615220 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615219 h1) (fun h1 : term426 = True => @lem2615218)). Qed.
Lemma lem2615221 : term426 = True.
Proof. exact (EQ_MP (@lem2615220) (@lem2615218)). Qed.
Lemma lem2615222 : term420 = True.
Proof. exact (TRANS (@lem2615217) (@lem2615221)). Qed.
Lemma lem2615223 : True = term420.
Proof. exact (SYM (@lem2615222)). Qed.
Lemma lem2615224 : term420.
Proof. exact (EQ_MP (@lem2615223) (@lem0)). Qed.
Lemma lem2615225 : term423 = term429.
Proof. exact (@lem2615214 (@lem2615224)). Qed.
Lemma lem2615227 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615228 : term140 = term141.
Proof. exact (@lem2615227 term48 term48). Qed.
Lemma lem2615229 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615230 : term143 = term48.
Proof. exact (EQ_MP (@lem2615229) (@lem940073)). Qed.
Lemma lem2615231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615232 : term141 = term47.
Proof. exact (MK_COMB (@lem2615231) (@lem2615230)). Qed.
Lemma lem2615233 : term140 = term47.
Proof. exact (TRANS (@lem2615228) (@lem2615232)). Qed.
Lemma lem2615235 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615236 : term431 = term43.
Proof. exact (@lem2615235 term48). Qed.
Lemma lem2615237 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2615238 : term432 = term421.
Proof. exact (MK_COMB (@lem2615237) (@lem2615236)). Qed.
Lemma lem2615239 : term429 = term420.
Proof. exact (MK_COMB (@lem2615238) (@lem2615233)). Qed.
Lemma lem2615241 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615242 : term420 = term426.
Proof. exact (@lem2615241 (NUMERAL 0) term48). Qed.
Lemma lem2615243 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615244 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615245 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615244 h1) (fun h1 : term426 = True => @lem2615243)). Qed.
Lemma lem2615246 : term426 = True.
Proof. exact (EQ_MP (@lem2615245) (@lem2615243)). Qed.
Lemma lem2615247 : term420 = True.
Proof. exact (TRANS (@lem2615242) (@lem2615246)). Qed.
Lemma lem2615248 : term429 = True.
Proof. exact (TRANS (@lem2615239) (@lem2615247)). Qed.
Lemma lem2615249 : term423 = True.
Proof. exact (TRANS (@lem2615225) (@lem2615248)). Qed.
Lemma lem2615250 : term420 = True.
Proof. exact (TRANS (@lem2615202) (@lem2615249)). Qed.
Lemma lem2615251 : term419 = True.
Proof. exact (TRANS (@lem2615193) (@lem2615250)). Qed.
Lemma lem2615252 : True = term419.
Proof. exact (SYM (@lem2615251)). Qed.
Lemma lem2615253 : term419.
Proof. exact (EQ_MP (@lem2615252) (@lem0)). Qed.
Lemma lem2615254 (m : int) (n : int) (h1 : term414 m n) : term565 n m.
Proof. exact (conj (@lem2615253) (@lem2615190 m n h1)). Qed.
Lemma lem2615256 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2615257 (n : int) (m : int) : term566 n m.
Proof. exact (@lem2615256 term47 (term561 n m)). Qed.
Lemma lem2615258 (m : int) (n : int) (h1 : term414 m n) : term567 n m.
Proof. exact (@lem2615257 n m (@lem2615254 m n h1)). Qed.
Lemma lem2615259 (n : int) (m : int) : (term568 n m) = (term561 n m).
Proof. exact (@lem1982733 (term561 n m)). Qed.
Lemma lem2615260 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2615261 (n : int) (m : int) : (term569 n m) = (term563 n m).
Proof. exact (MK_COMB (@lem2615260) (@lem2615259 n m)). Qed.
Lemma lem2615262 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2615263 (n : int) (m : int) : (term567 n m) = (term564 n m).
Proof. exact (MK_COMB (@lem2615261 n m) (@lem2615262)). Qed.
Lemma lem2615264 (m : int) (n : int) (h1 : term414 m n) : term564 n m.
Proof. exact (EQ_MP (@lem2615263 n m) (@lem2615258 m n h1)). Qed.
Lemma lem2615266 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2615267 : term419 = term420.
Proof. exact (@lem2615266 term43 term47). Qed.
Lemma lem2615269 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615270 : term47 = term128.
Proof. exact (@lem2615269 term48). Qed.
Lemma lem2615272 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615273 : term43 = term243.
Proof. exact (@lem2615272 (NUMERAL 0)). Qed.
Lemma lem2615274 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2615275 : term421 = term422.
Proof. exact (MK_COMB (@lem2615274) (@lem2615273)). Qed.
Lemma lem2615276 : term420 = term423.
Proof. exact (MK_COMB (@lem2615275) (@lem2615270)). Qed.
Lemma lem2615277 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2615279 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615280 : term420 = term426.
Proof. exact (@lem2615279 (NUMERAL 0) term48). Qed.
Lemma lem2615281 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615282 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615283 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615282 h1) (fun h1 : term426 = True => @lem2615281)). Qed.
Lemma lem2615284 : term426 = True.
Proof. exact (EQ_MP (@lem2615283) (@lem2615281)). Qed.
Lemma lem2615285 : term420 = True.
Proof. exact (TRANS (@lem2615280) (@lem2615284)). Qed.
Lemma lem2615286 : True = term420.
Proof. exact (SYM (@lem2615285)). Qed.
Lemma lem2615287 : term420.
Proof. exact (EQ_MP (@lem2615286) (@lem0)). Qed.
Lemma lem2615288 : term428.
Proof. exact (@lem2615277 (@lem2615287)). Qed.
Lemma lem2615290 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615291 : term420 = term426.
Proof. exact (@lem2615290 (NUMERAL 0) term48). Qed.
Lemma lem2615292 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615293 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615294 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615293 h1) (fun h1 : term426 = True => @lem2615292)). Qed.
Lemma lem2615295 : term426 = True.
Proof. exact (EQ_MP (@lem2615294) (@lem2615292)). Qed.
Lemma lem2615296 : term420 = True.
Proof. exact (TRANS (@lem2615291) (@lem2615295)). Qed.
Lemma lem2615297 : True = term420.
Proof. exact (SYM (@lem2615296)). Qed.
Lemma lem2615298 : term420.
Proof. exact (EQ_MP (@lem2615297) (@lem0)). Qed.
Lemma lem2615299 : term423 = term429.
Proof. exact (@lem2615288 (@lem2615298)). Qed.
Lemma lem2615301 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615302 : term140 = term141.
Proof. exact (@lem2615301 term48 term48). Qed.
Lemma lem2615303 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615304 : term143 = term48.
Proof. exact (EQ_MP (@lem2615303) (@lem940073)). Qed.
Lemma lem2615305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615306 : term141 = term47.
Proof. exact (MK_COMB (@lem2615305) (@lem2615304)). Qed.
Lemma lem2615307 : term140 = term47.
Proof. exact (TRANS (@lem2615302) (@lem2615306)). Qed.
Lemma lem2615309 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615310 : term431 = term43.
Proof. exact (@lem2615309 term48). Qed.
Lemma lem2615311 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2615312 : term432 = term421.
Proof. exact (MK_COMB (@lem2615311) (@lem2615310)). Qed.
Lemma lem2615313 : term429 = term420.
Proof. exact (MK_COMB (@lem2615312) (@lem2615307)). Qed.
Lemma lem2615315 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615316 : term420 = term426.
Proof. exact (@lem2615315 (NUMERAL 0) term48). Qed.
Lemma lem2615317 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615318 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615319 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615318 h1) (fun h1 : term426 = True => @lem2615317)). Qed.
Lemma lem2615320 : term426 = True.
Proof. exact (EQ_MP (@lem2615319) (@lem2615317)). Qed.
Lemma lem2615321 : term420 = True.
Proof. exact (TRANS (@lem2615316) (@lem2615320)). Qed.
Lemma lem2615322 : term429 = True.
Proof. exact (TRANS (@lem2615313) (@lem2615321)). Qed.
Lemma lem2615323 : term423 = True.
Proof. exact (TRANS (@lem2615299) (@lem2615322)). Qed.
Lemma lem2615324 : term420 = True.
Proof. exact (TRANS (@lem2615276) (@lem2615323)). Qed.
Lemma lem2615325 : term419 = True.
Proof. exact (TRANS (@lem2615267) (@lem2615324)). Qed.
Lemma lem2615326 : True = term419.
Proof. exact (SYM (@lem2615325)). Qed.
Lemma lem2615327 : term419.
Proof. exact (EQ_MP (@lem2615326) (@lem0)). Qed.
Lemma lem2615328 (m : int) (n : int) (h1 : term414 m n) : term570 n m.
Proof. exact (conj (@lem2615327) (@lem2614910 m n h1)). Qed.
Lemma lem2615330 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2615331 (n : int) (m : int) : term571 n m.
Proof. exact (@lem2615330 term47 (term307 n m)). Qed.
Lemma lem2615332 (m : int) (n : int) (h1 : term414 m n) : term572 n m.
Proof. exact (@lem2615331 n m (@lem2615328 m n h1)). Qed.
Lemma lem2615333 (n : int) (m : int) : (term573 n m) = (term307 n m).
Proof. exact (@lem1982733 (term307 n m)). Qed.
Lemma lem2615334 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2615335 (n : int) (m : int) : (term574 n m) = (term316 n m).
Proof. exact (MK_COMB (@lem2615334) (@lem2615333 n m)). Qed.
Lemma lem2615336 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2615337 (n : int) (m : int) : (term572 n m) = (term317 n m).
Proof. exact (MK_COMB (@lem2615335 n m) (@lem2615336)). Qed.
Lemma lem2615338 (m : int) (n : int) (h1 : term414 m n) : term317 n m.
Proof. exact (EQ_MP (@lem2615337 n m) (@lem2615332 m n h1)). Qed.
Lemma lem2615339 (m : int) (n : int) (h1 : term414 m n) : term575 n m.
Proof. exact (conj (@lem2615338 m n h1) (@lem2615264 m n h1)). Qed.
Lemma lem2615341 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2615342 (n : int) (m : int) : term576 n m.
Proof. exact (@lem2615341 (term307 n m) (term561 n m)). Qed.
Lemma lem2615343 (m : int) (n : int) (h1 : term414 m n) : term577 n m.
Proof. exact (@lem2615342 n m (@lem2615339 m n h1)). Qed.
Lemma lem2615344 (n : int) (m : int) : (term578 n m) = (term579 n m).
Proof. exact (@lem1982753 (term304 m n) (term58 m n) (term198 m) (term150 m)). Qed.
Lemma lem2615345 (m : int) (n : int) : (term450 m n) = (term451 m n).
Proof. exact (@lem1982713 term131 (term58 m n)). Qed.
Lemma lem2615347 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615348 : term47 = term128.
Proof. exact (@lem2615347 term48). Qed.
Lemma lem2615350 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2615351 : term131 = term132.
Proof. exact (@lem2615350 term48). Qed.
Lemma lem2615352 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615353 : term452 = term453.
Proof. exact (MK_COMB (@lem2615352) (@lem2615351)). Qed.
Lemma lem2615354 : term454 = term455.
Proof. exact (MK_COMB (@lem2615353) (@lem2615348)). Qed.
Lemma lem2615355 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2615357 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615358 : term420 = term426.
Proof. exact (@lem2615357 (NUMERAL 0) term48). Qed.
Lemma lem2615359 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615360 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615361 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615360 h1) (fun h1 : term426 = True => @lem2615359)). Qed.
Lemma lem2615362 : term426 = True.
Proof. exact (EQ_MP (@lem2615361) (@lem2615359)). Qed.
Lemma lem2615363 : term420 = True.
Proof. exact (TRANS (@lem2615358) (@lem2615362)). Qed.
Lemma lem2615364 : True = term420.
Proof. exact (SYM (@lem2615363)). Qed.
Lemma lem2615365 : term420.
Proof. exact (EQ_MP (@lem2615364) (@lem0)). Qed.
Lemma lem2615366 : term457.
Proof. exact (@lem2615355 (@lem2615365)). Qed.
Lemma lem2615368 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615369 : term420 = term426.
Proof. exact (@lem2615368 (NUMERAL 0) term48). Qed.
Lemma lem2615370 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615371 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615372 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615371 h1) (fun h1 : term426 = True => @lem2615370)). Qed.
Lemma lem2615373 : term426 = True.
Proof. exact (EQ_MP (@lem2615372) (@lem2615370)). Qed.
Lemma lem2615374 : term420 = True.
Proof. exact (TRANS (@lem2615369) (@lem2615373)). Qed.
Lemma lem2615375 : True = term420.
Proof. exact (SYM (@lem2615374)). Qed.
Lemma lem2615376 : term420.
Proof. exact (EQ_MP (@lem2615375) (@lem0)). Qed.
Lemma lem2615377 : term458.
Proof. exact (@lem2615366 (@lem2615376)). Qed.
Lemma lem2615379 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615380 : term420 = term426.
Proof. exact (@lem2615379 (NUMERAL 0) term48). Qed.
Lemma lem2615381 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615382 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615383 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615382 h1) (fun h1 : term426 = True => @lem2615381)). Qed.
Lemma lem2615384 : term426 = True.
Proof. exact (EQ_MP (@lem2615383) (@lem2615381)). Qed.
Lemma lem2615385 : term420 = True.
Proof. exact (TRANS (@lem2615380) (@lem2615384)). Qed.
Lemma lem2615386 : True = term420.
Proof. exact (SYM (@lem2615385)). Qed.
Lemma lem2615387 : term420.
Proof. exact (EQ_MP (@lem2615386) (@lem0)). Qed.
Lemma lem2615388 : term459.
Proof. exact (@lem2615377 (@lem2615387)). Qed.
Lemma lem2615390 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615391 : term140 = term141.
Proof. exact (@lem2615390 term48 term48). Qed.
Lemma lem2615392 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615393 : term143 = term48.
Proof. exact (EQ_MP (@lem2615392) (@lem940073)). Qed.
Lemma lem2615394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615395 : term141 = term47.
Proof. exact (MK_COMB (@lem2615394) (@lem2615393)). Qed.
Lemma lem2615396 : term140 = term47.
Proof. exact (TRANS (@lem2615391) (@lem2615395)). Qed.
Lemma lem2615398 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2615399 : term135 = term146.
Proof. exact (@lem2615398 term48 term48). Qed.
Lemma lem2615400 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615401 : term143 = term48.
Proof. exact (EQ_MP (@lem2615400) (@lem940073)). Qed.
Lemma lem2615402 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615403 : term141 = term47.
Proof. exact (MK_COMB (@lem2615402) (@lem2615401)). Qed.
Lemma lem2615404 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2615405 : term146 = term131.
Proof. exact (MK_COMB (@lem2615404) (@lem2615403)). Qed.
Lemma lem2615406 : term135 = term131.
Proof. exact (TRANS (@lem2615399) (@lem2615405)). Qed.
Lemma lem2615407 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615408 : term460 = term452.
Proof. exact (MK_COMB (@lem2615407) (@lem2615406)). Qed.
Lemma lem2615409 : term461 = term454.
Proof. exact (MK_COMB (@lem2615408) (@lem2615396)). Qed.
Lemma lem2615411 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2615412 : term454 = term43.
Proof. exact (@lem2615411 term48). Qed.
Lemma lem2615413 : term461 = term43.
Proof. exact (TRANS (@lem2615409) (@lem2615412)). Qed.
Lemma lem2615414 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2615415 : term463 = term464.
Proof. exact (MK_COMB (@lem2615414) (@lem2615413)). Qed.
Lemma lem2615416 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2615417 : term465 = term431.
Proof. exact (MK_COMB (@lem2615415) (@lem2615416)). Qed.
Lemma lem2615419 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615420 : term431 = term43.
Proof. exact (@lem2615419 term48). Qed.
Lemma lem2615421 : term465 = term43.
Proof. exact (TRANS (@lem2615417) (@lem2615420)). Qed.
Lemma lem2615423 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615424 : term140 = term141.
Proof. exact (@lem2615423 term48 term48). Qed.
Lemma lem2615425 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615426 : term143 = term48.
Proof. exact (EQ_MP (@lem2615425) (@lem940073)). Qed.
Lemma lem2615427 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615428 : term141 = term47.
Proof. exact (MK_COMB (@lem2615427) (@lem2615426)). Qed.
Lemma lem2615429 : term140 = term47.
Proof. exact (TRANS (@lem2615424) (@lem2615428)). Qed.
Lemma lem2615430 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2615431 : term466 = term431.
Proof. exact (MK_COMB (@lem2615430) (@lem2615429)). Qed.
Lemma lem2615433 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615434 : term431 = term43.
Proof. exact (@lem2615433 term48). Qed.
Lemma lem2615435 : term466 = term43.
Proof. exact (TRANS (@lem2615431) (@lem2615434)). Qed.
Lemma lem2615436 : term43 = term466.
Proof. exact (SYM (@lem2615435)). Qed.
Lemma lem2615437 : term465 = term466.
Proof. exact (TRANS (@lem2615421) (@lem2615436)). Qed.
Lemma lem2615438 : term455 = term243.
Proof. exact (@lem2615388 (@lem2615437)). Qed.
Lemma lem2615439 : term454 = term243.
Proof. exact (TRANS (@lem2615354) (@lem2615438)). Qed.
Lemma lem2615441 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2615442 : term243 = term43.
Proof. exact (@lem2615441 term43). Qed.
Lemma lem2615443 : term454 = term43.
Proof. exact (TRANS (@lem2615439) (@lem2615442)). Qed.
Lemma lem2615444 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2615445 : term467 = term464.
Proof. exact (MK_COMB (@lem2615444) (@lem2615443)). Qed.
Lemma lem2615446 (m : int) (n : int) : (term58 m n) = (term58 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem2615447 (m : int) (n : int) : (term451 m n) = (term468 m n).
Proof. exact (MK_COMB (@lem2615445) (@lem2615446 m n)). Qed.
Lemma lem2615448 (m : int) (n : int) : (term450 m n) = (term468 m n).
Proof. exact (TRANS (@lem2615345 m n) (@lem2615447 m n)). Qed.
Lemma lem2615449 (m : int) (n : int) : (term468 m n) = term43.
Proof. exact (@lem1982719 (term58 m n)). Qed.
Lemma lem2615450 (m : int) (n : int) : (term450 m n) = term43.
Proof. exact (TRANS (@lem2615448 m n) (@lem2615449 m n)). Qed.
Lemma lem2615451 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615452 (m : int) (n : int) : (term469 m n) = term45.
Proof. exact (MK_COMB (@lem2615451) (@lem2615450 m n)). Qed.
Lemma lem2615453 (m : int) : (term534 m) = (term471 m).
Proof. exact (@lem1982763 (term198 m) (real_of_int m) term131). Qed.
Lemma lem2615454 (m : int) : (term472 m) = (term473 m).
Proof. exact (@lem1982713 term131 (real_of_int m)). Qed.
Lemma lem2615456 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615457 : term47 = term128.
Proof. exact (@lem2615456 term48). Qed.
Lemma lem2615459 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2615460 : term131 = term132.
Proof. exact (@lem2615459 term48). Qed.
Lemma lem2615461 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615462 : term452 = term453.
Proof. exact (MK_COMB (@lem2615461) (@lem2615460)). Qed.
Lemma lem2615463 : term454 = term455.
Proof. exact (MK_COMB (@lem2615462) (@lem2615457)). Qed.
Lemma lem2615464 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2615466 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615467 : term420 = term426.
Proof. exact (@lem2615466 (NUMERAL 0) term48). Qed.
Lemma lem2615468 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615469 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615470 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615469 h1) (fun h1 : term426 = True => @lem2615468)). Qed.
Lemma lem2615471 : term426 = True.
Proof. exact (EQ_MP (@lem2615470) (@lem2615468)). Qed.
Lemma lem2615472 : term420 = True.
Proof. exact (TRANS (@lem2615467) (@lem2615471)). Qed.
Lemma lem2615473 : True = term420.
Proof. exact (SYM (@lem2615472)). Qed.
Lemma lem2615474 : term420.
Proof. exact (EQ_MP (@lem2615473) (@lem0)). Qed.
Lemma lem2615475 : term457.
Proof. exact (@lem2615464 (@lem2615474)). Qed.
Lemma lem2615477 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615478 : term420 = term426.
Proof. exact (@lem2615477 (NUMERAL 0) term48). Qed.
Lemma lem2615479 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615480 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615481 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615480 h1) (fun h1 : term426 = True => @lem2615479)). Qed.
Lemma lem2615482 : term426 = True.
Proof. exact (EQ_MP (@lem2615481) (@lem2615479)). Qed.
Lemma lem2615483 : term420 = True.
Proof. exact (TRANS (@lem2615478) (@lem2615482)). Qed.
Lemma lem2615484 : True = term420.
Proof. exact (SYM (@lem2615483)). Qed.
Lemma lem2615485 : term420.
Proof. exact (EQ_MP (@lem2615484) (@lem0)). Qed.
Lemma lem2615486 : term458.
Proof. exact (@lem2615475 (@lem2615485)). Qed.
Lemma lem2615488 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615489 : term420 = term426.
Proof. exact (@lem2615488 (NUMERAL 0) term48). Qed.
Lemma lem2615490 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615491 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615492 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615491 h1) (fun h1 : term426 = True => @lem2615490)). Qed.
Lemma lem2615493 : term426 = True.
Proof. exact (EQ_MP (@lem2615492) (@lem2615490)). Qed.
Lemma lem2615494 : term420 = True.
Proof. exact (TRANS (@lem2615489) (@lem2615493)). Qed.
Lemma lem2615495 : True = term420.
Proof. exact (SYM (@lem2615494)). Qed.
Lemma lem2615496 : term420.
Proof. exact (EQ_MP (@lem2615495) (@lem0)). Qed.
Lemma lem2615497 : term459.
Proof. exact (@lem2615486 (@lem2615496)). Qed.
Lemma lem2615499 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615500 : term140 = term141.
Proof. exact (@lem2615499 term48 term48). Qed.
Lemma lem2615501 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615502 : term143 = term48.
Proof. exact (EQ_MP (@lem2615501) (@lem940073)). Qed.
Lemma lem2615503 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615504 : term141 = term47.
Proof. exact (MK_COMB (@lem2615503) (@lem2615502)). Qed.
Lemma lem2615505 : term140 = term47.
Proof. exact (TRANS (@lem2615500) (@lem2615504)). Qed.
Lemma lem2615507 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2615508 : term135 = term146.
Proof. exact (@lem2615507 term48 term48). Qed.
Lemma lem2615509 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615510 : term143 = term48.
Proof. exact (EQ_MP (@lem2615509) (@lem940073)). Qed.
Lemma lem2615511 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615512 : term141 = term47.
Proof. exact (MK_COMB (@lem2615511) (@lem2615510)). Qed.
Lemma lem2615513 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2615514 : term146 = term131.
Proof. exact (MK_COMB (@lem2615513) (@lem2615512)). Qed.
Lemma lem2615515 : term135 = term131.
Proof. exact (TRANS (@lem2615508) (@lem2615514)). Qed.
Lemma lem2615516 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615517 : term460 = term452.
Proof. exact (MK_COMB (@lem2615516) (@lem2615515)). Qed.
Lemma lem2615518 : term461 = term454.
Proof. exact (MK_COMB (@lem2615517) (@lem2615505)). Qed.
Lemma lem2615520 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2615521 : term454 = term43.
Proof. exact (@lem2615520 term48). Qed.
Lemma lem2615522 : term461 = term43.
Proof. exact (TRANS (@lem2615518) (@lem2615521)). Qed.
Lemma lem2615523 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2615524 : term463 = term464.
Proof. exact (MK_COMB (@lem2615523) (@lem2615522)). Qed.
Lemma lem2615525 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2615526 : term465 = term431.
Proof. exact (MK_COMB (@lem2615524) (@lem2615525)). Qed.
Lemma lem2615528 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615529 : term431 = term43.
Proof. exact (@lem2615528 term48). Qed.
Lemma lem2615530 : term465 = term43.
Proof. exact (TRANS (@lem2615526) (@lem2615529)). Qed.
Lemma lem2615532 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615533 : term140 = term141.
Proof. exact (@lem2615532 term48 term48). Qed.
Lemma lem2615534 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615535 : term143 = term48.
Proof. exact (EQ_MP (@lem2615534) (@lem940073)). Qed.
Lemma lem2615536 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615537 : term141 = term47.
Proof. exact (MK_COMB (@lem2615536) (@lem2615535)). Qed.
Lemma lem2615538 : term140 = term47.
Proof. exact (TRANS (@lem2615533) (@lem2615537)). Qed.
Lemma lem2615539 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2615540 : term466 = term431.
Proof. exact (MK_COMB (@lem2615539) (@lem2615538)). Qed.
Lemma lem2615542 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615543 : term431 = term43.
Proof. exact (@lem2615542 term48). Qed.
Lemma lem2615544 : term466 = term43.
Proof. exact (TRANS (@lem2615540) (@lem2615543)). Qed.
Lemma lem2615545 : term43 = term466.
Proof. exact (SYM (@lem2615544)). Qed.
Lemma lem2615546 : term465 = term466.
Proof. exact (TRANS (@lem2615530) (@lem2615545)). Qed.
Lemma lem2615547 : term455 = term243.
Proof. exact (@lem2615497 (@lem2615546)). Qed.
Lemma lem2615548 : term454 = term243.
Proof. exact (TRANS (@lem2615463) (@lem2615547)). Qed.
Lemma lem2615550 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2615551 : term243 = term43.
Proof. exact (@lem2615550 term43). Qed.
Lemma lem2615552 : term454 = term43.
Proof. exact (TRANS (@lem2615548) (@lem2615551)). Qed.
Lemma lem2615553 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2615554 : term467 = term464.
Proof. exact (MK_COMB (@lem2615553) (@lem2615552)). Qed.
Lemma lem2615555 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2615556 (m : int) : (term473 m) = (term474 m).
Proof. exact (MK_COMB (@lem2615554) (@lem2615555 m)). Qed.
Lemma lem2615557 (m : int) : (term472 m) = (term474 m).
Proof. exact (TRANS (@lem2615454 m) (@lem2615556 m)). Qed.
Lemma lem2615558 (m : int) : (term474 m) = term43.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2615559 (m : int) : (term472 m) = term43.
Proof. exact (TRANS (@lem2615557 m) (@lem2615558 m)). Qed.
Lemma lem2615560 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2615561 (m : int) : (term475 m) = term45.
Proof. exact (MK_COMB (@lem2615560) (@lem2615559 m)). Qed.
Lemma lem2615562 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2615563 (m : int) : (term471 m) = term476.
Proof. exact (MK_COMB (@lem2615561 m) (@lem2615562)). Qed.
Lemma lem2615564 (m : int) : (term534 m) = term476.
Proof. exact (TRANS (@lem2615453 m) (@lem2615563 m)). Qed.
Lemma lem2615565 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2615566 (m : int) : (term534 m) = term131.
Proof. exact (TRANS (@lem2615564 m) (@lem2615565)). Qed.
Lemma lem2615567 (n : int) (m : int) : (term579 n m) = term476.
Proof. exact (MK_COMB (@lem2615452 m n) (@lem2615566 m)). Qed.
Lemma lem2615568 (n : int) (m : int) : (term578 n m) = term476.
Proof. exact (TRANS (@lem2615344 n m) (@lem2615567 n m)). Qed.
Lemma lem2615569 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2615570 (n : int) (m : int) : (term578 n m) = term131.
Proof. exact (TRANS (@lem2615568 n m) (@lem2615569)). Qed.
Lemma lem2615571 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2615572 (n : int) (m : int) : (term580 n m) = term478.
Proof. exact (MK_COMB (@lem2615571) (@lem2615570 n m)). Qed.
Lemma lem2615573 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2615574 (n : int) (m : int) : (term577 n m) = term479.
Proof. exact (MK_COMB (@lem2615572 n m) (@lem2615573)). Qed.
Lemma lem2615575 (m : int) (n : int) (h1 : term414 m n) : term479.
Proof. exact (EQ_MP (@lem2615574 n m) (@lem2615343 m n h1)). Qed.
Lemma lem2615577 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2615578 : term479 = term480.
Proof. exact (@lem2615577 term43 term131). Qed.
Lemma lem2615580 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2615581 : term131 = term132.
Proof. exact (@lem2615580 term48). Qed.
Lemma lem2615583 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615584 : term43 = term243.
Proof. exact (@lem2615583 (NUMERAL 0)). Qed.
Lemma lem2615585 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2615586 : term481 = term482.
Proof. exact (MK_COMB (@lem2615585) (@lem2615584)). Qed.
Lemma lem2615587 : term480 = term483.
Proof. exact (MK_COMB (@lem2615586) (@lem2615581)). Qed.
Lemma lem2615588 : term484.
Proof. exact (@lem1980026 term43 term47 term131 term47). Qed.
Lemma lem2615590 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615591 : term420 = term426.
Proof. exact (@lem2615590 (NUMERAL 0) term48). Qed.
Lemma lem2615592 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615593 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615594 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615593 h1) (fun h1 : term426 = True => @lem2615592)). Qed.
Lemma lem2615595 : term426 = True.
Proof. exact (EQ_MP (@lem2615594) (@lem2615592)). Qed.
Lemma lem2615596 : term420 = True.
Proof. exact (TRANS (@lem2615591) (@lem2615595)). Qed.
Lemma lem2615597 : True = term420.
Proof. exact (SYM (@lem2615596)). Qed.
Lemma lem2615598 : term420.
Proof. exact (EQ_MP (@lem2615597) (@lem0)). Qed.
Lemma lem2615599 : term485.
Proof. exact (@lem2615588 (@lem2615598)). Qed.
Lemma lem2615601 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2615602 : term420 = term426.
Proof. exact (@lem2615601 (NUMERAL 0) term48). Qed.
Lemma lem2615603 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615604 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2615605 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615604 h1) (fun h1 : term426 = True => @lem2615603)). Qed.
Lemma lem2615606 : term426 = True.
Proof. exact (EQ_MP (@lem2615605) (@lem2615603)). Qed.
Lemma lem2615607 : term420 = True.
Proof. exact (TRANS (@lem2615602) (@lem2615606)). Qed.
Lemma lem2615608 : True = term420.
Proof. exact (SYM (@lem2615607)). Qed.
Lemma lem2615609 : term420.
Proof. exact (EQ_MP (@lem2615608) (@lem0)). Qed.
Lemma lem2615610 : term483 = term486.
Proof. exact (@lem2615599 (@lem2615609)). Qed.
Lemma lem2615612 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2615613 : term135 = term146.
Proof. exact (@lem2615612 term48 term48). Qed.
Lemma lem2615614 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615615 : term143 = term48.
Proof. exact (EQ_MP (@lem2615614) (@lem940073)). Qed.
Lemma lem2615616 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615617 : term141 = term47.
Proof. exact (MK_COMB (@lem2615616) (@lem2615615)). Qed.
Lemma lem2615618 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2615619 : term146 = term131.
Proof. exact (MK_COMB (@lem2615618) (@lem2615617)). Qed.
Lemma lem2615620 : term135 = term131.
Proof. exact (TRANS (@lem2615613) (@lem2615619)). Qed.
Lemma lem2615622 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2615623 : term431 = term43.
Proof. exact (@lem2615622 term48). Qed.
Lemma lem2615624 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2615625 : term487 = term481.
Proof. exact (MK_COMB (@lem2615624) (@lem2615623)). Qed.
Lemma lem2615626 : term486 = term480.
Proof. exact (MK_COMB (@lem2615625) (@lem2615620)). Qed.
Lemma lem2615628 (m : nat) (n : nat) : (term488 m n) = (term489 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2615629 : term480 = term490.
Proof. exact (@lem2615628 (NUMERAL 0) term48). Qed.
Lemma lem2615630 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2615631 (h1 : term427 = (BIT1 0)) : (term48 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2615632 : (term427 = (BIT1 0)) = ((term48 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2615631 h1) (fun h1 : (term48 = (NUMERAL 0)) = False => @lem2615630)). Qed.
Lemma lem2615633 : (term48 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2615632) (@lem2615630)). Qed.
Lemma lem2615634 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2615635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2615636 : term491 = (and True).
Proof. exact (MK_COMB (@lem2615635) (@lem2615634)). Qed.
Lemma lem2615637 : term490 = (True /\ False).
Proof. exact (MK_COMB (@lem2615636) (@lem2615633)). Qed.
Lemma lem2615639 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2615640 : term490 = False.
Proof. exact (TRANS (@lem2615637) (@lem2615639)). Qed.
Lemma lem2615641 : term480 = False.
Proof. exact (TRANS (@lem2615629) (@lem2615640)). Qed.
Lemma lem2615642 : term486 = False.
Proof. exact (TRANS (@lem2615626) (@lem2615641)). Qed.
Lemma lem2615643 : term483 = False.
Proof. exact (TRANS (@lem2615610) (@lem2615642)). Qed.
Lemma lem2615644 : term480 = False.
Proof. exact (TRANS (@lem2615587) (@lem2615643)). Qed.
Lemma lem2615645 : term479 = False.
Proof. exact (TRANS (@lem2615578) (@lem2615644)). Qed.
Lemma lem2615646 (m : int) (n : int) (h1 : term414 m n) : False.
Proof. exact (EQ_MP (@lem2615645) (@lem2615575 m n h1)). Qed.
Lemma lem2615647 (m : int) (n : int) (h1 : term415 m n) : False.
Proof. exact (or_elim (@lem2614156 m n h1) (fun h0 : term384 m n => @lem2614901 m n h0) (fun h0 : term414 m n => @lem2615646 m n h0)). Qed.
Lemma lem2615648 (m : int) (n : int) (h1 : term418 m n) : False.
Proof. exact (or_elim (@lem2613223 m n h1) (fun h0 : term371 n m => @lem2614155 n m h0) (fun h0 : term415 m n => @lem2615647 m n h0)). Qed.
Lemma lem2615649 (m : int) (n : int) (h1 : term206 m n) : term206 m n.
Proof. exact (h1). Qed.
Lemma lem2615650 (m : int) (n : int) (h1 : term206 m n) : term418 m n.
Proof. exact (EQ_MP (@lem2613222 m n) (@lem2615649 m n h1)). Qed.
Lemma lem2615651 (m : int) (n : int) (h1 : term206 m n) : (term418 m n) = False.
Proof. exact (prop_ext (fun h2 : term418 m n => @lem2615648 m n h2) (fun h2 : False => @lem2615650 m n h1)). Qed.
Lemma lem2615652 (m : int) (n : int) (h1 : term206 m n) : False.
Proof. exact (EQ_MP (@lem2615651 m n h1) (@lem2615650 m n h1)). Qed.
Lemma lem2615653 (n : int) (m : int) (h1 : term121 n m) : term121 n m.
Proof. exact (h1). Qed.
Lemma lem2615654 (n : int) (m : int) (h1 : term121 n m) : term206 m n.
Proof. exact (EQ_MP (@lem2612174 m n) (@lem2615653 n m h1)). Qed.
Lemma lem2615655 (n : int) (m : int) (h1 : term121 n m) : (term206 m n) = False.
Proof. exact (prop_ext (fun h2 : term206 m n => @lem2615652 m n h2) (fun h2 : False => @lem2615654 n m h1)). Qed.
Lemma lem2615656 (n : int) (m : int) (h1 : term121 n m) : False.
Proof. exact (EQ_MP (@lem2615655 n m h1) (@lem2615654 n m h1)). Qed.
Lemma lem2615657 (n : int) (m : int) : term581 n m.
Proof. exact (fun h0 : term121 n m => @lem2615656 n m h0). Qed.
Lemma lem2615658 (n : int) (m : int) : term582 n m.
Proof. exact (@lem1386578 (term583 n m)). Qed.
Lemma lem2615661 (n : int) (m : int) : term583 n m.
Proof. exact (@lem2615658 n m (@lem2615657 n m)). Qed.
Lemma lem2615662 (n : int) (m : int) : (term119 n m) = (term26 n m).
Proof. exact (SYM (@lem2611862 n m)). Qed.
Lemma lem2615663 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2615664 (n : int) (m : int) : (term583 n m) = (term17 n m).
Proof. exact (MK_COMB (@lem2615663) (@lem2615662 n m)). Qed.
Lemma lem2615665 (n : int) (m : int) : term17 n m.
Proof. exact (EQ_MP (@lem2615664 n m) (@lem2615661 n m)). Qed.
Lemma lem2615666 (n : int) (m : int) : term18 n m.
Proof. exact (EQ_MP (@lem2611681 n m) (@lem2615665 n m)). Qed.
Lemma lem2615667 (n : int) (m : int) (h1 : term18 n m) : term18 n m.
Proof. exact (h1). Qed.
Lemma lem2615668 (m : int) (n : int) (h1 : term27 m n) : term27 m n.
Proof. exact (h1). Qed.
Lemma lem2615669 (n : int) (m : int) (h1 : term27 m n) (h2 : term18 n m) : term28 n m.
Proof. exact (@lem2615667 n m h2 (@lem2615668 m n h1)). Qed.
Lemma lem2615670 (m : int) (n : int) (h1 : term27 m n) : term584 n m.
Proof. exact (fun h0 : term18 n m => @lem2615669 n m h1 h0). Qed.
Lemma lem2615671 (n : int) (m : int) (h1 : term18 n m) : term18 n m.
Proof. exact (h1). Qed.
Lemma lem2615672 (n : int) (m : int) (h1 : term27 m n) (h2 : term18 n m) : term28 n m.
Proof. exact (@lem2615670 m n h1 (@lem2615671 n m h2)). Qed.
Lemma lem2615673 (n : int) (m : int) (h1 : term18 n m) : term18 n m.
Proof. exact (fun h0 : term27 m n => @lem2615672 n m h0 h1). Qed.
Lemma lem2615674 (n : int) (m : int) : term585 n m.
Proof. exact (fun h0 : term18 n m => @lem2615673 n m h0). Qed.
Lemma lem2615676 (x : int) (a : int) : (term586 x a) = ((term587 x a) = (term588 x a)).
Proof. exact (@lem2318604 ((term587 x a) = (term588 x a))). Qed.
Lemma lem2615694 (x : int) (a : int) : (term589 x a) = (term590 x a).
Proof. exact (@lem17045 (term591 a x) (int_le x a)). Qed.
Lemma lem2615700 (x : int) (a : int) : (term592 x a) = (term592 x a).
Proof. exact (eq_refl (term592 x a)). Qed.
Lemma lem2615702 (x : int) (a : int) : (term593 x a) = (term593 x a).
Proof. exact (eq_refl (term593 x a)). Qed.
Lemma lem2615703 (x : int) (a : int) : (term594 x a) = (term595 x a).
Proof. exact (MK_COMB (@lem2615702 x a) (@lem2615694 x a)). Qed.
Lemma lem2615704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2615705 (x : int) (a : int) : (term596 x a) = (term597 x a).
Proof. exact (MK_COMB (@lem2615704) (@lem2615703 x a)). Qed.
Lemma lem2615706 (x : int) (a : int) : (term598 x a) = (term599 x a).
Proof. exact (MK_COMB (@lem2615705 x a) (@lem2615700 x a)). Qed.
Lemma lem2615707 (x : int) (a : int) : (term600 x a) = (term598 x a).
Proof. exact (@lem17646 (term587 x a) (term588 x a)). Qed.
Lemma lem2615737 (x : int) (a : int) : (term600 x a) = (term599 x a).
Proof. exact (TRANS (@lem2615707 x a) (@lem2615706 x a)). Qed.
Lemma lem2615740 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2615741 (x : int) (a : int) : (term587 x a) = (term601 x a).
Proof. exact (@lem2615740 (int_abs x) a). Qed.
Lemma lem2615743 (x : int) : (term61 x) = (term62 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2615744 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2615745 (x : int) : (term602 x) = (term603 x).
Proof. exact (MK_COMB (@lem2615744) (@lem2615743 x)). Qed.
Lemma lem2615746 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2615747 (x : int) (a : int) : (term601 x a) = (term604 x a).
Proof. exact (MK_COMB (@lem2615745 x) (@lem2615746 a)). Qed.
Lemma lem2615749 (x : int) (a : int) : (term587 x a) = (term604 x a).
Proof. exact (TRANS (@lem2615741 x a) (@lem2615747 x a)). Qed.
Lemma lem2615751 (y : int) (x : int) : (term75 x y) = (term29 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2615752 (x : int) (a : int) : (term605 a x) = (term606 x a).
Proof. exact (@lem2615751 x (int_neg a)). Qed.
Lemma lem2615754 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2615755 (x : int) (a : int) : (term606 x a) = (term607 x a).
Proof. exact (@lem2615754 (term80 x) (int_neg a)). Qed.
Lemma lem2615757 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2615758 (x : int) : (term81 x) = (term82 x).
Proof. exact (@lem2615757 x term40). Qed.
Lemma lem2615760 (n : nat) : (term41 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2615761 : term46 = term47.
Proof. exact (@lem2615760 term48). Qed.
Lemma lem2615762 (x : int) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2615763 (x : int) : (term82 x) = (term84 x).
Proof. exact (MK_COMB (@lem2615762 x) (@lem2615761)). Qed.
Lemma lem2615764 (x : int) : (term81 x) = (term84 x).
Proof. exact (TRANS (@lem2615758 x) (@lem2615763 x)). Qed.
Lemma lem2615765 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2615766 (x : int) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem2615765) (@lem2615764 x)). Qed.
Lemma lem2615768 (x : int) : (term90 x) = (term91 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2615769 (a : int) : (term90 a) = (term91 a).
Proof. exact (@lem2615768 a). Qed.
Lemma lem2615770 (x : int) (a : int) : (term607 x a) = (term608 x a).
Proof. exact (MK_COMB (@lem2615766 x) (@lem2615769 a)). Qed.
Lemma lem2615771 (x : int) (a : int) : (term606 x a) = (term608 x a).
Proof. exact (TRANS (@lem2615755 x a) (@lem2615770 x a)). Qed.
Lemma lem2615772 (x : int) (a : int) : (term605 a x) = (term608 x a).
Proof. exact (TRANS (@lem2615752 x a) (@lem2615771 x a)). Qed.
Lemma lem2615774 (y : int) (x : int) : (term75 x y) = (term29 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2615775 (a : int) (x : int) : (term75 x a) = (term29 a x).
Proof. exact (@lem2615774 a x). Qed.
Lemma lem2615777 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2615778 (a : int) (x : int) : (term29 a x) = (term609 a x).
Proof. exact (@lem2615777 (term80 a) x). Qed.
Lemma lem2615780 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2615781 (a : int) : (term81 a) = (term82 a).
Proof. exact (@lem2615780 a term40). Qed.
Lemma lem2615783 (n : nat) : (term41 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2615784 : term46 = term47.
Proof. exact (@lem2615783 term48). Qed.
Lemma lem2615785 (a : int) : (term83 a) = (term83 a).
Proof. exact (eq_refl (term83 a)). Qed.
Lemma lem2615786 (a : int) : (term82 a) = (term84 a).
Proof. exact (MK_COMB (@lem2615785 a) (@lem2615784)). Qed.
Lemma lem2615787 (a : int) : (term81 a) = (term84 a).
Proof. exact (TRANS (@lem2615781 a) (@lem2615786 a)). Qed.
Lemma lem2615788 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2615789 (a : int) : (term85 a) = (term86 a).
Proof. exact (MK_COMB (@lem2615788) (@lem2615787 a)). Qed.
Lemma lem2615790 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2615791 (a : int) (x : int) : (term609 a x) = (term610 a x).
Proof. exact (MK_COMB (@lem2615789 a) (@lem2615790 x)). Qed.
Lemma lem2615792 (a : int) (x : int) : (term29 a x) = (term610 a x).
Proof. exact (TRANS (@lem2615778 a x) (@lem2615791 a x)). Qed.
Lemma lem2615793 (a : int) (x : int) : (term75 x a) = (term610 a x).
Proof. exact (TRANS (@lem2615775 a x) (@lem2615792 a x)). Qed.
Lemma lem2615794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2615795 (x : int) (a : int) : (term611 a x) = (term612 x a).
Proof. exact (MK_COMB (@lem2615794) (@lem2615772 x a)). Qed.
Lemma lem2615796 (a : int) (x : int) : (term590 x a) = (term613 a x).
Proof. exact (MK_COMB (@lem2615795 x a) (@lem2615793 a x)). Qed.
Lemma lem2615797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2615798 (x : int) (a : int) : (term593 x a) = (term614 x a).
Proof. exact (MK_COMB (@lem2615797) (@lem2615749 x a)). Qed.
Lemma lem2615799 (a : int) (x : int) : (term595 x a) = (term615 a x).
Proof. exact (MK_COMB (@lem2615798 x a) (@lem2615796 a x)). Qed.
Lemma lem2615801 (y : int) (x : int) : (term75 x y) = (term29 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2615802 (a : int) (x : int) : (term616 x a) = (term617 a x).
Proof. exact (@lem2615801 a (int_abs x)). Qed.
Lemma lem2615804 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2615805 (a : int) (x : int) : (term617 a x) = (term618 a x).
Proof. exact (@lem2615804 (term80 a) (int_abs x)). Qed.
Lemma lem2615807 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2615808 (a : int) : (term81 a) = (term82 a).
Proof. exact (@lem2615807 a term40). Qed.
Lemma lem2615810 (n : nat) : (term41 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2615811 : term46 = term47.
Proof. exact (@lem2615810 term48). Qed.
Lemma lem2615812 (a : int) : (term83 a) = (term83 a).
Proof. exact (eq_refl (term83 a)). Qed.
Lemma lem2615813 (a : int) : (term82 a) = (term84 a).
Proof. exact (MK_COMB (@lem2615812 a) (@lem2615811)). Qed.
Lemma lem2615814 (a : int) : (term81 a) = (term84 a).
Proof. exact (TRANS (@lem2615808 a) (@lem2615813 a)). Qed.
Lemma lem2615815 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2615816 (a : int) : (term85 a) = (term86 a).
Proof. exact (MK_COMB (@lem2615815) (@lem2615814 a)). Qed.
Lemma lem2615818 (x : int) : (term61 x) = (term62 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2615819 (a : int) (x : int) : (term618 a x) = (term619 a x).
Proof. exact (MK_COMB (@lem2615816 a) (@lem2615818 x)). Qed.
Lemma lem2615820 (a : int) (x : int) : (term617 a x) = (term619 a x).
Proof. exact (TRANS (@lem2615805 a x) (@lem2615819 a x)). Qed.
Lemma lem2615821 (a : int) (x : int) : (term616 x a) = (term619 a x).
Proof. exact (TRANS (@lem2615802 a x) (@lem2615820 a x)). Qed.
Lemma lem2615824 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2615825 (a : int) (x : int) : (term591 a x) = (term620 a x).
Proof. exact (@lem2615824 (int_neg a) x). Qed.
Lemma lem2615827 (x : int) : (term90 x) = (term91 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2615828 (a : int) : (term90 a) = (term91 a).
Proof. exact (@lem2615827 a). Qed.
Lemma lem2615829 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2615830 (a : int) : (term621 a) = (term622 a).
Proof. exact (MK_COMB (@lem2615829) (@lem2615828 a)). Qed.
Lemma lem2615831 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2615832 (a : int) (x : int) : (term620 a x) = (term623 a x).
Proof. exact (MK_COMB (@lem2615830 a) (@lem2615831 x)). Qed.
Lemma lem2615834 (a : int) (x : int) : (term591 a x) = (term623 a x).
Proof. exact (TRANS (@lem2615825 a x) (@lem2615832 a x)). Qed.
Lemma lem2615837 (x : int) (y : int) : (int_le x y) = (term33 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2615839 (x : int) (a : int) : (int_le x a) = (term33 x a).
Proof. exact (@lem2615837 x a). Qed.
Lemma lem2615840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2615841 (a : int) (x : int) : (term624 a x) = (term625 a x).
Proof. exact (MK_COMB (@lem2615840) (@lem2615834 a x)). Qed.
Lemma lem2615842 (x : int) (a : int) : (term588 x a) = (term626 x a).
Proof. exact (MK_COMB (@lem2615841 a x) (@lem2615839 x a)). Qed.
Lemma lem2615843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2615844 (a : int) (x : int) : (term627 x a) = (term628 a x).
Proof. exact (MK_COMB (@lem2615843) (@lem2615821 a x)). Qed.
Lemma lem2615845 (x : int) (a : int) : (term592 x a) = (term629 x a).
Proof. exact (MK_COMB (@lem2615844 a x) (@lem2615842 x a)). Qed.
Lemma lem2615846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2615847 (a : int) (x : int) : (term597 x a) = (term630 a x).
Proof. exact (MK_COMB (@lem2615846) (@lem2615799 a x)). Qed.
Lemma lem2615848 (x : int) (a : int) : (term599 x a) = (term631 x a).
Proof. exact (MK_COMB (@lem2615847 a x) (@lem2615845 x a)). Qed.
Lemma lem2615849 (x : int) (a : int) : (term600 x a) = (term631 x a).
Proof. exact (TRANS (@lem2615737 x a) (@lem2615848 x a)). Qed.
Lemma lem2615853 (t : Prop) : (term120 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2615909 (x : int) (a : int) : (term632 x a) = (term631 x a).
Proof. exact (@lem2615853 (term631 x a)). Qed.
Lemma lem2615910 (a : int) (x : int) : (term604 x a) = (term633 a x).
Proof. exact (@lem1988287 (real_of_int a) (term62 x)). Qed.
Lemma lem2615918 (a : int) (x : int) : (term634 a x) = (term635 a x).
Proof. exact (@lem1982792 (real_of_int a) (term62 x)). Qed.
Lemma lem2615923 (x : int) (a : int) : (term635 a x) = (term636 x a).
Proof. exact (@lem1982761 (term165 x) (real_of_int a)). Qed.
Lemma lem2615925 (x : int) (a : int) : (term634 a x) = (term636 x a).
Proof. exact (TRANS (@lem2615918 a x) (@lem2615923 x a)). Qed.
Lemma lem2615926 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2615927 (x : int) (a : int) : (term637 a x) = (term638 x a).
Proof. exact (MK_COMB (@lem2615926) (@lem2615925 x a)). Qed.
Lemma lem2615928 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2615929 (x : int) (a : int) : (term633 a x) = (term639 x a).
Proof. exact (MK_COMB (@lem2615927 x a) (@lem2615928)). Qed.
Lemma lem2615930 (x : int) (a : int) : (term604 x a) = (term639 x a).
Proof. exact (TRANS (@lem2615910 a x) (@lem2615929 x a)). Qed.
Lemma lem2615931 (a : int) (x : int) : (term608 x a) = (term640 a x).
Proof. exact (@lem1988287 (term91 a) (term84 x)). Qed.
Lemma lem2615938 (x : int) : (term84 x) = (term84 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem2615945 (a : int) : (term91 a) = (term198 a).
Proof. exact (@lem1982785 (real_of_int a)). Qed.
Lemma lem2615946 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2615947 (a : int) : (term641 a) = (term642 a).
Proof. exact (MK_COMB (@lem2615946) (@lem2615945 a)). Qed.
Lemma lem2615948 (a : int) (x : int) : (term643 a x) = (term644 a x).
Proof. exact (MK_COMB (@lem2615947 a) (@lem2615938 x)). Qed.
Lemma lem2615949 (a : int) (x : int) : (term644 a x) = (term645 a x).
Proof. exact (@lem1982792 (term198 a) (term84 x)). Qed.
Lemma lem2615950 (x : int) : (term175 x) = (term176 x).
Proof. exact (@lem1982781 (real_of_int x) term131 term47). Qed.
Lemma lem2615952 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2615953 : term47 = term128.
Proof. exact (@lem2615952 term48). Qed.
Lemma lem2615955 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2615956 : term131 = term132.
Proof. exact (@lem2615955 term48). Qed.
Lemma lem2615957 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2615958 : term133 = term134.
Proof. exact (MK_COMB (@lem2615957) (@lem2615956)). Qed.
Lemma lem2615959 : term135 = term136.
Proof. exact (MK_COMB (@lem2615958) (@lem2615953)). Qed.
Lemma lem2615960 : term136 = term137.
Proof. exact (@lem1981613 term131 term47 term47 term47). Qed.
Lemma lem2615962 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2615963 : term140 = term141.
Proof. exact (@lem2615962 term48 term48). Qed.
Lemma lem2615964 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615965 : term143 = term48.
Proof. exact (EQ_MP (@lem2615964) (@lem940073)). Qed.
Lemma lem2615966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615967 : term141 = term47.
Proof. exact (MK_COMB (@lem2615966) (@lem2615965)). Qed.
Lemma lem2615968 : term140 = term47.
Proof. exact (TRANS (@lem2615963) (@lem2615967)). Qed.
Lemma lem2615970 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2615971 : term135 = term146.
Proof. exact (@lem2615970 term48 term48). Qed.
Lemma lem2615972 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2615973 : term143 = term48.
Proof. exact (EQ_MP (@lem2615972) (@lem940073)). Qed.
Lemma lem2615974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2615975 : term141 = term47.
Proof. exact (MK_COMB (@lem2615974) (@lem2615973)). Qed.
Lemma lem2615976 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2615977 : term146 = term131.
Proof. exact (MK_COMB (@lem2615976) (@lem2615975)). Qed.
Lemma lem2615978 : term135 = term131.
Proof. exact (TRANS (@lem2615971) (@lem2615977)). Qed.
Lemma lem2615979 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2615980 : term147 = term148.
Proof. exact (MK_COMB (@lem2615979) (@lem2615978)). Qed.
Lemma lem2615981 : term137 = term132.
Proof. exact (MK_COMB (@lem2615980) (@lem2615968)). Qed.
Lemma lem2615982 : term136 = term132.
Proof. exact (TRANS (@lem2615960) (@lem2615981)). Qed.
Lemma lem2615983 : term135 = term132.
Proof. exact (TRANS (@lem2615959) (@lem2615982)). Qed.
Lemma lem2615985 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2615986 : term132 = term131.
Proof. exact (@lem2615985 term131). Qed.
Lemma lem2615987 : term135 = term131.
Proof. exact (TRANS (@lem2615983) (@lem2615986)). Qed.
Lemma lem2615990 (x : int) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem2615991 (x : int) : (term176 x) = (term178 x).
Proof. exact (MK_COMB (@lem2615990 x) (@lem2615987)). Qed.
Lemma lem2615992 (x : int) : (term175 x) = (term178 x).
Proof. exact (TRANS (@lem2615950 x) (@lem2615991 x)). Qed.
Lemma lem2615993 (a : int) : (term177 a) = (term177 a).
Proof. exact (eq_refl (term177 a)). Qed.
Lemma lem2615996 (a : int) (x : int) : (term645 a x) = (term646 a x).
Proof. exact (MK_COMB (@lem2615993 a) (@lem2615992 x)). Qed.
Lemma lem2615997 (a : int) (x : int) : (term644 a x) = (term646 a x).
Proof. exact (TRANS (@lem2615949 a x) (@lem2615996 a x)). Qed.
Lemma lem2615998 (a : int) (x : int) : (term643 a x) = (term646 a x).
Proof. exact (TRANS (@lem2615948 a x) (@lem2615997 a x)). Qed.
Lemma lem2615999 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616000 (a : int) (x : int) : (term647 a x) = (term648 a x).
Proof. exact (MK_COMB (@lem2615999) (@lem2615998 a x)). Qed.
Lemma lem2616001 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616002 (a : int) (x : int) : (term640 a x) = (term649 a x).
Proof. exact (MK_COMB (@lem2616000 a x) (@lem2616001)). Qed.
Lemma lem2616003 (a : int) (x : int) : (term608 x a) = (term649 a x).
Proof. exact (TRANS (@lem2615931 a x) (@lem2616002 a x)). Qed.
Lemma lem2616004 (x : int) (a : int) : (term610 a x) = (term650 x a).
Proof. exact (@lem1988287 (real_of_int x) (term84 a)). Qed.
Lemma lem2616016 (x : int) (a : int) : (term651 x a) = (term652 x a).
Proof. exact (@lem1982792 (real_of_int x) (term84 a)). Qed.
Lemma lem2616017 (a : int) : (term175 a) = (term176 a).
Proof. exact (@lem1982781 (real_of_int a) term131 term47). Qed.
Lemma lem2616019 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616020 : term47 = term128.
Proof. exact (@lem2616019 term48). Qed.
Lemma lem2616022 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616023 : term131 = term132.
Proof. exact (@lem2616022 term48). Qed.
Lemma lem2616024 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616025 : term133 = term134.
Proof. exact (MK_COMB (@lem2616024) (@lem2616023)). Qed.
Lemma lem2616026 : term135 = term136.
Proof. exact (MK_COMB (@lem2616025) (@lem2616020)). Qed.
Lemma lem2616027 : term136 = term137.
Proof. exact (@lem1981613 term131 term47 term47 term47). Qed.
Lemma lem2616029 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616030 : term140 = term141.
Proof. exact (@lem2616029 term48 term48). Qed.
Lemma lem2616031 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616032 : term143 = term48.
Proof. exact (EQ_MP (@lem2616031) (@lem940073)). Qed.
Lemma lem2616033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616034 : term141 = term47.
Proof. exact (MK_COMB (@lem2616033) (@lem2616032)). Qed.
Lemma lem2616035 : term140 = term47.
Proof. exact (TRANS (@lem2616030) (@lem2616034)). Qed.
Lemma lem2616037 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2616038 : term135 = term146.
Proof. exact (@lem2616037 term48 term48). Qed.
Lemma lem2616039 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616040 : term143 = term48.
Proof. exact (EQ_MP (@lem2616039) (@lem940073)). Qed.
Lemma lem2616041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616042 : term141 = term47.
Proof. exact (MK_COMB (@lem2616041) (@lem2616040)). Qed.
Lemma lem2616043 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2616044 : term146 = term131.
Proof. exact (MK_COMB (@lem2616043) (@lem2616042)). Qed.
Lemma lem2616045 : term135 = term131.
Proof. exact (TRANS (@lem2616038) (@lem2616044)). Qed.
Lemma lem2616046 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2616047 : term147 = term148.
Proof. exact (MK_COMB (@lem2616046) (@lem2616045)). Qed.
Lemma lem2616048 : term137 = term132.
Proof. exact (MK_COMB (@lem2616047) (@lem2616035)). Qed.
Lemma lem2616049 : term136 = term132.
Proof. exact (TRANS (@lem2616027) (@lem2616048)). Qed.
Lemma lem2616050 : term135 = term132.
Proof. exact (TRANS (@lem2616026) (@lem2616049)). Qed.
Lemma lem2616052 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2616053 : term132 = term131.
Proof. exact (@lem2616052 term131). Qed.
Lemma lem2616054 : term135 = term131.
Proof. exact (TRANS (@lem2616050) (@lem2616053)). Qed.
Lemma lem2616057 (a : int) : (term177 a) = (term177 a).
Proof. exact (eq_refl (term177 a)). Qed.
Lemma lem2616058 (a : int) : (term176 a) = (term178 a).
Proof. exact (MK_COMB (@lem2616057 a) (@lem2616054)). Qed.
Lemma lem2616059 (a : int) : (term175 a) = (term178 a).
Proof. exact (TRANS (@lem2616017 a) (@lem2616058 a)). Qed.
Lemma lem2616060 (x : int) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2616061 (x : int) (a : int) : (term652 x a) = (term653 x a).
Proof. exact (MK_COMB (@lem2616060 x) (@lem2616059 a)). Qed.
Lemma lem2616066 (a : int) (x : int) : (term653 x a) = (term654 a x).
Proof. exact (@lem1982757 (term198 a) (real_of_int x) term131). Qed.
Lemma lem2616067 (a : int) (x : int) : (term652 x a) = (term654 a x).
Proof. exact (TRANS (@lem2616061 x a) (@lem2616066 a x)). Qed.
Lemma lem2616069 (a : int) (x : int) : (term651 x a) = (term654 a x).
Proof. exact (TRANS (@lem2616016 x a) (@lem2616067 a x)). Qed.
Lemma lem2616070 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616071 (a : int) (x : int) : (term655 x a) = (term656 a x).
Proof. exact (MK_COMB (@lem2616070) (@lem2616069 a x)). Qed.
Lemma lem2616072 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616073 (a : int) (x : int) : (term650 x a) = (term657 a x).
Proof. exact (MK_COMB (@lem2616071 a x) (@lem2616072)). Qed.
Lemma lem2616074 (a : int) (x : int) : (term610 a x) = (term657 a x).
Proof. exact (TRANS (@lem2616004 x a) (@lem2616073 a x)). Qed.
Lemma lem2616075 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2616076 (a : int) (x : int) : (term612 x a) = (term658 a x).
Proof. exact (MK_COMB (@lem2616075) (@lem2616003 a x)). Qed.
Lemma lem2616077 (a : int) (x : int) : (term613 a x) = (term659 a x).
Proof. exact (MK_COMB (@lem2616076 a x) (@lem2616074 a x)). Qed.
Lemma lem2616078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616079 (x : int) (a : int) : (term614 x a) = (term660 x a).
Proof. exact (MK_COMB (@lem2616078) (@lem2615930 x a)). Qed.
Lemma lem2616080 (a : int) (x : int) : (term615 a x) = (term661 a x).
Proof. exact (MK_COMB (@lem2616079 x a) (@lem2616077 a x)). Qed.
Lemma lem2616081 (x : int) (a : int) : (term619 a x) = (term662 x a).
Proof. exact (@lem1988287 (term62 x) (term84 a)). Qed.
Lemma lem2616095 (x : int) (a : int) : (term663 x a) = (term664 x a).
Proof. exact (@lem1982792 (term62 x) (term84 a)). Qed.
Lemma lem2616096 (a : int) : (term175 a) = (term176 a).
Proof. exact (@lem1982781 (real_of_int a) term131 term47). Qed.
Lemma lem2616098 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616099 : term47 = term128.
Proof. exact (@lem2616098 term48). Qed.
Lemma lem2616101 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616102 : term131 = term132.
Proof. exact (@lem2616101 term48). Qed.
Lemma lem2616103 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616104 : term133 = term134.
Proof. exact (MK_COMB (@lem2616103) (@lem2616102)). Qed.
Lemma lem2616105 : term135 = term136.
Proof. exact (MK_COMB (@lem2616104) (@lem2616099)). Qed.
Lemma lem2616106 : term136 = term137.
Proof. exact (@lem1981613 term131 term47 term47 term47). Qed.
Lemma lem2616108 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616109 : term140 = term141.
Proof. exact (@lem2616108 term48 term48). Qed.
Lemma lem2616110 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616111 : term143 = term48.
Proof. exact (EQ_MP (@lem2616110) (@lem940073)). Qed.
Lemma lem2616112 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616113 : term141 = term47.
Proof. exact (MK_COMB (@lem2616112) (@lem2616111)). Qed.
Lemma lem2616114 : term140 = term47.
Proof. exact (TRANS (@lem2616109) (@lem2616113)). Qed.
Lemma lem2616116 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2616117 : term135 = term146.
Proof. exact (@lem2616116 term48 term48). Qed.
Lemma lem2616118 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616119 : term143 = term48.
Proof. exact (EQ_MP (@lem2616118) (@lem940073)). Qed.
Lemma lem2616120 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616121 : term141 = term47.
Proof. exact (MK_COMB (@lem2616120) (@lem2616119)). Qed.
Lemma lem2616122 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2616123 : term146 = term131.
Proof. exact (MK_COMB (@lem2616122) (@lem2616121)). Qed.
Lemma lem2616124 : term135 = term131.
Proof. exact (TRANS (@lem2616117) (@lem2616123)). Qed.
Lemma lem2616125 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2616126 : term147 = term148.
Proof. exact (MK_COMB (@lem2616125) (@lem2616124)). Qed.
Lemma lem2616127 : term137 = term132.
Proof. exact (MK_COMB (@lem2616126) (@lem2616114)). Qed.
Lemma lem2616128 : term136 = term132.
Proof. exact (TRANS (@lem2616106) (@lem2616127)). Qed.
Lemma lem2616129 : term135 = term132.
Proof. exact (TRANS (@lem2616105) (@lem2616128)). Qed.
Lemma lem2616131 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2616132 : term132 = term131.
Proof. exact (@lem2616131 term131). Qed.
Lemma lem2616133 : term135 = term131.
Proof. exact (TRANS (@lem2616129) (@lem2616132)). Qed.
Lemma lem2616136 (a : int) : (term177 a) = (term177 a).
Proof. exact (eq_refl (term177 a)). Qed.
Lemma lem2616137 (a : int) : (term176 a) = (term178 a).
Proof. exact (MK_COMB (@lem2616136 a) (@lem2616133)). Qed.
Lemma lem2616138 (a : int) : (term175 a) = (term178 a).
Proof. exact (TRANS (@lem2616096 a) (@lem2616137 a)). Qed.
Lemma lem2616139 (x : int) : (term109 x) = (term109 x).
Proof. exact (eq_refl (term109 x)). Qed.
Lemma lem2616142 (x : int) (a : int) : (term664 x a) = (term665 x a).
Proof. exact (MK_COMB (@lem2616139 x) (@lem2616138 a)). Qed.
Lemma lem2616144 (x : int) (a : int) : (term663 x a) = (term665 x a).
Proof. exact (TRANS (@lem2616095 x a) (@lem2616142 x a)). Qed.
Lemma lem2616145 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616146 (x : int) (a : int) : (term666 x a) = (term667 x a).
Proof. exact (MK_COMB (@lem2616145) (@lem2616144 x a)). Qed.
Lemma lem2616147 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616148 (x : int) (a : int) : (term662 x a) = (term668 x a).
Proof. exact (MK_COMB (@lem2616146 x a) (@lem2616147)). Qed.
Lemma lem2616149 (x : int) (a : int) : (term619 a x) = (term668 x a).
Proof. exact (TRANS (@lem2616081 x a) (@lem2616148 x a)). Qed.
Lemma lem2616150 (x : int) (a : int) : (term623 a x) = (term669 x a).
Proof. exact (@lem1988287 (real_of_int x) (term91 a)). Qed.
Lemma lem2616157 (a : int) : (term91 a) = (term198 a).
Proof. exact (@lem1982785 (real_of_int a)). Qed.
Lemma lem2616160 (x : int) : (term123 x) = (term123 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem2616161 (x : int) (a : int) : (term670 x a) = (term671 x a).
Proof. exact (MK_COMB (@lem2616160 x) (@lem2616157 a)). Qed.
Lemma lem2616162 (x : int) (a : int) : (term671 x a) = (term672 x a).
Proof. exact (@lem1982792 (real_of_int x) (term198 a)). Qed.
Lemma lem2616163 (a : int) : (term673 a) = (term674 a).
Proof. exact (@lem1982749 term131 term131 (real_of_int a)). Qed.
Lemma lem2616165 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616166 : term131 = term132.
Proof. exact (@lem2616165 term48). Qed.
Lemma lem2616168 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616169 : term131 = term132.
Proof. exact (@lem2616168 term48). Qed.
Lemma lem2616170 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616171 : term133 = term134.
Proof. exact (MK_COMB (@lem2616170) (@lem2616169)). Qed.
Lemma lem2616172 : term344 = term345.
Proof. exact (MK_COMB (@lem2616171) (@lem2616166)). Qed.
Lemma lem2616173 : term345 = term346.
Proof. exact (@lem1981613 term131 term131 term47 term47). Qed.
Lemma lem2616175 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616176 : term140 = term141.
Proof. exact (@lem2616175 term48 term48). Qed.
Lemma lem2616177 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616178 : term143 = term48.
Proof. exact (EQ_MP (@lem2616177) (@lem940073)). Qed.
Lemma lem2616179 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616180 : term141 = term47.
Proof. exact (MK_COMB (@lem2616179) (@lem2616178)). Qed.
Lemma lem2616181 : term140 = term47.
Proof. exact (TRANS (@lem2616176) (@lem2616180)). Qed.
Lemma lem2616183 (m : nat) (n : nat) : (term347 m n) = (term139 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2616184 : term344 = term141.
Proof. exact (@lem2616183 term48 term48). Qed.
Lemma lem2616185 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616186 : term143 = term48.
Proof. exact (EQ_MP (@lem2616185) (@lem940073)). Qed.
Lemma lem2616187 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616188 : term141 = term47.
Proof. exact (MK_COMB (@lem2616187) (@lem2616186)). Qed.
Lemma lem2616189 : term344 = term47.
Proof. exact (TRANS (@lem2616184) (@lem2616188)). Qed.
Lemma lem2616190 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2616191 : term348 = term349.
Proof. exact (MK_COMB (@lem2616190) (@lem2616189)). Qed.
Lemma lem2616192 : term346 = term128.
Proof. exact (MK_COMB (@lem2616191) (@lem2616181)). Qed.
Lemma lem2616193 : term345 = term128.
Proof. exact (TRANS (@lem2616173) (@lem2616192)). Qed.
Lemma lem2616194 : term344 = term128.
Proof. exact (TRANS (@lem2616172) (@lem2616193)). Qed.
Lemma lem2616196 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2616197 : term128 = term47.
Proof. exact (@lem2616196 term47). Qed.
Lemma lem2616198 : term344 = term47.
Proof. exact (TRANS (@lem2616194) (@lem2616197)). Qed.
Lemma lem2616199 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616200 : term350 = term351.
Proof. exact (MK_COMB (@lem2616199) (@lem2616198)). Qed.
Lemma lem2616201 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2616202 (a : int) : (term674 a) = (term187 a).
Proof. exact (MK_COMB (@lem2616200) (@lem2616201 a)). Qed.
Lemma lem2616203 (a : int) : (term673 a) = (term187 a).
Proof. exact (TRANS (@lem2616163 a) (@lem2616202 a)). Qed.
Lemma lem2616204 (a : int) : (term187 a) = (real_of_int a).
Proof. exact (@lem1982709 (real_of_int a)). Qed.
Lemma lem2616205 (a : int) : (term673 a) = (real_of_int a).
Proof. exact (TRANS (@lem2616203 a) (@lem2616204 a)). Qed.
Lemma lem2616206 (x : int) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2616207 (x : int) (a : int) : (term672 x a) = (term37 x a).
Proof. exact (MK_COMB (@lem2616206 x) (@lem2616205 a)). Qed.
Lemma lem2616208 (a : int) (x : int) : (term37 x a) = (term37 a x).
Proof. exact (@lem1982761 (real_of_int a) (real_of_int x)). Qed.
Lemma lem2616209 (a : int) (x : int) : (term672 x a) = (term37 a x).
Proof. exact (TRANS (@lem2616207 x a) (@lem2616208 a x)). Qed.
Lemma lem2616210 (a : int) (x : int) : (term671 x a) = (term37 a x).
Proof. exact (TRANS (@lem2616162 x a) (@lem2616209 a x)). Qed.
Lemma lem2616211 (a : int) (x : int) : (term670 x a) = (term37 a x).
Proof. exact (TRANS (@lem2616161 x a) (@lem2616210 a x)). Qed.
Lemma lem2616212 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616213 (a : int) (x : int) : (term675 x a) = (term676 a x).
Proof. exact (MK_COMB (@lem2616212) (@lem2616211 a x)). Qed.
Lemma lem2616214 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616215 (a : int) (x : int) : (term669 x a) = (term677 a x).
Proof. exact (MK_COMB (@lem2616213 a x) (@lem2616214)). Qed.
Lemma lem2616216 (a : int) (x : int) : (term623 a x) = (term677 a x).
Proof. exact (TRANS (@lem2616150 x a) (@lem2616215 a x)). Qed.
Lemma lem2616217 (a : int) (x : int) : (term33 x a) = (term678 a x).
Proof. exact (@lem1988287 (real_of_int a) (real_of_int x)). Qed.
Lemma lem2616230 (a : int) (x : int) : (term679 a x) = (term401 a x).
Proof. exact (@lem1982792 (real_of_int a) (real_of_int x)). Qed.
Lemma lem2616231 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616232 (a : int) (x : int) : (term680 a x) = (term681 a x).
Proof. exact (MK_COMB (@lem2616231) (@lem2616230 a x)). Qed.
Lemma lem2616233 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616234 (a : int) (x : int) : (term678 a x) = (term682 a x).
Proof. exact (MK_COMB (@lem2616232 a x) (@lem2616233)). Qed.
Lemma lem2616235 (a : int) (x : int) : (term33 x a) = (term682 a x).
Proof. exact (TRANS (@lem2616217 a x) (@lem2616234 a x)). Qed.
Lemma lem2616236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616237 (a : int) (x : int) : (term625 a x) = (term683 a x).
Proof. exact (MK_COMB (@lem2616236) (@lem2616216 a x)). Qed.
Lemma lem2616238 (a : int) (x : int) : (term626 x a) = (term684 a x).
Proof. exact (MK_COMB (@lem2616237 a x) (@lem2616235 a x)). Qed.
Lemma lem2616239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616240 (x : int) (a : int) : (term628 a x) = (term685 x a).
Proof. exact (MK_COMB (@lem2616239) (@lem2616149 x a)). Qed.
Lemma lem2616241 (a : int) (x : int) : (term629 x a) = (term686 a x).
Proof. exact (MK_COMB (@lem2616240 x a) (@lem2616238 a x)). Qed.
Lemma lem2616242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2616243 (a : int) (x : int) : (term630 a x) = (term687 a x).
Proof. exact (MK_COMB (@lem2616242) (@lem2616080 a x)). Qed.
Lemma lem2616244 (a : int) (x : int) : (term631 x a) = (term688 a x).
Proof. exact (MK_COMB (@lem2616243 a x) (@lem2616241 a x)). Qed.
Lemma lem2616251 (a : int) (x : int) : (term632 x a) = (term688 a x).
Proof. exact (TRANS (@lem2615909 x a) (@lem2616244 a x)). Qed.
Lemma lem2616264 (a : int) (x : int) : (term686 a x) = (term686 a x).
Proof. exact (eq_refl (term686 a x)). Qed.
Lemma lem2616281 (a : int) (x : int) : (term661 a x) = (term689 a x).
Proof. exact (@lem19158 (term649 a x) (term639 x a) (term657 a x)). Qed.
Lemma lem2616282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2616283 (a : int) (x : int) : (term687 a x) = (term690 a x).
Proof. exact (MK_COMB (@lem2616282) (@lem2616281 a x)). Qed.
Lemma lem2616284 (a : int) (x : int) : (term688 a x) = (term691 a x).
Proof. exact (MK_COMB (@lem2616283 a x) (@lem2616264 a x)). Qed.
Lemma lem2616285 (a : int) (x : int) : (term632 x a) = (term691 a x).
Proof. exact (TRANS (@lem2616251 a x) (@lem2616284 a x)). Qed.
Lemma lem2616287 (a : real) (x : real) (r : real) : (term692 x a r) = (term208 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2616288 (a : int) (x : int) : (term639 x a) = (term693 a x).
Proof. exact (@lem2616287 (real_of_int a) (real_of_int x) term43). Qed.
Lemma lem2616295 (x : int) : (term187 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2616298 (a : int) : (term83 a) = (term83 a).
Proof. exact (eq_refl (term83 a)). Qed.
Lemma lem2616301 (a : int) (x : int) : (term694 a x) = (term37 a x).
Proof. exact (MK_COMB (@lem2616298 a) (@lem2616295 x)). Qed.
Lemma lem2616302 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616303 (a : int) (x : int) : (term695 a x) = (term676 a x).
Proof. exact (MK_COMB (@lem2616302) (@lem2616301 a x)). Qed.
Lemma lem2616304 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616305 (a : int) (x : int) : (term696 a x) = (term677 a x).
Proof. exact (MK_COMB (@lem2616303 a x) (@lem2616304)). Qed.
Lemma lem2616324 (a : int) (x : int) : (term697 a x) = (term697 a x).
Proof. exact (eq_refl (term697 a x)). Qed.
Lemma lem2616325 (a : int) (x : int) : (term693 a x) = (term698 a x).
Proof. exact (MK_COMB (@lem2616324 a x) (@lem2616305 a x)). Qed.
Lemma lem2616326 (a : int) (x : int) : (term639 x a) = (term698 a x).
Proof. exact (TRANS (@lem2616288 a x) (@lem2616325 a x)). Qed.
Lemma lem2616327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616328 (a : int) (x : int) : (term660 x a) = (term699 a x).
Proof. exact (MK_COMB (@lem2616327) (@lem2616326 a x)). Qed.
Lemma lem2616329 (a : int) (x : int) : (term649 a x) = (term649 a x).
Proof. exact (eq_refl (term649 a x)). Qed.
Lemma lem2616332 (a : int) (x : int) : (term700 a x) = (term701 a x).
Proof. exact (MK_COMB (@lem2616328 a x) (@lem2616329 a x)). Qed.
Lemma lem2616334 (a : real) (x : real) (r : real) : (term692 x a r) = (term208 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2616335 (a : int) (x : int) : (term639 x a) = (term693 a x).
Proof. exact (@lem2616334 (real_of_int a) (real_of_int x) term43). Qed.
Lemma lem2616342 (x : int) : (term187 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2616345 (a : int) : (term83 a) = (term83 a).
Proof. exact (eq_refl (term83 a)). Qed.
Lemma lem2616348 (a : int) (x : int) : (term694 a x) = (term37 a x).
Proof. exact (MK_COMB (@lem2616345 a) (@lem2616342 x)). Qed.
Lemma lem2616349 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616350 (a : int) (x : int) : (term695 a x) = (term676 a x).
Proof. exact (MK_COMB (@lem2616349) (@lem2616348 a x)). Qed.
Lemma lem2616351 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616352 (a : int) (x : int) : (term696 a x) = (term677 a x).
Proof. exact (MK_COMB (@lem2616350 a x) (@lem2616351)). Qed.
Lemma lem2616371 (a : int) (x : int) : (term697 a x) = (term697 a x).
Proof. exact (eq_refl (term697 a x)). Qed.
Lemma lem2616372 (a : int) (x : int) : (term693 a x) = (term698 a x).
Proof. exact (MK_COMB (@lem2616371 a x) (@lem2616352 a x)). Qed.
Lemma lem2616373 (a : int) (x : int) : (term639 x a) = (term698 a x).
Proof. exact (TRANS (@lem2616335 a x) (@lem2616372 a x)). Qed.
Lemma lem2616374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616375 (a : int) (x : int) : (term660 x a) = (term699 a x).
Proof. exact (MK_COMB (@lem2616374) (@lem2616373 a x)). Qed.
Lemma lem2616376 (a : int) (x : int) : (term657 a x) = (term657 a x).
Proof. exact (eq_refl (term657 a x)). Qed.
Lemma lem2616379 (a : int) (x : int) : (term702 a x) = (term703 a x).
Proof. exact (MK_COMB (@lem2616375 a x) (@lem2616376 a x)). Qed.
Lemma lem2616380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2616381 (a : int) (x : int) : (term704 a x) = (term705 a x).
Proof. exact (MK_COMB (@lem2616380) (@lem2616332 a x)). Qed.
Lemma lem2616382 (a : int) (x : int) : (term689 a x) = (term706 a x).
Proof. exact (MK_COMB (@lem2616381 a x) (@lem2616379 a x)). Qed.
Lemma lem2616384 (a : int) (x : int) : (term707 a x) = (term686 a x).
Proof. exact (eq_refl (term707 a x)). Qed.
Lemma lem2616385 (a : int) (x : int) : (term686 a x) = (term707 a x).
Proof. exact (SYM (@lem2616384 a x)). Qed.
Lemma lem2616386 (a : int) (x : int) : (term707 a x) = (term708 a x).
Proof. exact (@lem1482981 (term709 a x) (real_of_int x)). Qed.
Lemma lem2616387 (a : int) (x : int) : (term686 a x) = (term708 a x).
Proof. exact (TRANS (@lem2616385 a x) (@lem2616386 a x)). Qed.
Lemma lem2616388 (a : int) (x : int) : (term710 a x) = (term711 a x).
Proof. exact (eq_refl (term710 a x)). Qed.
Lemma lem2616389 (x : int) : (term227 x) = (term227 x).
Proof. exact (eq_refl (term227 x)). Qed.
Lemma lem2616390 (a : int) (x : int) : (term712 a x) = (term713 a x).
Proof. exact (MK_COMB (@lem2616389 x) (@lem2616388 a x)). Qed.
Lemma lem2616391 (a : int) (x : int) : (term714 a x) = (term715 a x).
Proof. exact (eq_refl (term714 a x)). Qed.
Lemma lem2616392 (x : int) : (term232 x) = (term232 x).
Proof. exact (eq_refl (term232 x)). Qed.
Lemma lem2616393 (a : int) (x : int) : (term716 a x) = (term717 a x).
Proof. exact (MK_COMB (@lem2616392 x) (@lem2616391 a x)). Qed.
Lemma lem2616394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2616395 (a : int) (x : int) : (term718 a x) = (term719 a x).
Proof. exact (MK_COMB (@lem2616394) (@lem2616393 a x)). Qed.
Lemma lem2616396 (a : int) (x : int) : (term708 a x) = (term720 a x).
Proof. exact (MK_COMB (@lem2616395 a x) (@lem2616390 a x)). Qed.
Lemma lem2616397 (a : int) (x : int) : (term721 a x) = (term721 a x).
Proof. exact (eq_refl (term721 a x)). Qed.
Lemma lem2616398 (a : int) (x : int) : ((term686 a x) = (term708 a x)) = ((term686 a x) = (term720 a x)).
Proof. exact (MK_COMB (@lem2616397 a x) (@lem2616396 a x)). Qed.
Lemma lem2616399 (a : int) (x : int) : (term686 a x) = (term720 a x).
Proof. exact (EQ_MP (@lem2616398 a x) (@lem2616387 a x)). Qed.
Lemma lem2616400 (x : int) : (term239 x) = (term240 x).
Proof. exact (@lem1988291 (real_of_int x) term43). Qed.
Lemma lem2616406 (x : int) : (term241 x) = (term242 x).
Proof. exact (@lem1982792 (real_of_int x) term43). Qed.
Lemma lem2616408 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616409 : term43 = term243.
Proof. exact (@lem2616408 (NUMERAL 0)). Qed.
Lemma lem2616411 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616412 : term131 = term132.
Proof. exact (@lem2616411 term48). Qed.
Lemma lem2616413 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616414 : term133 = term134.
Proof. exact (MK_COMB (@lem2616413) (@lem2616412)). Qed.
Lemma lem2616415 : term244 = term245.
Proof. exact (MK_COMB (@lem2616414) (@lem2616409)). Qed.
Lemma lem2616416 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2616418 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616419 : term140 = term141.
Proof. exact (@lem2616418 term48 term48). Qed.
Lemma lem2616420 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616421 : term143 = term48.
Proof. exact (EQ_MP (@lem2616420) (@lem940073)). Qed.
Lemma lem2616422 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616423 : term141 = term47.
Proof. exact (MK_COMB (@lem2616422) (@lem2616421)). Qed.
Lemma lem2616424 : term140 = term47.
Proof. exact (TRANS (@lem2616419) (@lem2616423)). Qed.
Lemma lem2616426 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2616427 : term244 = term43.
Proof. exact (@lem2616426 term48). Qed.
Lemma lem2616428 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2616429 : term248 = term249.
Proof. exact (MK_COMB (@lem2616428) (@lem2616427)). Qed.
Lemma lem2616430 : term246 = term243.
Proof. exact (MK_COMB (@lem2616429) (@lem2616424)). Qed.
Lemma lem2616431 : term245 = term243.
Proof. exact (TRANS (@lem2616416) (@lem2616430)). Qed.
Lemma lem2616432 : term244 = term243.
Proof. exact (TRANS (@lem2616415) (@lem2616431)). Qed.
Lemma lem2616434 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2616435 : term243 = term43.
Proof. exact (@lem2616434 term43). Qed.
Lemma lem2616436 : term244 = term43.
Proof. exact (TRANS (@lem2616432) (@lem2616435)). Qed.
Lemma lem2616437 (x : int) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2616438 (x : int) : (term242 x) = (term250 x).
Proof. exact (MK_COMB (@lem2616437 x) (@lem2616436)). Qed.
Lemma lem2616439 (x : int) : (term250 x) = (real_of_int x).
Proof. exact (@lem1982723 (real_of_int x)). Qed.
Lemma lem2616440 (x : int) : (term242 x) = (real_of_int x).
Proof. exact (TRANS (@lem2616438 x) (@lem2616439 x)). Qed.
Lemma lem2616442 (x : int) : (term241 x) = (real_of_int x).
Proof. exact (TRANS (@lem2616406 x) (@lem2616440 x)). Qed.
Lemma lem2616443 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616444 (x : int) : (term251 x) = (term252 x).
Proof. exact (MK_COMB (@lem2616443) (@lem2616442 x)). Qed.
Lemma lem2616445 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616446 (x : int) : (term240 x) = (term239 x).
Proof. exact (MK_COMB (@lem2616444 x) (@lem2616445)). Qed.
Lemma lem2616447 (x : int) : (term239 x) = (term239 x).
Proof. exact (TRANS (@lem2616400 x) (@lem2616446 x)). Qed.
Lemma lem2616448 (x : int) (a : int) : (term722 x a) = (term723 x a).
Proof. exact (@lem1988291 (term653 x a) term43). Qed.
Lemma lem2616449 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616472 (a : int) (x : int) : (term653 x a) = (term654 a x).
Proof. exact (@lem1982757 (term198 a) (real_of_int x) term131). Qed.
Lemma lem2616473 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2616474 (a : int) (x : int) : (term724 x a) = (term725 a x).
Proof. exact (MK_COMB (@lem2616473) (@lem2616472 a x)). Qed.
Lemma lem2616475 (a : int) (x : int) : (term726 x a) = (term727 a x).
Proof. exact (MK_COMB (@lem2616474 a x) (@lem2616449)). Qed.
Lemma lem2616476 (a : int) (x : int) : (term727 a x) = (term728 a x).
Proof. exact (@lem1982792 (term654 a x) term43). Qed.
Lemma lem2616478 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616479 : term43 = term243.
Proof. exact (@lem2616478 (NUMERAL 0)). Qed.
Lemma lem2616481 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616482 : term131 = term132.
Proof. exact (@lem2616481 term48). Qed.
Lemma lem2616483 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616484 : term133 = term134.
Proof. exact (MK_COMB (@lem2616483) (@lem2616482)). Qed.
Lemma lem2616485 : term244 = term245.
Proof. exact (MK_COMB (@lem2616484) (@lem2616479)). Qed.
Lemma lem2616486 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2616488 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616489 : term140 = term141.
Proof. exact (@lem2616488 term48 term48). Qed.
Lemma lem2616490 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616491 : term143 = term48.
Proof. exact (EQ_MP (@lem2616490) (@lem940073)). Qed.
Lemma lem2616492 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616493 : term141 = term47.
Proof. exact (MK_COMB (@lem2616492) (@lem2616491)). Qed.
Lemma lem2616494 : term140 = term47.
Proof. exact (TRANS (@lem2616489) (@lem2616493)). Qed.
Lemma lem2616496 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2616497 : term244 = term43.
Proof. exact (@lem2616496 term48). Qed.
Lemma lem2616498 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2616499 : term248 = term249.
Proof. exact (MK_COMB (@lem2616498) (@lem2616497)). Qed.
Lemma lem2616500 : term246 = term243.
Proof. exact (MK_COMB (@lem2616499) (@lem2616494)). Qed.
Lemma lem2616501 : term245 = term243.
Proof. exact (TRANS (@lem2616486) (@lem2616500)). Qed.
Lemma lem2616502 : term244 = term243.
Proof. exact (TRANS (@lem2616485) (@lem2616501)). Qed.
Lemma lem2616504 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2616505 : term243 = term43.
Proof. exact (@lem2616504 term43). Qed.
Lemma lem2616506 : term244 = term43.
Proof. exact (TRANS (@lem2616502) (@lem2616505)). Qed.
Lemma lem2616507 (a : int) (x : int) : (term729 a x) = (term729 a x).
Proof. exact (eq_refl (term729 a x)). Qed.
Lemma lem2616508 (a : int) (x : int) : (term728 a x) = (term730 a x).
Proof. exact (MK_COMB (@lem2616507 a x) (@lem2616506)). Qed.
Lemma lem2616509 (a : int) (x : int) : (term730 a x) = (term654 a x).
Proof. exact (@lem1982723 (term654 a x)). Qed.
Lemma lem2616510 (a : int) (x : int) : (term728 a x) = (term654 a x).
Proof. exact (TRANS (@lem2616508 a x) (@lem2616509 a x)). Qed.
Lemma lem2616511 (a : int) (x : int) : (term727 a x) = (term654 a x).
Proof. exact (TRANS (@lem2616476 a x) (@lem2616510 a x)). Qed.
Lemma lem2616512 (a : int) (x : int) : (term726 x a) = (term654 a x).
Proof. exact (TRANS (@lem2616475 a x) (@lem2616511 a x)). Qed.
Lemma lem2616513 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616514 (a : int) (x : int) : (term731 x a) = (term656 a x).
Proof. exact (MK_COMB (@lem2616513) (@lem2616512 a x)). Qed.
Lemma lem2616515 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616516 (a : int) (x : int) : (term723 x a) = (term657 a x).
Proof. exact (MK_COMB (@lem2616514 a x) (@lem2616515)). Qed.
Lemma lem2616517 (a : int) (x : int) : (term722 x a) = (term657 a x).
Proof. exact (TRANS (@lem2616448 x a) (@lem2616516 a x)). Qed.
Lemma lem2616518 (a : int) (x : int) : (term677 a x) = (term732 a x).
Proof. exact (@lem1988291 (term37 a x) term43). Qed.
Lemma lem2616530 (a : int) (x : int) : (term733 a x) = (term734 a x).
Proof. exact (@lem1982792 (term37 a x) term43). Qed.
Lemma lem2616532 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616533 : term43 = term243.
Proof. exact (@lem2616532 (NUMERAL 0)). Qed.
Lemma lem2616535 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616536 : term131 = term132.
Proof. exact (@lem2616535 term48). Qed.
Lemma lem2616537 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616538 : term133 = term134.
Proof. exact (MK_COMB (@lem2616537) (@lem2616536)). Qed.
Lemma lem2616539 : term244 = term245.
Proof. exact (MK_COMB (@lem2616538) (@lem2616533)). Qed.
Lemma lem2616540 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2616542 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616543 : term140 = term141.
Proof. exact (@lem2616542 term48 term48). Qed.
Lemma lem2616544 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616545 : term143 = term48.
Proof. exact (EQ_MP (@lem2616544) (@lem940073)). Qed.
Lemma lem2616546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616547 : term141 = term47.
Proof. exact (MK_COMB (@lem2616546) (@lem2616545)). Qed.
Lemma lem2616548 : term140 = term47.
Proof. exact (TRANS (@lem2616543) (@lem2616547)). Qed.
Lemma lem2616550 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2616551 : term244 = term43.
Proof. exact (@lem2616550 term48). Qed.
Lemma lem2616552 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2616553 : term248 = term249.
Proof. exact (MK_COMB (@lem2616552) (@lem2616551)). Qed.
Lemma lem2616554 : term246 = term243.
Proof. exact (MK_COMB (@lem2616553) (@lem2616548)). Qed.
Lemma lem2616555 : term245 = term243.
Proof. exact (TRANS (@lem2616540) (@lem2616554)). Qed.
Lemma lem2616556 : term244 = term243.
Proof. exact (TRANS (@lem2616539) (@lem2616555)). Qed.
Lemma lem2616558 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2616559 : term243 = term43.
Proof. exact (@lem2616558 term43). Qed.
Lemma lem2616560 : term244 = term43.
Proof. exact (TRANS (@lem2616556) (@lem2616559)). Qed.
Lemma lem2616561 (a : int) (x : int) : (term735 a x) = (term735 a x).
Proof. exact (eq_refl (term735 a x)). Qed.
Lemma lem2616562 (a : int) (x : int) : (term734 a x) = (term736 a x).
Proof. exact (MK_COMB (@lem2616561 a x) (@lem2616560)). Qed.
Lemma lem2616563 (a : int) (x : int) : (term736 a x) = (term37 a x).
Proof. exact (@lem1982723 (term37 a x)). Qed.
Lemma lem2616564 (a : int) (x : int) : (term734 a x) = (term37 a x).
Proof. exact (TRANS (@lem2616562 a x) (@lem2616563 a x)). Qed.
Lemma lem2616566 (a : int) (x : int) : (term733 a x) = (term37 a x).
Proof. exact (TRANS (@lem2616530 a x) (@lem2616564 a x)). Qed.
Lemma lem2616567 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616568 (a : int) (x : int) : (term737 a x) = (term676 a x).
Proof. exact (MK_COMB (@lem2616567) (@lem2616566 a x)). Qed.
Lemma lem2616569 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616570 (a : int) (x : int) : (term732 a x) = (term677 a x).
Proof. exact (MK_COMB (@lem2616568 a x) (@lem2616569)). Qed.
Lemma lem2616571 (a : int) (x : int) : (term677 a x) = (term677 a x).
Proof. exact (TRANS (@lem2616518 a x) (@lem2616570 a x)). Qed.
Lemma lem2616572 (a : int) (x : int) : (term682 a x) = (term738 a x).
Proof. exact (@lem1988291 (term401 a x) term43). Qed.
Lemma lem2616590 (a : int) (x : int) : (term739 a x) = (term740 a x).
Proof. exact (@lem1982792 (term401 a x) term43). Qed.
Lemma lem2616592 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616593 : term43 = term243.
Proof. exact (@lem2616592 (NUMERAL 0)). Qed.
Lemma lem2616595 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616596 : term131 = term132.
Proof. exact (@lem2616595 term48). Qed.
Lemma lem2616597 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616598 : term133 = term134.
Proof. exact (MK_COMB (@lem2616597) (@lem2616596)). Qed.
Lemma lem2616599 : term244 = term245.
Proof. exact (MK_COMB (@lem2616598) (@lem2616593)). Qed.
Lemma lem2616600 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2616602 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616603 : term140 = term141.
Proof. exact (@lem2616602 term48 term48). Qed.
Lemma lem2616604 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616605 : term143 = term48.
Proof. exact (EQ_MP (@lem2616604) (@lem940073)). Qed.
Lemma lem2616606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616607 : term141 = term47.
Proof. exact (MK_COMB (@lem2616606) (@lem2616605)). Qed.
Lemma lem2616608 : term140 = term47.
Proof. exact (TRANS (@lem2616603) (@lem2616607)). Qed.
Lemma lem2616610 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2616611 : term244 = term43.
Proof. exact (@lem2616610 term48). Qed.
Lemma lem2616612 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2616613 : term248 = term249.
Proof. exact (MK_COMB (@lem2616612) (@lem2616611)). Qed.
Lemma lem2616614 : term246 = term243.
Proof. exact (MK_COMB (@lem2616613) (@lem2616608)). Qed.
Lemma lem2616615 : term245 = term243.
Proof. exact (TRANS (@lem2616600) (@lem2616614)). Qed.
Lemma lem2616616 : term244 = term243.
Proof. exact (TRANS (@lem2616599) (@lem2616615)). Qed.
Lemma lem2616618 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2616619 : term243 = term43.
Proof. exact (@lem2616618 term43). Qed.
Lemma lem2616620 : term244 = term43.
Proof. exact (TRANS (@lem2616616) (@lem2616619)). Qed.
Lemma lem2616621 (a : int) (x : int) : (term741 a x) = (term741 a x).
Proof. exact (eq_refl (term741 a x)). Qed.
Lemma lem2616622 (a : int) (x : int) : (term740 a x) = (term742 a x).
Proof. exact (MK_COMB (@lem2616621 a x) (@lem2616620)). Qed.
Lemma lem2616623 (a : int) (x : int) : (term742 a x) = (term401 a x).
Proof. exact (@lem1982723 (term401 a x)). Qed.
Lemma lem2616624 (a : int) (x : int) : (term740 a x) = (term401 a x).
Proof. exact (TRANS (@lem2616622 a x) (@lem2616623 a x)). Qed.
Lemma lem2616626 (a : int) (x : int) : (term739 a x) = (term401 a x).
Proof. exact (TRANS (@lem2616590 a x) (@lem2616624 a x)). Qed.
Lemma lem2616627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616628 (a : int) (x : int) : (term743 a x) = (term681 a x).
Proof. exact (MK_COMB (@lem2616627) (@lem2616626 a x)). Qed.
Lemma lem2616629 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616630 (a : int) (x : int) : (term738 a x) = (term682 a x).
Proof. exact (MK_COMB (@lem2616628 a x) (@lem2616629)). Qed.
Lemma lem2616631 (a : int) (x : int) : (term682 a x) = (term682 a x).
Proof. exact (TRANS (@lem2616572 a x) (@lem2616630 a x)). Qed.
Lemma lem2616632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616633 (a : int) (x : int) : (term683 a x) = (term683 a x).
Proof. exact (MK_COMB (@lem2616632) (@lem2616571 a x)). Qed.
Lemma lem2616634 (a : int) (x : int) : (term684 a x) = (term684 a x).
Proof. exact (MK_COMB (@lem2616633 a x) (@lem2616631 a x)). Qed.
Lemma lem2616635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616636 (a : int) (x : int) : (term744 x a) = (term745 a x).
Proof. exact (MK_COMB (@lem2616635) (@lem2616517 a x)). Qed.
Lemma lem2616637 (a : int) (x : int) : (term715 a x) = (term746 a x).
Proof. exact (MK_COMB (@lem2616636 a x) (@lem2616634 a x)). Qed.
Lemma lem2616638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616639 (x : int) : (term232 x) = (term232 x).
Proof. exact (MK_COMB (@lem2616638) (@lem2616447 x)). Qed.
Lemma lem2616640 (a : int) (x : int) : (term717 a x) = (term747 a x).
Proof. exact (MK_COMB (@lem2616639 x) (@lem2616637 a x)). Qed.
Lemma lem2616641 (x : int) : (term290 x) = (term291 x).
Proof. exact (@lem1988289 term43 (real_of_int x)). Qed.
Lemma lem2616647 (x : int) : (term292 x) = (term293 x).
Proof. exact (@lem1982792 term43 (real_of_int x)). Qed.
Lemma lem2616652 (x : int) : (term293 x) = (term198 x).
Proof. exact (@lem1982721 (term198 x)). Qed.
Lemma lem2616654 (x : int) : (term292 x) = (term198 x).
Proof. exact (TRANS (@lem2616647 x) (@lem2616652 x)). Qed.
Lemma lem2616655 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2616656 (x : int) : (term294 x) = (term295 x).
Proof. exact (MK_COMB (@lem2616655) (@lem2616654 x)). Qed.
Lemma lem2616657 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616658 (x : int) : (term291 x) = (term296 x).
Proof. exact (MK_COMB (@lem2616656 x) (@lem2616657)). Qed.
Lemma lem2616659 (x : int) : (term290 x) = (term296 x).
Proof. exact (TRANS (@lem2616641 x) (@lem2616658 x)). Qed.
Lemma lem2616660 (x : int) (a : int) : (term748 x a) = (term749 x a).
Proof. exact (@lem1988291 (term750 x a) term43). Qed.
Lemma lem2616661 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616674 (a : int) : (term178 a) = (term178 a).
Proof. exact (eq_refl (term178 a)). Qed.
Lemma lem2616681 (x : int) : (term91 x) = (term198 x).
Proof. exact (@lem1982785 (real_of_int x)). Qed.
Lemma lem2616682 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2616683 (x : int) : (term751 x) = (term177 x).
Proof. exact (MK_COMB (@lem2616682) (@lem2616681 x)). Qed.
Lemma lem2616684 (x : int) (a : int) : (term750 x a) = (term646 x a).
Proof. exact (MK_COMB (@lem2616683 x) (@lem2616674 a)). Qed.
Lemma lem2616689 (a : int) (x : int) : (term646 x a) = (term646 a x).
Proof. exact (@lem1982757 (term198 a) (term198 x) term131). Qed.
Lemma lem2616690 (a : int) (x : int) : (term750 x a) = (term646 a x).
Proof. exact (TRANS (@lem2616684 x a) (@lem2616689 a x)). Qed.
Lemma lem2616691 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2616692 (a : int) (x : int) : (term752 x a) = (term753 a x).
Proof. exact (MK_COMB (@lem2616691) (@lem2616690 a x)). Qed.
Lemma lem2616693 (a : int) (x : int) : (term754 x a) = (term755 a x).
Proof. exact (MK_COMB (@lem2616692 a x) (@lem2616661)). Qed.
Lemma lem2616694 (a : int) (x : int) : (term755 a x) = (term756 a x).
Proof. exact (@lem1982792 (term646 a x) term43). Qed.
Lemma lem2616696 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616697 : term43 = term243.
Proof. exact (@lem2616696 (NUMERAL 0)). Qed.
Lemma lem2616699 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616700 : term131 = term132.
Proof. exact (@lem2616699 term48). Qed.
Lemma lem2616701 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616702 : term133 = term134.
Proof. exact (MK_COMB (@lem2616701) (@lem2616700)). Qed.
Lemma lem2616703 : term244 = term245.
Proof. exact (MK_COMB (@lem2616702) (@lem2616697)). Qed.
Lemma lem2616704 : term245 = term246.
Proof. exact (@lem1981613 term131 term43 term47 term47). Qed.
Lemma lem2616706 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616707 : term140 = term141.
Proof. exact (@lem2616706 term48 term48). Qed.
Lemma lem2616708 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616709 : term143 = term48.
Proof. exact (EQ_MP (@lem2616708) (@lem940073)). Qed.
Lemma lem2616710 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616711 : term141 = term47.
Proof. exact (MK_COMB (@lem2616710) (@lem2616709)). Qed.
Lemma lem2616712 : term140 = term47.
Proof. exact (TRANS (@lem2616707) (@lem2616711)). Qed.
Lemma lem2616714 (x : nat) : (term247 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2616715 : term244 = term43.
Proof. exact (@lem2616714 term48). Qed.
Lemma lem2616716 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2616717 : term248 = term249.
Proof. exact (MK_COMB (@lem2616716) (@lem2616715)). Qed.
Lemma lem2616718 : term246 = term243.
Proof. exact (MK_COMB (@lem2616717) (@lem2616712)). Qed.
Lemma lem2616719 : term245 = term243.
Proof. exact (TRANS (@lem2616704) (@lem2616718)). Qed.
Lemma lem2616720 : term244 = term243.
Proof. exact (TRANS (@lem2616703) (@lem2616719)). Qed.
Lemma lem2616722 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2616723 : term243 = term43.
Proof. exact (@lem2616722 term43). Qed.
Lemma lem2616724 : term244 = term43.
Proof. exact (TRANS (@lem2616720) (@lem2616723)). Qed.
Lemma lem2616725 (a : int) (x : int) : (term757 a x) = (term757 a x).
Proof. exact (eq_refl (term757 a x)). Qed.
Lemma lem2616726 (a : int) (x : int) : (term756 a x) = (term758 a x).
Proof. exact (MK_COMB (@lem2616725 a x) (@lem2616724)). Qed.
Lemma lem2616727 (a : int) (x : int) : (term758 a x) = (term646 a x).
Proof. exact (@lem1982723 (term646 a x)). Qed.
Lemma lem2616728 (a : int) (x : int) : (term756 a x) = (term646 a x).
Proof. exact (TRANS (@lem2616726 a x) (@lem2616727 a x)). Qed.
Lemma lem2616729 (a : int) (x : int) : (term755 a x) = (term646 a x).
Proof. exact (TRANS (@lem2616694 a x) (@lem2616728 a x)). Qed.
Lemma lem2616730 (a : int) (x : int) : (term754 x a) = (term646 a x).
Proof. exact (TRANS (@lem2616693 a x) (@lem2616729 a x)). Qed.
Lemma lem2616731 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616732 (a : int) (x : int) : (term759 x a) = (term648 a x).
Proof. exact (MK_COMB (@lem2616731) (@lem2616730 a x)). Qed.
Lemma lem2616733 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616734 (a : int) (x : int) : (term749 x a) = (term649 a x).
Proof. exact (MK_COMB (@lem2616732 a x) (@lem2616733)). Qed.
Lemma lem2616735 (a : int) (x : int) : (term748 x a) = (term649 a x).
Proof. exact (TRANS (@lem2616660 x a) (@lem2616734 a x)). Qed.
Lemma lem2616736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616737 (a : int) (x : int) : (term683 a x) = (term683 a x).
Proof. exact (MK_COMB (@lem2616736) (@lem2616571 a x)). Qed.
Lemma lem2616738 (a : int) (x : int) : (term684 a x) = (term684 a x).
Proof. exact (MK_COMB (@lem2616737 a x) (@lem2616631 a x)). Qed.
Lemma lem2616739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616740 (a : int) (x : int) : (term760 x a) = (term761 a x).
Proof. exact (MK_COMB (@lem2616739) (@lem2616735 a x)). Qed.
Lemma lem2616741 (a : int) (x : int) : (term711 a x) = (term762 a x).
Proof. exact (MK_COMB (@lem2616740 a x) (@lem2616738 a x)). Qed.
Lemma lem2616742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2616743 (x : int) : (term227 x) = (term369 x).
Proof. exact (MK_COMB (@lem2616742) (@lem2616659 x)). Qed.
Lemma lem2616744 (a : int) (x : int) : (term713 a x) = (term763 a x).
Proof. exact (MK_COMB (@lem2616743 x) (@lem2616741 a x)). Qed.
Lemma lem2616745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2616746 (a : int) (x : int) : (term719 a x) = (term764 a x).
Proof. exact (MK_COMB (@lem2616745) (@lem2616640 a x)). Qed.
Lemma lem2616747 (a : int) (x : int) : (term720 a x) = (term765 a x).
Proof. exact (MK_COMB (@lem2616746 a x) (@lem2616744 a x)). Qed.
Lemma lem2616759 (a : int) (x : int) : (term686 a x) = (term765 a x).
Proof. exact (TRANS (@lem2616399 a x) (@lem2616747 a x)). Qed.
Lemma lem2616760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2616761 (a : int) (x : int) : (term690 a x) = (term766 a x).
Proof. exact (MK_COMB (@lem2616760) (@lem2616382 a x)). Qed.
Lemma lem2616762 (a : int) (x : int) : (term691 a x) = (term767 a x).
Proof. exact (MK_COMB (@lem2616761 a x) (@lem2616759 a x)). Qed.
Lemma lem2616763 (a : int) (x : int) (h1 : term767 a x) : term767 a x.
Proof. exact (h1). Qed.
Lemma lem2616764 (a : int) (x : int) (h1 : term706 a x) : term706 a x.
Proof. exact (h1). Qed.
Lemma lem2616765 (a : int) (x : int) (h1 : term701 a x) : term701 a x.
Proof. exact (h1). Qed.
Lemma lem2616766 (a : int) (x : int) (h1 : term701 a x) : term649 a x.
Proof. exact (proj2 (@lem2616765 a x h1)). Qed.
Lemma lem2616767 (a : int) (x : int) (h1 : term701 a x) : term698 a x.
Proof. exact (proj1 (@lem2616765 a x h1)). Qed.
Lemma lem2616768 (a : int) (x : int) (h1 : term701 a x) : term677 a x.
Proof. exact (proj2 (@lem2616767 a x h1)). Qed.
Lemma lem2616771 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2616772 : term419 = term420.
Proof. exact (@lem2616771 term43 term47). Qed.
Lemma lem2616774 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616775 : term47 = term128.
Proof. exact (@lem2616774 term48). Qed.
Lemma lem2616777 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616778 : term43 = term243.
Proof. exact (@lem2616777 (NUMERAL 0)). Qed.
Lemma lem2616779 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2616780 : term421 = term422.
Proof. exact (MK_COMB (@lem2616779) (@lem2616778)). Qed.
Lemma lem2616781 : term420 = term423.
Proof. exact (MK_COMB (@lem2616780) (@lem2616775)). Qed.
Lemma lem2616782 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2616784 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616785 : term420 = term426.
Proof. exact (@lem2616784 (NUMERAL 0) term48). Qed.
Lemma lem2616786 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616787 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616788 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616787 h1) (fun h1 : term426 = True => @lem2616786)). Qed.
Lemma lem2616789 : term426 = True.
Proof. exact (EQ_MP (@lem2616788) (@lem2616786)). Qed.
Lemma lem2616790 : term420 = True.
Proof. exact (TRANS (@lem2616785) (@lem2616789)). Qed.
Lemma lem2616791 : True = term420.
Proof. exact (SYM (@lem2616790)). Qed.
Lemma lem2616792 : term420.
Proof. exact (EQ_MP (@lem2616791) (@lem0)). Qed.
Lemma lem2616793 : term428.
Proof. exact (@lem2616782 (@lem2616792)). Qed.
Lemma lem2616795 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616796 : term420 = term426.
Proof. exact (@lem2616795 (NUMERAL 0) term48). Qed.
Lemma lem2616797 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616798 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616799 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616798 h1) (fun h1 : term426 = True => @lem2616797)). Qed.
Lemma lem2616800 : term426 = True.
Proof. exact (EQ_MP (@lem2616799) (@lem2616797)). Qed.
Lemma lem2616801 : term420 = True.
Proof. exact (TRANS (@lem2616796) (@lem2616800)). Qed.
Lemma lem2616802 : True = term420.
Proof. exact (SYM (@lem2616801)). Qed.
Lemma lem2616803 : term420.
Proof. exact (EQ_MP (@lem2616802) (@lem0)). Qed.
Lemma lem2616804 : term423 = term429.
Proof. exact (@lem2616793 (@lem2616803)). Qed.
Lemma lem2616806 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616807 : term140 = term141.
Proof. exact (@lem2616806 term48 term48). Qed.
Lemma lem2616808 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616809 : term143 = term48.
Proof. exact (EQ_MP (@lem2616808) (@lem940073)). Qed.
Lemma lem2616810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616811 : term141 = term47.
Proof. exact (MK_COMB (@lem2616810) (@lem2616809)). Qed.
Lemma lem2616812 : term140 = term47.
Proof. exact (TRANS (@lem2616807) (@lem2616811)). Qed.
Lemma lem2616814 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2616815 : term431 = term43.
Proof. exact (@lem2616814 term48). Qed.
Lemma lem2616816 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2616817 : term432 = term421.
Proof. exact (MK_COMB (@lem2616816) (@lem2616815)). Qed.
Lemma lem2616818 : term429 = term420.
Proof. exact (MK_COMB (@lem2616817) (@lem2616812)). Qed.
Lemma lem2616820 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616821 : term420 = term426.
Proof. exact (@lem2616820 (NUMERAL 0) term48). Qed.
Lemma lem2616822 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616823 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616824 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616823 h1) (fun h1 : term426 = True => @lem2616822)). Qed.
Lemma lem2616825 : term426 = True.
Proof. exact (EQ_MP (@lem2616824) (@lem2616822)). Qed.
Lemma lem2616826 : term420 = True.
Proof. exact (TRANS (@lem2616821) (@lem2616825)). Qed.
Lemma lem2616827 : term429 = True.
Proof. exact (TRANS (@lem2616818) (@lem2616826)). Qed.
Lemma lem2616828 : term423 = True.
Proof. exact (TRANS (@lem2616804) (@lem2616827)). Qed.
Lemma lem2616829 : term420 = True.
Proof. exact (TRANS (@lem2616781) (@lem2616828)). Qed.
Lemma lem2616830 : term419 = True.
Proof. exact (TRANS (@lem2616772) (@lem2616829)). Qed.
Lemma lem2616831 : True = term419.
Proof. exact (SYM (@lem2616830)). Qed.
Lemma lem2616832 : term419.
Proof. exact (EQ_MP (@lem2616831) (@lem0)). Qed.
Lemma lem2616833 (a : int) (x : int) (h1 : term701 a x) : term768 a x.
Proof. exact (conj (@lem2616832) (@lem2616768 a x h1)). Qed.
Lemma lem2616835 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2616836 (a : int) (x : int) : term769 a x.
Proof. exact (@lem2616835 term47 (term37 a x)). Qed.
Lemma lem2616837 (a : int) (x : int) (h1 : term701 a x) : term770 a x.
Proof. exact (@lem2616836 a x (@lem2616833 a x h1)). Qed.
Lemma lem2616838 (a : int) (x : int) : (term771 a x) = (term37 a x).
Proof. exact (@lem1982733 (term37 a x)). Qed.
Lemma lem2616839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616840 (a : int) (x : int) : (term772 a x) = (term676 a x).
Proof. exact (MK_COMB (@lem2616839) (@lem2616838 a x)). Qed.
Lemma lem2616841 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616842 (a : int) (x : int) : (term770 a x) = (term677 a x).
Proof. exact (MK_COMB (@lem2616840 a x) (@lem2616841)). Qed.
Lemma lem2616843 (a : int) (x : int) (h1 : term701 a x) : term677 a x.
Proof. exact (EQ_MP (@lem2616842 a x) (@lem2616837 a x h1)). Qed.
Lemma lem2616845 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2616846 : term419 = term420.
Proof. exact (@lem2616845 term43 term47). Qed.
Lemma lem2616848 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616849 : term47 = term128.
Proof. exact (@lem2616848 term48). Qed.
Lemma lem2616851 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616852 : term43 = term243.
Proof. exact (@lem2616851 (NUMERAL 0)). Qed.
Lemma lem2616853 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2616854 : term421 = term422.
Proof. exact (MK_COMB (@lem2616853) (@lem2616852)). Qed.
Lemma lem2616855 : term420 = term423.
Proof. exact (MK_COMB (@lem2616854) (@lem2616849)). Qed.
Lemma lem2616856 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2616858 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616859 : term420 = term426.
Proof. exact (@lem2616858 (NUMERAL 0) term48). Qed.
Lemma lem2616860 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616861 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616862 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616861 h1) (fun h1 : term426 = True => @lem2616860)). Qed.
Lemma lem2616863 : term426 = True.
Proof. exact (EQ_MP (@lem2616862) (@lem2616860)). Qed.
Lemma lem2616864 : term420 = True.
Proof. exact (TRANS (@lem2616859) (@lem2616863)). Qed.
Lemma lem2616865 : True = term420.
Proof. exact (SYM (@lem2616864)). Qed.
Lemma lem2616866 : term420.
Proof. exact (EQ_MP (@lem2616865) (@lem0)). Qed.
Lemma lem2616867 : term428.
Proof. exact (@lem2616856 (@lem2616866)). Qed.
Lemma lem2616869 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616870 : term420 = term426.
Proof. exact (@lem2616869 (NUMERAL 0) term48). Qed.
Lemma lem2616871 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616872 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616873 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616872 h1) (fun h1 : term426 = True => @lem2616871)). Qed.
Lemma lem2616874 : term426 = True.
Proof. exact (EQ_MP (@lem2616873) (@lem2616871)). Qed.
Lemma lem2616875 : term420 = True.
Proof. exact (TRANS (@lem2616870) (@lem2616874)). Qed.
Lemma lem2616876 : True = term420.
Proof. exact (SYM (@lem2616875)). Qed.
Lemma lem2616877 : term420.
Proof. exact (EQ_MP (@lem2616876) (@lem0)). Qed.
Lemma lem2616878 : term423 = term429.
Proof. exact (@lem2616867 (@lem2616877)). Qed.
Lemma lem2616880 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616881 : term140 = term141.
Proof. exact (@lem2616880 term48 term48). Qed.
Lemma lem2616882 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616883 : term143 = term48.
Proof. exact (EQ_MP (@lem2616882) (@lem940073)). Qed.
Lemma lem2616884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616885 : term141 = term47.
Proof. exact (MK_COMB (@lem2616884) (@lem2616883)). Qed.
Lemma lem2616886 : term140 = term47.
Proof. exact (TRANS (@lem2616881) (@lem2616885)). Qed.
Lemma lem2616888 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2616889 : term431 = term43.
Proof. exact (@lem2616888 term48). Qed.
Lemma lem2616890 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2616891 : term432 = term421.
Proof. exact (MK_COMB (@lem2616890) (@lem2616889)). Qed.
Lemma lem2616892 : term429 = term420.
Proof. exact (MK_COMB (@lem2616891) (@lem2616886)). Qed.
Lemma lem2616894 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616895 : term420 = term426.
Proof. exact (@lem2616894 (NUMERAL 0) term48). Qed.
Lemma lem2616896 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616897 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616898 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616897 h1) (fun h1 : term426 = True => @lem2616896)). Qed.
Lemma lem2616899 : term426 = True.
Proof. exact (EQ_MP (@lem2616898) (@lem2616896)). Qed.
Lemma lem2616900 : term420 = True.
Proof. exact (TRANS (@lem2616895) (@lem2616899)). Qed.
Lemma lem2616901 : term429 = True.
Proof. exact (TRANS (@lem2616892) (@lem2616900)). Qed.
Lemma lem2616902 : term423 = True.
Proof. exact (TRANS (@lem2616878) (@lem2616901)). Qed.
Lemma lem2616903 : term420 = True.
Proof. exact (TRANS (@lem2616855) (@lem2616902)). Qed.
Lemma lem2616904 : term419 = True.
Proof. exact (TRANS (@lem2616846) (@lem2616903)). Qed.
Lemma lem2616905 : True = term419.
Proof. exact (SYM (@lem2616904)). Qed.
Lemma lem2616906 : term419.
Proof. exact (EQ_MP (@lem2616905) (@lem0)). Qed.
Lemma lem2616907 (a : int) (x : int) (h1 : term701 a x) : term773 a x.
Proof. exact (conj (@lem2616906) (@lem2616766 a x h1)). Qed.
Lemma lem2616909 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2616910 (a : int) (x : int) : term774 a x.
Proof. exact (@lem2616909 term47 (term646 a x)). Qed.
Lemma lem2616911 (a : int) (x : int) (h1 : term701 a x) : term775 a x.
Proof. exact (@lem2616910 a x (@lem2616907 a x h1)). Qed.
Lemma lem2616912 (a : int) (x : int) : (term776 a x) = (term646 a x).
Proof. exact (@lem1982733 (term646 a x)). Qed.
Lemma lem2616913 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2616914 (a : int) (x : int) : (term777 a x) = (term648 a x).
Proof. exact (MK_COMB (@lem2616913) (@lem2616912 a x)). Qed.
Lemma lem2616915 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2616916 (a : int) (x : int) : (term775 a x) = (term649 a x).
Proof. exact (MK_COMB (@lem2616914 a x) (@lem2616915)). Qed.
Lemma lem2616917 (a : int) (x : int) (h1 : term701 a x) : term649 a x.
Proof. exact (EQ_MP (@lem2616916 a x) (@lem2616911 a x h1)). Qed.
Lemma lem2616918 (a : int) (x : int) (h1 : term701 a x) : term778 a x.
Proof. exact (conj (@lem2616917 a x h1) (@lem2616843 a x h1)). Qed.
Lemma lem2616920 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2616921 (a : int) (x : int) : term779 a x.
Proof. exact (@lem2616920 (term646 a x) (term37 a x)). Qed.
Lemma lem2616922 (a : int) (x : int) (h1 : term701 a x) : term780 a x.
Proof. exact (@lem2616921 a x (@lem2616918 a x h1)). Qed.
Lemma lem2616923 (a : int) (x : int) : (term781 a x) = (term782 a x).
Proof. exact (@lem1982753 (term198 a) (real_of_int a) (term178 x) (real_of_int x)). Qed.
Lemma lem2616924 (a : int) : (term472 a) = (term473 a).
Proof. exact (@lem1982713 term131 (real_of_int a)). Qed.
Lemma lem2616926 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2616927 : term47 = term128.
Proof. exact (@lem2616926 term48). Qed.
Lemma lem2616929 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2616930 : term131 = term132.
Proof. exact (@lem2616929 term48). Qed.
Lemma lem2616931 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2616932 : term452 = term453.
Proof. exact (MK_COMB (@lem2616931) (@lem2616930)). Qed.
Lemma lem2616933 : term454 = term455.
Proof. exact (MK_COMB (@lem2616932) (@lem2616927)). Qed.
Lemma lem2616934 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2616936 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616937 : term420 = term426.
Proof. exact (@lem2616936 (NUMERAL 0) term48). Qed.
Lemma lem2616938 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616939 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616940 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616939 h1) (fun h1 : term426 = True => @lem2616938)). Qed.
Lemma lem2616941 : term426 = True.
Proof. exact (EQ_MP (@lem2616940) (@lem2616938)). Qed.
Lemma lem2616942 : term420 = True.
Proof. exact (TRANS (@lem2616937) (@lem2616941)). Qed.
Lemma lem2616943 : True = term420.
Proof. exact (SYM (@lem2616942)). Qed.
Lemma lem2616944 : term420.
Proof. exact (EQ_MP (@lem2616943) (@lem0)). Qed.
Lemma lem2616945 : term457.
Proof. exact (@lem2616934 (@lem2616944)). Qed.
Lemma lem2616947 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616948 : term420 = term426.
Proof. exact (@lem2616947 (NUMERAL 0) term48). Qed.
Lemma lem2616949 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616950 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616951 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616950 h1) (fun h1 : term426 = True => @lem2616949)). Qed.
Lemma lem2616952 : term426 = True.
Proof. exact (EQ_MP (@lem2616951) (@lem2616949)). Qed.
Lemma lem2616953 : term420 = True.
Proof. exact (TRANS (@lem2616948) (@lem2616952)). Qed.
Lemma lem2616954 : True = term420.
Proof. exact (SYM (@lem2616953)). Qed.
Lemma lem2616955 : term420.
Proof. exact (EQ_MP (@lem2616954) (@lem0)). Qed.
Lemma lem2616956 : term458.
Proof. exact (@lem2616945 (@lem2616955)). Qed.
Lemma lem2616958 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2616959 : term420 = term426.
Proof. exact (@lem2616958 (NUMERAL 0) term48). Qed.
Lemma lem2616960 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2616961 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2616962 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2616961 h1) (fun h1 : term426 = True => @lem2616960)). Qed.
Lemma lem2616963 : term426 = True.
Proof. exact (EQ_MP (@lem2616962) (@lem2616960)). Qed.
Lemma lem2616964 : term420 = True.
Proof. exact (TRANS (@lem2616959) (@lem2616963)). Qed.
Lemma lem2616965 : True = term420.
Proof. exact (SYM (@lem2616964)). Qed.
Lemma lem2616966 : term420.
Proof. exact (EQ_MP (@lem2616965) (@lem0)). Qed.
Lemma lem2616967 : term459.
Proof. exact (@lem2616956 (@lem2616966)). Qed.
Lemma lem2616969 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2616970 : term140 = term141.
Proof. exact (@lem2616969 term48 term48). Qed.
Lemma lem2616971 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616972 : term143 = term48.
Proof. exact (EQ_MP (@lem2616971) (@lem940073)). Qed.
Lemma lem2616973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616974 : term141 = term47.
Proof. exact (MK_COMB (@lem2616973) (@lem2616972)). Qed.
Lemma lem2616975 : term140 = term47.
Proof. exact (TRANS (@lem2616970) (@lem2616974)). Qed.
Lemma lem2616977 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2616978 : term135 = term146.
Proof. exact (@lem2616977 term48 term48). Qed.
Lemma lem2616979 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2616980 : term143 = term48.
Proof. exact (EQ_MP (@lem2616979) (@lem940073)). Qed.
Lemma lem2616981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2616982 : term141 = term47.
Proof. exact (MK_COMB (@lem2616981) (@lem2616980)). Qed.
Lemma lem2616983 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2616984 : term146 = term131.
Proof. exact (MK_COMB (@lem2616983) (@lem2616982)). Qed.
Lemma lem2616985 : term135 = term131.
Proof. exact (TRANS (@lem2616978) (@lem2616984)). Qed.
Lemma lem2616986 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2616987 : term460 = term452.
Proof. exact (MK_COMB (@lem2616986) (@lem2616985)). Qed.
Lemma lem2616988 : term461 = term454.
Proof. exact (MK_COMB (@lem2616987) (@lem2616975)). Qed.
Lemma lem2616990 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2616991 : term454 = term43.
Proof. exact (@lem2616990 term48). Qed.
Lemma lem2616992 : term461 = term43.
Proof. exact (TRANS (@lem2616988) (@lem2616991)). Qed.
Lemma lem2616993 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2616994 : term463 = term464.
Proof. exact (MK_COMB (@lem2616993) (@lem2616992)). Qed.
Lemma lem2616995 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2616996 : term465 = term431.
Proof. exact (MK_COMB (@lem2616994) (@lem2616995)). Qed.
Lemma lem2616998 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2616999 : term431 = term43.
Proof. exact (@lem2616998 term48). Qed.
Lemma lem2617000 : term465 = term43.
Proof. exact (TRANS (@lem2616996) (@lem2616999)). Qed.
Lemma lem2617002 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617003 : term140 = term141.
Proof. exact (@lem2617002 term48 term48). Qed.
Lemma lem2617004 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617005 : term143 = term48.
Proof. exact (EQ_MP (@lem2617004) (@lem940073)). Qed.
Lemma lem2617006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617007 : term141 = term47.
Proof. exact (MK_COMB (@lem2617006) (@lem2617005)). Qed.
Lemma lem2617008 : term140 = term47.
Proof. exact (TRANS (@lem2617003) (@lem2617007)). Qed.
Lemma lem2617009 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2617010 : term466 = term431.
Proof. exact (MK_COMB (@lem2617009) (@lem2617008)). Qed.
Lemma lem2617012 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617013 : term431 = term43.
Proof. exact (@lem2617012 term48). Qed.
Lemma lem2617014 : term466 = term43.
Proof. exact (TRANS (@lem2617010) (@lem2617013)). Qed.
Lemma lem2617015 : term43 = term466.
Proof. exact (SYM (@lem2617014)). Qed.
Lemma lem2617016 : term465 = term466.
Proof. exact (TRANS (@lem2617000) (@lem2617015)). Qed.
Lemma lem2617017 : term455 = term243.
Proof. exact (@lem2616967 (@lem2617016)). Qed.
Lemma lem2617018 : term454 = term243.
Proof. exact (TRANS (@lem2616933) (@lem2617017)). Qed.
Lemma lem2617020 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2617021 : term243 = term43.
Proof. exact (@lem2617020 term43). Qed.
Lemma lem2617022 : term454 = term43.
Proof. exact (TRANS (@lem2617018) (@lem2617021)). Qed.
Lemma lem2617023 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617024 : term467 = term464.
Proof. exact (MK_COMB (@lem2617023) (@lem2617022)). Qed.
Lemma lem2617025 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2617026 (a : int) : (term473 a) = (term474 a).
Proof. exact (MK_COMB (@lem2617024) (@lem2617025 a)). Qed.
Lemma lem2617027 (a : int) : (term472 a) = (term474 a).
Proof. exact (TRANS (@lem2616924 a) (@lem2617026 a)). Qed.
Lemma lem2617028 (a : int) : (term474 a) = term43.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2617029 (a : int) : (term472 a) = term43.
Proof. exact (TRANS (@lem2617027 a) (@lem2617028 a)). Qed.
Lemma lem2617030 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617031 (a : int) : (term475 a) = term45.
Proof. exact (MK_COMB (@lem2617030) (@lem2617029 a)). Qed.
Lemma lem2617032 (x : int) : (term470 x) = (term471 x).
Proof. exact (@lem1982759 (term198 x) (real_of_int x) term131). Qed.
Lemma lem2617033 (x : int) : (term472 x) = (term473 x).
Proof. exact (@lem1982713 term131 (real_of_int x)). Qed.
Lemma lem2617035 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617036 : term47 = term128.
Proof. exact (@lem2617035 term48). Qed.
Lemma lem2617038 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2617039 : term131 = term132.
Proof. exact (@lem2617038 term48). Qed.
Lemma lem2617040 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617041 : term452 = term453.
Proof. exact (MK_COMB (@lem2617040) (@lem2617039)). Qed.
Lemma lem2617042 : term454 = term455.
Proof. exact (MK_COMB (@lem2617041) (@lem2617036)). Qed.
Lemma lem2617043 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2617045 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617046 : term420 = term426.
Proof. exact (@lem2617045 (NUMERAL 0) term48). Qed.
Lemma lem2617047 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617048 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617049 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617048 h1) (fun h1 : term426 = True => @lem2617047)). Qed.
Lemma lem2617050 : term426 = True.
Proof. exact (EQ_MP (@lem2617049) (@lem2617047)). Qed.
Lemma lem2617051 : term420 = True.
Proof. exact (TRANS (@lem2617046) (@lem2617050)). Qed.
Lemma lem2617052 : True = term420.
Proof. exact (SYM (@lem2617051)). Qed.
Lemma lem2617053 : term420.
Proof. exact (EQ_MP (@lem2617052) (@lem0)). Qed.
Lemma lem2617054 : term457.
Proof. exact (@lem2617043 (@lem2617053)). Qed.
Lemma lem2617056 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617057 : term420 = term426.
Proof. exact (@lem2617056 (NUMERAL 0) term48). Qed.
Lemma lem2617058 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617059 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617060 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617059 h1) (fun h1 : term426 = True => @lem2617058)). Qed.
Lemma lem2617061 : term426 = True.
Proof. exact (EQ_MP (@lem2617060) (@lem2617058)). Qed.
Lemma lem2617062 : term420 = True.
Proof. exact (TRANS (@lem2617057) (@lem2617061)). Qed.
Lemma lem2617063 : True = term420.
Proof. exact (SYM (@lem2617062)). Qed.
Lemma lem2617064 : term420.
Proof. exact (EQ_MP (@lem2617063) (@lem0)). Qed.
Lemma lem2617065 : term458.
Proof. exact (@lem2617054 (@lem2617064)). Qed.
Lemma lem2617067 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617068 : term420 = term426.
Proof. exact (@lem2617067 (NUMERAL 0) term48). Qed.
Lemma lem2617069 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617070 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617071 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617070 h1) (fun h1 : term426 = True => @lem2617069)). Qed.
Lemma lem2617072 : term426 = True.
Proof. exact (EQ_MP (@lem2617071) (@lem2617069)). Qed.
Lemma lem2617073 : term420 = True.
Proof. exact (TRANS (@lem2617068) (@lem2617072)). Qed.
Lemma lem2617074 : True = term420.
Proof. exact (SYM (@lem2617073)). Qed.
Lemma lem2617075 : term420.
Proof. exact (EQ_MP (@lem2617074) (@lem0)). Qed.
Lemma lem2617076 : term459.
Proof. exact (@lem2617065 (@lem2617075)). Qed.
Lemma lem2617078 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617079 : term140 = term141.
Proof. exact (@lem2617078 term48 term48). Qed.
Lemma lem2617080 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617081 : term143 = term48.
Proof. exact (EQ_MP (@lem2617080) (@lem940073)). Qed.
Lemma lem2617082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617083 : term141 = term47.
Proof. exact (MK_COMB (@lem2617082) (@lem2617081)). Qed.
Lemma lem2617084 : term140 = term47.
Proof. exact (TRANS (@lem2617079) (@lem2617083)). Qed.
Lemma lem2617086 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2617087 : term135 = term146.
Proof. exact (@lem2617086 term48 term48). Qed.
Lemma lem2617088 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617089 : term143 = term48.
Proof. exact (EQ_MP (@lem2617088) (@lem940073)). Qed.
Lemma lem2617090 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617091 : term141 = term47.
Proof. exact (MK_COMB (@lem2617090) (@lem2617089)). Qed.
Lemma lem2617092 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2617093 : term146 = term131.
Proof. exact (MK_COMB (@lem2617092) (@lem2617091)). Qed.
Lemma lem2617094 : term135 = term131.
Proof. exact (TRANS (@lem2617087) (@lem2617093)). Qed.
Lemma lem2617095 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617096 : term460 = term452.
Proof. exact (MK_COMB (@lem2617095) (@lem2617094)). Qed.
Lemma lem2617097 : term461 = term454.
Proof. exact (MK_COMB (@lem2617096) (@lem2617084)). Qed.
Lemma lem2617099 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2617100 : term454 = term43.
Proof. exact (@lem2617099 term48). Qed.
Lemma lem2617101 : term461 = term43.
Proof. exact (TRANS (@lem2617097) (@lem2617100)). Qed.
Lemma lem2617102 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617103 : term463 = term464.
Proof. exact (MK_COMB (@lem2617102) (@lem2617101)). Qed.
Lemma lem2617104 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2617105 : term465 = term431.
Proof. exact (MK_COMB (@lem2617103) (@lem2617104)). Qed.
Lemma lem2617107 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617108 : term431 = term43.
Proof. exact (@lem2617107 term48). Qed.
Lemma lem2617109 : term465 = term43.
Proof. exact (TRANS (@lem2617105) (@lem2617108)). Qed.
Lemma lem2617111 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617112 : term140 = term141.
Proof. exact (@lem2617111 term48 term48). Qed.
Lemma lem2617113 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617114 : term143 = term48.
Proof. exact (EQ_MP (@lem2617113) (@lem940073)). Qed.
Lemma lem2617115 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617116 : term141 = term47.
Proof. exact (MK_COMB (@lem2617115) (@lem2617114)). Qed.
Lemma lem2617117 : term140 = term47.
Proof. exact (TRANS (@lem2617112) (@lem2617116)). Qed.
Lemma lem2617118 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2617119 : term466 = term431.
Proof. exact (MK_COMB (@lem2617118) (@lem2617117)). Qed.
Lemma lem2617121 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617122 : term431 = term43.
Proof. exact (@lem2617121 term48). Qed.
Lemma lem2617123 : term466 = term43.
Proof. exact (TRANS (@lem2617119) (@lem2617122)). Qed.
Lemma lem2617124 : term43 = term466.
Proof. exact (SYM (@lem2617123)). Qed.
Lemma lem2617125 : term465 = term466.
Proof. exact (TRANS (@lem2617109) (@lem2617124)). Qed.
Lemma lem2617126 : term455 = term243.
Proof. exact (@lem2617076 (@lem2617125)). Qed.
Lemma lem2617127 : term454 = term243.
Proof. exact (TRANS (@lem2617042) (@lem2617126)). Qed.
Lemma lem2617129 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2617130 : term243 = term43.
Proof. exact (@lem2617129 term43). Qed.
Lemma lem2617131 : term454 = term43.
Proof. exact (TRANS (@lem2617127) (@lem2617130)). Qed.
Lemma lem2617132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617133 : term467 = term464.
Proof. exact (MK_COMB (@lem2617132) (@lem2617131)). Qed.
Lemma lem2617134 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2617135 (x : int) : (term473 x) = (term474 x).
Proof. exact (MK_COMB (@lem2617133) (@lem2617134 x)). Qed.
Lemma lem2617136 (x : int) : (term472 x) = (term474 x).
Proof. exact (TRANS (@lem2617033 x) (@lem2617135 x)). Qed.
Lemma lem2617137 (x : int) : (term474 x) = term43.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2617138 (x : int) : (term472 x) = term43.
Proof. exact (TRANS (@lem2617136 x) (@lem2617137 x)). Qed.
Lemma lem2617139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617140 (x : int) : (term475 x) = term45.
Proof. exact (MK_COMB (@lem2617139) (@lem2617138 x)). Qed.
Lemma lem2617141 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2617142 (x : int) : (term471 x) = term476.
Proof. exact (MK_COMB (@lem2617140 x) (@lem2617141)). Qed.
Lemma lem2617143 (x : int) : (term470 x) = term476.
Proof. exact (TRANS (@lem2617032 x) (@lem2617142 x)). Qed.
Lemma lem2617144 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2617145 (x : int) : (term470 x) = term131.
Proof. exact (TRANS (@lem2617143 x) (@lem2617144)). Qed.
Lemma lem2617146 (a : int) (x : int) : (term782 a x) = term476.
Proof. exact (MK_COMB (@lem2617031 a) (@lem2617145 x)). Qed.
Lemma lem2617147 (a : int) (x : int) : (term781 a x) = term476.
Proof. exact (TRANS (@lem2616923 a x) (@lem2617146 a x)). Qed.
Lemma lem2617148 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2617149 (a : int) (x : int) : (term781 a x) = term131.
Proof. exact (TRANS (@lem2617147 a x) (@lem2617148)). Qed.
Lemma lem2617150 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2617151 (a : int) (x : int) : (term783 a x) = term478.
Proof. exact (MK_COMB (@lem2617150) (@lem2617149 a x)). Qed.
Lemma lem2617152 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2617153 (a : int) (x : int) : (term780 a x) = term479.
Proof. exact (MK_COMB (@lem2617151 a x) (@lem2617152)). Qed.
Lemma lem2617154 (a : int) (x : int) (h1 : term701 a x) : term479.
Proof. exact (EQ_MP (@lem2617153 a x) (@lem2616922 a x h1)). Qed.
Lemma lem2617156 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2617157 : term479 = term480.
Proof. exact (@lem2617156 term43 term131). Qed.
Lemma lem2617159 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2617160 : term131 = term132.
Proof. exact (@lem2617159 term48). Qed.
Lemma lem2617162 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617163 : term43 = term243.
Proof. exact (@lem2617162 (NUMERAL 0)). Qed.
Lemma lem2617164 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2617165 : term481 = term482.
Proof. exact (MK_COMB (@lem2617164) (@lem2617163)). Qed.
Lemma lem2617166 : term480 = term483.
Proof. exact (MK_COMB (@lem2617165) (@lem2617160)). Qed.
Lemma lem2617167 : term484.
Proof. exact (@lem1980026 term43 term47 term131 term47). Qed.
Lemma lem2617169 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617170 : term420 = term426.
Proof. exact (@lem2617169 (NUMERAL 0) term48). Qed.
Lemma lem2617171 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617172 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617173 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617172 h1) (fun h1 : term426 = True => @lem2617171)). Qed.
Lemma lem2617174 : term426 = True.
Proof. exact (EQ_MP (@lem2617173) (@lem2617171)). Qed.
Lemma lem2617175 : term420 = True.
Proof. exact (TRANS (@lem2617170) (@lem2617174)). Qed.
Lemma lem2617176 : True = term420.
Proof. exact (SYM (@lem2617175)). Qed.
Lemma lem2617177 : term420.
Proof. exact (EQ_MP (@lem2617176) (@lem0)). Qed.
Lemma lem2617178 : term485.
Proof. exact (@lem2617167 (@lem2617177)). Qed.
Lemma lem2617180 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617181 : term420 = term426.
Proof. exact (@lem2617180 (NUMERAL 0) term48). Qed.
Lemma lem2617182 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617183 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617184 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617183 h1) (fun h1 : term426 = True => @lem2617182)). Qed.
Lemma lem2617185 : term426 = True.
Proof. exact (EQ_MP (@lem2617184) (@lem2617182)). Qed.
Lemma lem2617186 : term420 = True.
Proof. exact (TRANS (@lem2617181) (@lem2617185)). Qed.
Lemma lem2617187 : True = term420.
Proof. exact (SYM (@lem2617186)). Qed.
Lemma lem2617188 : term420.
Proof. exact (EQ_MP (@lem2617187) (@lem0)). Qed.
Lemma lem2617189 : term483 = term486.
Proof. exact (@lem2617178 (@lem2617188)). Qed.
Lemma lem2617191 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2617192 : term135 = term146.
Proof. exact (@lem2617191 term48 term48). Qed.
Lemma lem2617193 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617194 : term143 = term48.
Proof. exact (EQ_MP (@lem2617193) (@lem940073)). Qed.
Lemma lem2617195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617196 : term141 = term47.
Proof. exact (MK_COMB (@lem2617195) (@lem2617194)). Qed.
Lemma lem2617197 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2617198 : term146 = term131.
Proof. exact (MK_COMB (@lem2617197) (@lem2617196)). Qed.
Lemma lem2617199 : term135 = term131.
Proof. exact (TRANS (@lem2617192) (@lem2617198)). Qed.
Lemma lem2617201 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617202 : term431 = term43.
Proof. exact (@lem2617201 term48). Qed.
Lemma lem2617203 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2617204 : term487 = term481.
Proof. exact (MK_COMB (@lem2617203) (@lem2617202)). Qed.
Lemma lem2617205 : term486 = term480.
Proof. exact (MK_COMB (@lem2617204) (@lem2617199)). Qed.
Lemma lem2617207 (m : nat) (n : nat) : (term488 m n) = (term489 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2617208 : term480 = term490.
Proof. exact (@lem2617207 (NUMERAL 0) term48). Qed.
Lemma lem2617209 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617210 (h1 : term427 = (BIT1 0)) : (term48 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2617211 : (term427 = (BIT1 0)) = ((term48 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617210 h1) (fun h1 : (term48 = (NUMERAL 0)) = False => @lem2617209)). Qed.
Lemma lem2617212 : (term48 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2617211) (@lem2617209)). Qed.
Lemma lem2617213 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2617214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2617215 : term491 = (and True).
Proof. exact (MK_COMB (@lem2617214) (@lem2617213)). Qed.
Lemma lem2617216 : term490 = (True /\ False).
Proof. exact (MK_COMB (@lem2617215) (@lem2617212)). Qed.
Lemma lem2617218 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2617219 : term490 = False.
Proof. exact (TRANS (@lem2617216) (@lem2617218)). Qed.
Lemma lem2617220 : term480 = False.
Proof. exact (TRANS (@lem2617208) (@lem2617219)). Qed.
Lemma lem2617221 : term486 = False.
Proof. exact (TRANS (@lem2617205) (@lem2617220)). Qed.
Lemma lem2617222 : term483 = False.
Proof. exact (TRANS (@lem2617189) (@lem2617221)). Qed.
Lemma lem2617223 : term480 = False.
Proof. exact (TRANS (@lem2617166) (@lem2617222)). Qed.
Lemma lem2617224 : term479 = False.
Proof. exact (TRANS (@lem2617157) (@lem2617223)). Qed.
Lemma lem2617225 (a : int) (x : int) (h1 : term701 a x) : False.
Proof. exact (EQ_MP (@lem2617224) (@lem2617154 a x h1)). Qed.
Lemma lem2617226 (a : int) (x : int) (h1 : term703 a x) : term703 a x.
Proof. exact (h1). Qed.
Lemma lem2617227 (a : int) (x : int) (h1 : term703 a x) : term657 a x.
Proof. exact (proj2 (@lem2617226 a x h1)). Qed.
Lemma lem2617228 (a : int) (x : int) (h1 : term703 a x) : term698 a x.
Proof. exact (proj1 (@lem2617226 a x h1)). Qed.
Lemma lem2617230 (a : int) (x : int) (h1 : term703 a x) : term682 a x.
Proof. exact (proj1 (@lem2617228 a x h1)). Qed.
Lemma lem2617232 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2617233 : term419 = term420.
Proof. exact (@lem2617232 term43 term47). Qed.
Lemma lem2617235 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617236 : term47 = term128.
Proof. exact (@lem2617235 term48). Qed.
Lemma lem2617238 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617239 : term43 = term243.
Proof. exact (@lem2617238 (NUMERAL 0)). Qed.
Lemma lem2617240 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2617241 : term421 = term422.
Proof. exact (MK_COMB (@lem2617240) (@lem2617239)). Qed.
Lemma lem2617242 : term420 = term423.
Proof. exact (MK_COMB (@lem2617241) (@lem2617236)). Qed.
Lemma lem2617243 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2617245 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617246 : term420 = term426.
Proof. exact (@lem2617245 (NUMERAL 0) term48). Qed.
Lemma lem2617247 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617248 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617249 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617248 h1) (fun h1 : term426 = True => @lem2617247)). Qed.
Lemma lem2617250 : term426 = True.
Proof. exact (EQ_MP (@lem2617249) (@lem2617247)). Qed.
Lemma lem2617251 : term420 = True.
Proof. exact (TRANS (@lem2617246) (@lem2617250)). Qed.
Lemma lem2617252 : True = term420.
Proof. exact (SYM (@lem2617251)). Qed.
Lemma lem2617253 : term420.
Proof. exact (EQ_MP (@lem2617252) (@lem0)). Qed.
Lemma lem2617254 : term428.
Proof. exact (@lem2617243 (@lem2617253)). Qed.
Lemma lem2617256 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617257 : term420 = term426.
Proof. exact (@lem2617256 (NUMERAL 0) term48). Qed.
Lemma lem2617258 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617259 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617260 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617259 h1) (fun h1 : term426 = True => @lem2617258)). Qed.
Lemma lem2617261 : term426 = True.
Proof. exact (EQ_MP (@lem2617260) (@lem2617258)). Qed.
Lemma lem2617262 : term420 = True.
Proof. exact (TRANS (@lem2617257) (@lem2617261)). Qed.
Lemma lem2617263 : True = term420.
Proof. exact (SYM (@lem2617262)). Qed.
Lemma lem2617264 : term420.
Proof. exact (EQ_MP (@lem2617263) (@lem0)). Qed.
Lemma lem2617265 : term423 = term429.
Proof. exact (@lem2617254 (@lem2617264)). Qed.
Lemma lem2617267 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617268 : term140 = term141.
Proof. exact (@lem2617267 term48 term48). Qed.
Lemma lem2617269 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617270 : term143 = term48.
Proof. exact (EQ_MP (@lem2617269) (@lem940073)). Qed.
Lemma lem2617271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617272 : term141 = term47.
Proof. exact (MK_COMB (@lem2617271) (@lem2617270)). Qed.
Lemma lem2617273 : term140 = term47.
Proof. exact (TRANS (@lem2617268) (@lem2617272)). Qed.
Lemma lem2617275 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617276 : term431 = term43.
Proof. exact (@lem2617275 term48). Qed.
Lemma lem2617277 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2617278 : term432 = term421.
Proof. exact (MK_COMB (@lem2617277) (@lem2617276)). Qed.
Lemma lem2617279 : term429 = term420.
Proof. exact (MK_COMB (@lem2617278) (@lem2617273)). Qed.
Lemma lem2617281 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617282 : term420 = term426.
Proof. exact (@lem2617281 (NUMERAL 0) term48). Qed.
Lemma lem2617283 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617284 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617285 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617284 h1) (fun h1 : term426 = True => @lem2617283)). Qed.
Lemma lem2617286 : term426 = True.
Proof. exact (EQ_MP (@lem2617285) (@lem2617283)). Qed.
Lemma lem2617287 : term420 = True.
Proof. exact (TRANS (@lem2617282) (@lem2617286)). Qed.
Lemma lem2617288 : term429 = True.
Proof. exact (TRANS (@lem2617279) (@lem2617287)). Qed.
Lemma lem2617289 : term423 = True.
Proof. exact (TRANS (@lem2617265) (@lem2617288)). Qed.
Lemma lem2617290 : term420 = True.
Proof. exact (TRANS (@lem2617242) (@lem2617289)). Qed.
Lemma lem2617291 : term419 = True.
Proof. exact (TRANS (@lem2617233) (@lem2617290)). Qed.
Lemma lem2617292 : True = term419.
Proof. exact (SYM (@lem2617291)). Qed.
Lemma lem2617293 : term419.
Proof. exact (EQ_MP (@lem2617292) (@lem0)). Qed.
Lemma lem2617294 (a : int) (x : int) (h1 : term703 a x) : term784 a x.
Proof. exact (conj (@lem2617293) (@lem2617227 a x h1)). Qed.
Lemma lem2617296 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2617297 (a : int) (x : int) : term785 a x.
Proof. exact (@lem2617296 term47 (term654 a x)). Qed.
Lemma lem2617298 (a : int) (x : int) (h1 : term703 a x) : term786 a x.
Proof. exact (@lem2617297 a x (@lem2617294 a x h1)). Qed.
Lemma lem2617299 (a : int) (x : int) : (term787 a x) = (term654 a x).
Proof. exact (@lem1982733 (term654 a x)). Qed.
Lemma lem2617300 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2617301 (a : int) (x : int) : (term788 a x) = (term656 a x).
Proof. exact (MK_COMB (@lem2617300) (@lem2617299 a x)). Qed.
Lemma lem2617302 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2617303 (a : int) (x : int) : (term786 a x) = (term657 a x).
Proof. exact (MK_COMB (@lem2617301 a x) (@lem2617302)). Qed.
Lemma lem2617304 (a : int) (x : int) (h1 : term703 a x) : term657 a x.
Proof. exact (EQ_MP (@lem2617303 a x) (@lem2617298 a x h1)). Qed.
Lemma lem2617306 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2617307 : term419 = term420.
Proof. exact (@lem2617306 term43 term47). Qed.
Lemma lem2617309 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617310 : term47 = term128.
Proof. exact (@lem2617309 term48). Qed.
Lemma lem2617312 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617313 : term43 = term243.
Proof. exact (@lem2617312 (NUMERAL 0)). Qed.
Lemma lem2617314 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2617315 : term421 = term422.
Proof. exact (MK_COMB (@lem2617314) (@lem2617313)). Qed.
Lemma lem2617316 : term420 = term423.
Proof. exact (MK_COMB (@lem2617315) (@lem2617310)). Qed.
Lemma lem2617317 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2617319 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617320 : term420 = term426.
Proof. exact (@lem2617319 (NUMERAL 0) term48). Qed.
Lemma lem2617321 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617322 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617323 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617322 h1) (fun h1 : term426 = True => @lem2617321)). Qed.
Lemma lem2617324 : term426 = True.
Proof. exact (EQ_MP (@lem2617323) (@lem2617321)). Qed.
Lemma lem2617325 : term420 = True.
Proof. exact (TRANS (@lem2617320) (@lem2617324)). Qed.
Lemma lem2617326 : True = term420.
Proof. exact (SYM (@lem2617325)). Qed.
Lemma lem2617327 : term420.
Proof. exact (EQ_MP (@lem2617326) (@lem0)). Qed.
Lemma lem2617328 : term428.
Proof. exact (@lem2617317 (@lem2617327)). Qed.
Lemma lem2617330 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617331 : term420 = term426.
Proof. exact (@lem2617330 (NUMERAL 0) term48). Qed.
Lemma lem2617332 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617333 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617334 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617333 h1) (fun h1 : term426 = True => @lem2617332)). Qed.
Lemma lem2617335 : term426 = True.
Proof. exact (EQ_MP (@lem2617334) (@lem2617332)). Qed.
Lemma lem2617336 : term420 = True.
Proof. exact (TRANS (@lem2617331) (@lem2617335)). Qed.
Lemma lem2617337 : True = term420.
Proof. exact (SYM (@lem2617336)). Qed.
Lemma lem2617338 : term420.
Proof. exact (EQ_MP (@lem2617337) (@lem0)). Qed.
Lemma lem2617339 : term423 = term429.
Proof. exact (@lem2617328 (@lem2617338)). Qed.
Lemma lem2617341 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617342 : term140 = term141.
Proof. exact (@lem2617341 term48 term48). Qed.
Lemma lem2617343 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617344 : term143 = term48.
Proof. exact (EQ_MP (@lem2617343) (@lem940073)). Qed.
Lemma lem2617345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617346 : term141 = term47.
Proof. exact (MK_COMB (@lem2617345) (@lem2617344)). Qed.
Lemma lem2617347 : term140 = term47.
Proof. exact (TRANS (@lem2617342) (@lem2617346)). Qed.
Lemma lem2617349 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617350 : term431 = term43.
Proof. exact (@lem2617349 term48). Qed.
Lemma lem2617351 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2617352 : term432 = term421.
Proof. exact (MK_COMB (@lem2617351) (@lem2617350)). Qed.
Lemma lem2617353 : term429 = term420.
Proof. exact (MK_COMB (@lem2617352) (@lem2617347)). Qed.
Lemma lem2617355 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617356 : term420 = term426.
Proof. exact (@lem2617355 (NUMERAL 0) term48). Qed.
Lemma lem2617357 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617358 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617359 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617358 h1) (fun h1 : term426 = True => @lem2617357)). Qed.
Lemma lem2617360 : term426 = True.
Proof. exact (EQ_MP (@lem2617359) (@lem2617357)). Qed.
Lemma lem2617361 : term420 = True.
Proof. exact (TRANS (@lem2617356) (@lem2617360)). Qed.
Lemma lem2617362 : term429 = True.
Proof. exact (TRANS (@lem2617353) (@lem2617361)). Qed.
Lemma lem2617363 : term423 = True.
Proof. exact (TRANS (@lem2617339) (@lem2617362)). Qed.
Lemma lem2617364 : term420 = True.
Proof. exact (TRANS (@lem2617316) (@lem2617363)). Qed.
Lemma lem2617365 : term419 = True.
Proof. exact (TRANS (@lem2617307) (@lem2617364)). Qed.
Lemma lem2617366 : True = term419.
Proof. exact (SYM (@lem2617365)). Qed.
Lemma lem2617367 : term419.
Proof. exact (EQ_MP (@lem2617366) (@lem0)). Qed.
Lemma lem2617368 (a : int) (x : int) (h1 : term703 a x) : term789 a x.
Proof. exact (conj (@lem2617367) (@lem2617230 a x h1)). Qed.
Lemma lem2617370 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2617371 (a : int) (x : int) : term790 a x.
Proof. exact (@lem2617370 term47 (term401 a x)). Qed.
Lemma lem2617372 (a : int) (x : int) (h1 : term703 a x) : term791 a x.
Proof. exact (@lem2617371 a x (@lem2617368 a x h1)). Qed.
Lemma lem2617373 (a : int) (x : int) : (term792 a x) = (term401 a x).
Proof. exact (@lem1982733 (term401 a x)). Qed.
Lemma lem2617374 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2617375 (a : int) (x : int) : (term793 a x) = (term681 a x).
Proof. exact (MK_COMB (@lem2617374) (@lem2617373 a x)). Qed.
Lemma lem2617376 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2617377 (a : int) (x : int) : (term791 a x) = (term682 a x).
Proof. exact (MK_COMB (@lem2617375 a x) (@lem2617376)). Qed.
Lemma lem2617378 (a : int) (x : int) (h1 : term703 a x) : term682 a x.
Proof. exact (EQ_MP (@lem2617377 a x) (@lem2617372 a x h1)). Qed.
Lemma lem2617379 (a : int) (x : int) (h1 : term703 a x) : term794 a x.
Proof. exact (conj (@lem2617378 a x h1) (@lem2617304 a x h1)). Qed.
Lemma lem2617381 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2617382 (a : int) (x : int) : term795 a x.
Proof. exact (@lem2617381 (term401 a x) (term654 a x)). Qed.
Lemma lem2617383 (a : int) (x : int) (h1 : term703 a x) : term796 a x.
Proof. exact (@lem2617382 a x (@lem2617379 a x h1)). Qed.
Lemma lem2617384 (a : int) (x : int) : (term797 a x) = (term798 a x).
Proof. exact (@lem1982753 (real_of_int a) (term198 a) (term198 x) (term150 x)). Qed.
Lemma lem2617385 (a : int) : (term509 a) = (term473 a).
Proof. exact (@lem1982715 term131 (real_of_int a)). Qed.
Lemma lem2617387 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617388 : term47 = term128.
Proof. exact (@lem2617387 term48). Qed.
Lemma lem2617390 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2617391 : term131 = term132.
Proof. exact (@lem2617390 term48). Qed.
Lemma lem2617392 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617393 : term452 = term453.
Proof. exact (MK_COMB (@lem2617392) (@lem2617391)). Qed.
Lemma lem2617394 : term454 = term455.
Proof. exact (MK_COMB (@lem2617393) (@lem2617388)). Qed.
Lemma lem2617395 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2617397 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617398 : term420 = term426.
Proof. exact (@lem2617397 (NUMERAL 0) term48). Qed.
Lemma lem2617399 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617400 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617401 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617400 h1) (fun h1 : term426 = True => @lem2617399)). Qed.
Lemma lem2617402 : term426 = True.
Proof. exact (EQ_MP (@lem2617401) (@lem2617399)). Qed.
Lemma lem2617403 : term420 = True.
Proof. exact (TRANS (@lem2617398) (@lem2617402)). Qed.
Lemma lem2617404 : True = term420.
Proof. exact (SYM (@lem2617403)). Qed.
Lemma lem2617405 : term420.
Proof. exact (EQ_MP (@lem2617404) (@lem0)). Qed.
Lemma lem2617406 : term457.
Proof. exact (@lem2617395 (@lem2617405)). Qed.
Lemma lem2617408 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617409 : term420 = term426.
Proof. exact (@lem2617408 (NUMERAL 0) term48). Qed.
Lemma lem2617410 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617411 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617412 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617411 h1) (fun h1 : term426 = True => @lem2617410)). Qed.
Lemma lem2617413 : term426 = True.
Proof. exact (EQ_MP (@lem2617412) (@lem2617410)). Qed.
Lemma lem2617414 : term420 = True.
Proof. exact (TRANS (@lem2617409) (@lem2617413)). Qed.
Lemma lem2617415 : True = term420.
Proof. exact (SYM (@lem2617414)). Qed.
Lemma lem2617416 : term420.
Proof. exact (EQ_MP (@lem2617415) (@lem0)). Qed.
Lemma lem2617417 : term458.
Proof. exact (@lem2617406 (@lem2617416)). Qed.
Lemma lem2617419 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617420 : term420 = term426.
Proof. exact (@lem2617419 (NUMERAL 0) term48). Qed.
Lemma lem2617421 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617422 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617423 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617422 h1) (fun h1 : term426 = True => @lem2617421)). Qed.
Lemma lem2617424 : term426 = True.
Proof. exact (EQ_MP (@lem2617423) (@lem2617421)). Qed.
Lemma lem2617425 : term420 = True.
Proof. exact (TRANS (@lem2617420) (@lem2617424)). Qed.
Lemma lem2617426 : True = term420.
Proof. exact (SYM (@lem2617425)). Qed.
Lemma lem2617427 : term420.
Proof. exact (EQ_MP (@lem2617426) (@lem0)). Qed.
Lemma lem2617428 : term459.
Proof. exact (@lem2617417 (@lem2617427)). Qed.
Lemma lem2617430 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617431 : term140 = term141.
Proof. exact (@lem2617430 term48 term48). Qed.
Lemma lem2617432 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617433 : term143 = term48.
Proof. exact (EQ_MP (@lem2617432) (@lem940073)). Qed.
Lemma lem2617434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617435 : term141 = term47.
Proof. exact (MK_COMB (@lem2617434) (@lem2617433)). Qed.
Lemma lem2617436 : term140 = term47.
Proof. exact (TRANS (@lem2617431) (@lem2617435)). Qed.
Lemma lem2617438 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2617439 : term135 = term146.
Proof. exact (@lem2617438 term48 term48). Qed.
Lemma lem2617440 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617441 : term143 = term48.
Proof. exact (EQ_MP (@lem2617440) (@lem940073)). Qed.
Lemma lem2617442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617443 : term141 = term47.
Proof. exact (MK_COMB (@lem2617442) (@lem2617441)). Qed.
Lemma lem2617444 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2617445 : term146 = term131.
Proof. exact (MK_COMB (@lem2617444) (@lem2617443)). Qed.
Lemma lem2617446 : term135 = term131.
Proof. exact (TRANS (@lem2617439) (@lem2617445)). Qed.
Lemma lem2617447 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617448 : term460 = term452.
Proof. exact (MK_COMB (@lem2617447) (@lem2617446)). Qed.
Lemma lem2617449 : term461 = term454.
Proof. exact (MK_COMB (@lem2617448) (@lem2617436)). Qed.
Lemma lem2617451 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2617452 : term454 = term43.
Proof. exact (@lem2617451 term48). Qed.
Lemma lem2617453 : term461 = term43.
Proof. exact (TRANS (@lem2617449) (@lem2617452)). Qed.
Lemma lem2617454 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617455 : term463 = term464.
Proof. exact (MK_COMB (@lem2617454) (@lem2617453)). Qed.
Lemma lem2617456 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2617457 : term465 = term431.
Proof. exact (MK_COMB (@lem2617455) (@lem2617456)). Qed.
Lemma lem2617459 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617460 : term431 = term43.
Proof. exact (@lem2617459 term48). Qed.
Lemma lem2617461 : term465 = term43.
Proof. exact (TRANS (@lem2617457) (@lem2617460)). Qed.
Lemma lem2617463 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617464 : term140 = term141.
Proof. exact (@lem2617463 term48 term48). Qed.
Lemma lem2617465 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617466 : term143 = term48.
Proof. exact (EQ_MP (@lem2617465) (@lem940073)). Qed.
Lemma lem2617467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617468 : term141 = term47.
Proof. exact (MK_COMB (@lem2617467) (@lem2617466)). Qed.
Lemma lem2617469 : term140 = term47.
Proof. exact (TRANS (@lem2617464) (@lem2617468)). Qed.
Lemma lem2617470 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2617471 : term466 = term431.
Proof. exact (MK_COMB (@lem2617470) (@lem2617469)). Qed.
Lemma lem2617473 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617474 : term431 = term43.
Proof. exact (@lem2617473 term48). Qed.
Lemma lem2617475 : term466 = term43.
Proof. exact (TRANS (@lem2617471) (@lem2617474)). Qed.
Lemma lem2617476 : term43 = term466.
Proof. exact (SYM (@lem2617475)). Qed.
Lemma lem2617477 : term465 = term466.
Proof. exact (TRANS (@lem2617461) (@lem2617476)). Qed.
Lemma lem2617478 : term455 = term243.
Proof. exact (@lem2617428 (@lem2617477)). Qed.
Lemma lem2617479 : term454 = term243.
Proof. exact (TRANS (@lem2617394) (@lem2617478)). Qed.
Lemma lem2617481 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2617482 : term243 = term43.
Proof. exact (@lem2617481 term43). Qed.
Lemma lem2617483 : term454 = term43.
Proof. exact (TRANS (@lem2617479) (@lem2617482)). Qed.
Lemma lem2617484 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617485 : term467 = term464.
Proof. exact (MK_COMB (@lem2617484) (@lem2617483)). Qed.
Lemma lem2617486 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2617487 (a : int) : (term473 a) = (term474 a).
Proof. exact (MK_COMB (@lem2617485) (@lem2617486 a)). Qed.
Lemma lem2617488 (a : int) : (term509 a) = (term474 a).
Proof. exact (TRANS (@lem2617385 a) (@lem2617487 a)). Qed.
Lemma lem2617489 (a : int) : (term474 a) = term43.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2617490 (a : int) : (term509 a) = term43.
Proof. exact (TRANS (@lem2617488 a) (@lem2617489 a)). Qed.
Lemma lem2617491 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617492 (a : int) : (term510 a) = term45.
Proof. exact (MK_COMB (@lem2617491) (@lem2617490 a)). Qed.
Lemma lem2617493 (x : int) : (term534 x) = (term471 x).
Proof. exact (@lem1982763 (term198 x) (real_of_int x) term131). Qed.
Lemma lem2617494 (x : int) : (term472 x) = (term473 x).
Proof. exact (@lem1982713 term131 (real_of_int x)). Qed.
Lemma lem2617496 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617497 : term47 = term128.
Proof. exact (@lem2617496 term48). Qed.
Lemma lem2617499 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2617500 : term131 = term132.
Proof. exact (@lem2617499 term48). Qed.
Lemma lem2617501 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617502 : term452 = term453.
Proof. exact (MK_COMB (@lem2617501) (@lem2617500)). Qed.
Lemma lem2617503 : term454 = term455.
Proof. exact (MK_COMB (@lem2617502) (@lem2617497)). Qed.
Lemma lem2617504 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2617506 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617507 : term420 = term426.
Proof. exact (@lem2617506 (NUMERAL 0) term48). Qed.
Lemma lem2617508 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617509 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617510 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617509 h1) (fun h1 : term426 = True => @lem2617508)). Qed.
Lemma lem2617511 : term426 = True.
Proof. exact (EQ_MP (@lem2617510) (@lem2617508)). Qed.
Lemma lem2617512 : term420 = True.
Proof. exact (TRANS (@lem2617507) (@lem2617511)). Qed.
Lemma lem2617513 : True = term420.
Proof. exact (SYM (@lem2617512)). Qed.
Lemma lem2617514 : term420.
Proof. exact (EQ_MP (@lem2617513) (@lem0)). Qed.
Lemma lem2617515 : term457.
Proof. exact (@lem2617504 (@lem2617514)). Qed.
Lemma lem2617517 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617518 : term420 = term426.
Proof. exact (@lem2617517 (NUMERAL 0) term48). Qed.
Lemma lem2617519 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617520 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617521 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617520 h1) (fun h1 : term426 = True => @lem2617519)). Qed.
Lemma lem2617522 : term426 = True.
Proof. exact (EQ_MP (@lem2617521) (@lem2617519)). Qed.
Lemma lem2617523 : term420 = True.
Proof. exact (TRANS (@lem2617518) (@lem2617522)). Qed.
Lemma lem2617524 : True = term420.
Proof. exact (SYM (@lem2617523)). Qed.
Lemma lem2617525 : term420.
Proof. exact (EQ_MP (@lem2617524) (@lem0)). Qed.
Lemma lem2617526 : term458.
Proof. exact (@lem2617515 (@lem2617525)). Qed.
Lemma lem2617528 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617529 : term420 = term426.
Proof. exact (@lem2617528 (NUMERAL 0) term48). Qed.
Lemma lem2617530 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617531 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617532 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617531 h1) (fun h1 : term426 = True => @lem2617530)). Qed.
Lemma lem2617533 : term426 = True.
Proof. exact (EQ_MP (@lem2617532) (@lem2617530)). Qed.
Lemma lem2617534 : term420 = True.
Proof. exact (TRANS (@lem2617529) (@lem2617533)). Qed.
Lemma lem2617535 : True = term420.
Proof. exact (SYM (@lem2617534)). Qed.
Lemma lem2617536 : term420.
Proof. exact (EQ_MP (@lem2617535) (@lem0)). Qed.
Lemma lem2617537 : term459.
Proof. exact (@lem2617526 (@lem2617536)). Qed.
Lemma lem2617539 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617540 : term140 = term141.
Proof. exact (@lem2617539 term48 term48). Qed.
Lemma lem2617541 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617542 : term143 = term48.
Proof. exact (EQ_MP (@lem2617541) (@lem940073)). Qed.
Lemma lem2617543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617544 : term141 = term47.
Proof. exact (MK_COMB (@lem2617543) (@lem2617542)). Qed.
Lemma lem2617545 : term140 = term47.
Proof. exact (TRANS (@lem2617540) (@lem2617544)). Qed.
Lemma lem2617547 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2617548 : term135 = term146.
Proof. exact (@lem2617547 term48 term48). Qed.
Lemma lem2617549 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617550 : term143 = term48.
Proof. exact (EQ_MP (@lem2617549) (@lem940073)). Qed.
Lemma lem2617551 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617552 : term141 = term47.
Proof. exact (MK_COMB (@lem2617551) (@lem2617550)). Qed.
Lemma lem2617553 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2617554 : term146 = term131.
Proof. exact (MK_COMB (@lem2617553) (@lem2617552)). Qed.
Lemma lem2617555 : term135 = term131.
Proof. exact (TRANS (@lem2617548) (@lem2617554)). Qed.
Lemma lem2617556 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617557 : term460 = term452.
Proof. exact (MK_COMB (@lem2617556) (@lem2617555)). Qed.
Lemma lem2617558 : term461 = term454.
Proof. exact (MK_COMB (@lem2617557) (@lem2617545)). Qed.
Lemma lem2617560 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2617561 : term454 = term43.
Proof. exact (@lem2617560 term48). Qed.
Lemma lem2617562 : term461 = term43.
Proof. exact (TRANS (@lem2617558) (@lem2617561)). Qed.
Lemma lem2617563 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617564 : term463 = term464.
Proof. exact (MK_COMB (@lem2617563) (@lem2617562)). Qed.
Lemma lem2617565 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2617566 : term465 = term431.
Proof. exact (MK_COMB (@lem2617564) (@lem2617565)). Qed.
Lemma lem2617568 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617569 : term431 = term43.
Proof. exact (@lem2617568 term48). Qed.
Lemma lem2617570 : term465 = term43.
Proof. exact (TRANS (@lem2617566) (@lem2617569)). Qed.
Lemma lem2617572 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617573 : term140 = term141.
Proof. exact (@lem2617572 term48 term48). Qed.
Lemma lem2617574 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617575 : term143 = term48.
Proof. exact (EQ_MP (@lem2617574) (@lem940073)). Qed.
Lemma lem2617576 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617577 : term141 = term47.
Proof. exact (MK_COMB (@lem2617576) (@lem2617575)). Qed.
Lemma lem2617578 : term140 = term47.
Proof. exact (TRANS (@lem2617573) (@lem2617577)). Qed.
Lemma lem2617579 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2617580 : term466 = term431.
Proof. exact (MK_COMB (@lem2617579) (@lem2617578)). Qed.
Lemma lem2617582 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617583 : term431 = term43.
Proof. exact (@lem2617582 term48). Qed.
Lemma lem2617584 : term466 = term43.
Proof. exact (TRANS (@lem2617580) (@lem2617583)). Qed.
Lemma lem2617585 : term43 = term466.
Proof. exact (SYM (@lem2617584)). Qed.
Lemma lem2617586 : term465 = term466.
Proof. exact (TRANS (@lem2617570) (@lem2617585)). Qed.
Lemma lem2617587 : term455 = term243.
Proof. exact (@lem2617537 (@lem2617586)). Qed.
Lemma lem2617588 : term454 = term243.
Proof. exact (TRANS (@lem2617503) (@lem2617587)). Qed.
Lemma lem2617590 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2617591 : term243 = term43.
Proof. exact (@lem2617590 term43). Qed.
Lemma lem2617592 : term454 = term43.
Proof. exact (TRANS (@lem2617588) (@lem2617591)). Qed.
Lemma lem2617593 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617594 : term467 = term464.
Proof. exact (MK_COMB (@lem2617593) (@lem2617592)). Qed.
Lemma lem2617595 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2617596 (x : int) : (term473 x) = (term474 x).
Proof. exact (MK_COMB (@lem2617594) (@lem2617595 x)). Qed.
Lemma lem2617597 (x : int) : (term472 x) = (term474 x).
Proof. exact (TRANS (@lem2617494 x) (@lem2617596 x)). Qed.
Lemma lem2617598 (x : int) : (term474 x) = term43.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2617599 (x : int) : (term472 x) = term43.
Proof. exact (TRANS (@lem2617597 x) (@lem2617598 x)). Qed.
Lemma lem2617600 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617601 (x : int) : (term475 x) = term45.
Proof. exact (MK_COMB (@lem2617600) (@lem2617599 x)). Qed.
Lemma lem2617602 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2617603 (x : int) : (term471 x) = term476.
Proof. exact (MK_COMB (@lem2617601 x) (@lem2617602)). Qed.
Lemma lem2617604 (x : int) : (term534 x) = term476.
Proof. exact (TRANS (@lem2617493 x) (@lem2617603 x)). Qed.
Lemma lem2617605 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2617606 (x : int) : (term534 x) = term131.
Proof. exact (TRANS (@lem2617604 x) (@lem2617605)). Qed.
Lemma lem2617607 (a : int) (x : int) : (term798 a x) = term476.
Proof. exact (MK_COMB (@lem2617492 a) (@lem2617606 x)). Qed.
Lemma lem2617608 (a : int) (x : int) : (term797 a x) = term476.
Proof. exact (TRANS (@lem2617384 a x) (@lem2617607 a x)). Qed.
Lemma lem2617609 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2617610 (a : int) (x : int) : (term797 a x) = term131.
Proof. exact (TRANS (@lem2617608 a x) (@lem2617609)). Qed.
Lemma lem2617611 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2617612 (a : int) (x : int) : (term799 a x) = term478.
Proof. exact (MK_COMB (@lem2617611) (@lem2617610 a x)). Qed.
Lemma lem2617613 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2617614 (a : int) (x : int) : (term796 a x) = term479.
Proof. exact (MK_COMB (@lem2617612 a x) (@lem2617613)). Qed.
Lemma lem2617615 (a : int) (x : int) (h1 : term703 a x) : term479.
Proof. exact (EQ_MP (@lem2617614 a x) (@lem2617383 a x h1)). Qed.
Lemma lem2617617 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2617618 : term479 = term480.
Proof. exact (@lem2617617 term43 term131). Qed.
Lemma lem2617620 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2617621 : term131 = term132.
Proof. exact (@lem2617620 term48). Qed.
Lemma lem2617623 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617624 : term43 = term243.
Proof. exact (@lem2617623 (NUMERAL 0)). Qed.
Lemma lem2617625 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2617626 : term481 = term482.
Proof. exact (MK_COMB (@lem2617625) (@lem2617624)). Qed.
Lemma lem2617627 : term480 = term483.
Proof. exact (MK_COMB (@lem2617626) (@lem2617621)). Qed.
Lemma lem2617628 : term484.
Proof. exact (@lem1980026 term43 term47 term131 term47). Qed.
Lemma lem2617630 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617631 : term420 = term426.
Proof. exact (@lem2617630 (NUMERAL 0) term48). Qed.
Lemma lem2617632 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617633 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617634 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617633 h1) (fun h1 : term426 = True => @lem2617632)). Qed.
Lemma lem2617635 : term426 = True.
Proof. exact (EQ_MP (@lem2617634) (@lem2617632)). Qed.
Lemma lem2617636 : term420 = True.
Proof. exact (TRANS (@lem2617631) (@lem2617635)). Qed.
Lemma lem2617637 : True = term420.
Proof. exact (SYM (@lem2617636)). Qed.
Lemma lem2617638 : term420.
Proof. exact (EQ_MP (@lem2617637) (@lem0)). Qed.
Lemma lem2617639 : term485.
Proof. exact (@lem2617628 (@lem2617638)). Qed.
Lemma lem2617641 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617642 : term420 = term426.
Proof. exact (@lem2617641 (NUMERAL 0) term48). Qed.
Lemma lem2617643 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617644 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617645 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617644 h1) (fun h1 : term426 = True => @lem2617643)). Qed.
Lemma lem2617646 : term426 = True.
Proof. exact (EQ_MP (@lem2617645) (@lem2617643)). Qed.
Lemma lem2617647 : term420 = True.
Proof. exact (TRANS (@lem2617642) (@lem2617646)). Qed.
Lemma lem2617648 : True = term420.
Proof. exact (SYM (@lem2617647)). Qed.
Lemma lem2617649 : term420.
Proof. exact (EQ_MP (@lem2617648) (@lem0)). Qed.
Lemma lem2617650 : term483 = term486.
Proof. exact (@lem2617639 (@lem2617649)). Qed.
Lemma lem2617652 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2617653 : term135 = term146.
Proof. exact (@lem2617652 term48 term48). Qed.
Lemma lem2617654 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617655 : term143 = term48.
Proof. exact (EQ_MP (@lem2617654) (@lem940073)). Qed.
Lemma lem2617656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617657 : term141 = term47.
Proof. exact (MK_COMB (@lem2617656) (@lem2617655)). Qed.
Lemma lem2617658 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2617659 : term146 = term131.
Proof. exact (MK_COMB (@lem2617658) (@lem2617657)). Qed.
Lemma lem2617660 : term135 = term131.
Proof. exact (TRANS (@lem2617653) (@lem2617659)). Qed.
Lemma lem2617662 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617663 : term431 = term43.
Proof. exact (@lem2617662 term48). Qed.
Lemma lem2617664 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2617665 : term487 = term481.
Proof. exact (MK_COMB (@lem2617664) (@lem2617663)). Qed.
Lemma lem2617666 : term486 = term480.
Proof. exact (MK_COMB (@lem2617665) (@lem2617660)). Qed.
Lemma lem2617668 (m : nat) (n : nat) : (term488 m n) = (term489 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2617669 : term480 = term490.
Proof. exact (@lem2617668 (NUMERAL 0) term48). Qed.
Lemma lem2617670 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617671 (h1 : term427 = (BIT1 0)) : (term48 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2617672 : (term427 = (BIT1 0)) = ((term48 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617671 h1) (fun h1 : (term48 = (NUMERAL 0)) = False => @lem2617670)). Qed.
Lemma lem2617673 : (term48 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2617672) (@lem2617670)). Qed.
Lemma lem2617674 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2617675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2617676 : term491 = (and True).
Proof. exact (MK_COMB (@lem2617675) (@lem2617674)). Qed.
Lemma lem2617677 : term490 = (True /\ False).
Proof. exact (MK_COMB (@lem2617676) (@lem2617673)). Qed.
Lemma lem2617679 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2617680 : term490 = False.
Proof. exact (TRANS (@lem2617677) (@lem2617679)). Qed.
Lemma lem2617681 : term480 = False.
Proof. exact (TRANS (@lem2617669) (@lem2617680)). Qed.
Lemma lem2617682 : term486 = False.
Proof. exact (TRANS (@lem2617666) (@lem2617681)). Qed.
Lemma lem2617683 : term483 = False.
Proof. exact (TRANS (@lem2617650) (@lem2617682)). Qed.
Lemma lem2617684 : term480 = False.
Proof. exact (TRANS (@lem2617627) (@lem2617683)). Qed.
Lemma lem2617685 : term479 = False.
Proof. exact (TRANS (@lem2617618) (@lem2617684)). Qed.
Lemma lem2617686 (a : int) (x : int) (h1 : term703 a x) : False.
Proof. exact (EQ_MP (@lem2617685) (@lem2617615 a x h1)). Qed.
Lemma lem2617687 (a : int) (x : int) (h1 : term706 a x) : False.
Proof. exact (or_elim (@lem2616764 a x h1) (fun h0 : term701 a x => @lem2617225 a x h0) (fun h0 : term703 a x => @lem2617686 a x h0)). Qed.
Lemma lem2617688 (a : int) (x : int) (h1 : term765 a x) : term765 a x.
Proof. exact (h1). Qed.
Lemma lem2617689 (a : int) (x : int) (h1 : term747 a x) : term747 a x.
Proof. exact (h1). Qed.
Lemma lem2617690 (a : int) (x : int) (h1 : term747 a x) : term746 a x.
Proof. exact (proj2 (@lem2617689 a x h1)). Qed.
Lemma lem2617692 (a : int) (x : int) (h1 : term747 a x) : term684 a x.
Proof. exact (proj2 (@lem2617690 a x h1)). Qed.
Lemma lem2617693 (a : int) (x : int) (h1 : term747 a x) : term657 a x.
Proof. exact (proj1 (@lem2617690 a x h1)). Qed.
Lemma lem2617694 (a : int) (x : int) (h1 : term747 a x) : term682 a x.
Proof. exact (proj2 (@lem2617692 a x h1)). Qed.
Lemma lem2617697 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2617698 : term419 = term420.
Proof. exact (@lem2617697 term43 term47). Qed.
Lemma lem2617700 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617701 : term47 = term128.
Proof. exact (@lem2617700 term48). Qed.
Lemma lem2617703 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617704 : term43 = term243.
Proof. exact (@lem2617703 (NUMERAL 0)). Qed.
Lemma lem2617705 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2617706 : term421 = term422.
Proof. exact (MK_COMB (@lem2617705) (@lem2617704)). Qed.
Lemma lem2617707 : term420 = term423.
Proof. exact (MK_COMB (@lem2617706) (@lem2617701)). Qed.
Lemma lem2617708 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2617710 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617711 : term420 = term426.
Proof. exact (@lem2617710 (NUMERAL 0) term48). Qed.
Lemma lem2617712 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617713 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617714 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617713 h1) (fun h1 : term426 = True => @lem2617712)). Qed.
Lemma lem2617715 : term426 = True.
Proof. exact (EQ_MP (@lem2617714) (@lem2617712)). Qed.
Lemma lem2617716 : term420 = True.
Proof. exact (TRANS (@lem2617711) (@lem2617715)). Qed.
Lemma lem2617717 : True = term420.
Proof. exact (SYM (@lem2617716)). Qed.
Lemma lem2617718 : term420.
Proof. exact (EQ_MP (@lem2617717) (@lem0)). Qed.
Lemma lem2617719 : term428.
Proof. exact (@lem2617708 (@lem2617718)). Qed.
Lemma lem2617721 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617722 : term420 = term426.
Proof. exact (@lem2617721 (NUMERAL 0) term48). Qed.
Lemma lem2617723 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617724 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617725 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617724 h1) (fun h1 : term426 = True => @lem2617723)). Qed.
Lemma lem2617726 : term426 = True.
Proof. exact (EQ_MP (@lem2617725) (@lem2617723)). Qed.
Lemma lem2617727 : term420 = True.
Proof. exact (TRANS (@lem2617722) (@lem2617726)). Qed.
Lemma lem2617728 : True = term420.
Proof. exact (SYM (@lem2617727)). Qed.
Lemma lem2617729 : term420.
Proof. exact (EQ_MP (@lem2617728) (@lem0)). Qed.
Lemma lem2617730 : term423 = term429.
Proof. exact (@lem2617719 (@lem2617729)). Qed.
Lemma lem2617732 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617733 : term140 = term141.
Proof. exact (@lem2617732 term48 term48). Qed.
Lemma lem2617734 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617735 : term143 = term48.
Proof. exact (EQ_MP (@lem2617734) (@lem940073)). Qed.
Lemma lem2617736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617737 : term141 = term47.
Proof. exact (MK_COMB (@lem2617736) (@lem2617735)). Qed.
Lemma lem2617738 : term140 = term47.
Proof. exact (TRANS (@lem2617733) (@lem2617737)). Qed.
Lemma lem2617740 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617741 : term431 = term43.
Proof. exact (@lem2617740 term48). Qed.
Lemma lem2617742 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2617743 : term432 = term421.
Proof. exact (MK_COMB (@lem2617742) (@lem2617741)). Qed.
Lemma lem2617744 : term429 = term420.
Proof. exact (MK_COMB (@lem2617743) (@lem2617738)). Qed.
Lemma lem2617746 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617747 : term420 = term426.
Proof. exact (@lem2617746 (NUMERAL 0) term48). Qed.
Lemma lem2617748 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617749 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617750 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617749 h1) (fun h1 : term426 = True => @lem2617748)). Qed.
Lemma lem2617751 : term426 = True.
Proof. exact (EQ_MP (@lem2617750) (@lem2617748)). Qed.
Lemma lem2617752 : term420 = True.
Proof. exact (TRANS (@lem2617747) (@lem2617751)). Qed.
Lemma lem2617753 : term429 = True.
Proof. exact (TRANS (@lem2617744) (@lem2617752)). Qed.
Lemma lem2617754 : term423 = True.
Proof. exact (TRANS (@lem2617730) (@lem2617753)). Qed.
Lemma lem2617755 : term420 = True.
Proof. exact (TRANS (@lem2617707) (@lem2617754)). Qed.
Lemma lem2617756 : term419 = True.
Proof. exact (TRANS (@lem2617698) (@lem2617755)). Qed.
Lemma lem2617757 : True = term419.
Proof. exact (SYM (@lem2617756)). Qed.
Lemma lem2617758 : term419.
Proof. exact (EQ_MP (@lem2617757) (@lem0)). Qed.
Lemma lem2617759 (a : int) (x : int) (h1 : term747 a x) : term789 a x.
Proof. exact (conj (@lem2617758) (@lem2617694 a x h1)). Qed.
Lemma lem2617761 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2617762 (a : int) (x : int) : term790 a x.
Proof. exact (@lem2617761 term47 (term401 a x)). Qed.
Lemma lem2617763 (a : int) (x : int) (h1 : term747 a x) : term791 a x.
Proof. exact (@lem2617762 a x (@lem2617759 a x h1)). Qed.
Lemma lem2617764 (a : int) (x : int) : (term792 a x) = (term401 a x).
Proof. exact (@lem1982733 (term401 a x)). Qed.
Lemma lem2617765 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2617766 (a : int) (x : int) : (term793 a x) = (term681 a x).
Proof. exact (MK_COMB (@lem2617765) (@lem2617764 a x)). Qed.
Lemma lem2617767 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2617768 (a : int) (x : int) : (term791 a x) = (term682 a x).
Proof. exact (MK_COMB (@lem2617766 a x) (@lem2617767)). Qed.
Lemma lem2617769 (a : int) (x : int) (h1 : term747 a x) : term682 a x.
Proof. exact (EQ_MP (@lem2617768 a x) (@lem2617763 a x h1)). Qed.
Lemma lem2617771 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2617772 : term419 = term420.
Proof. exact (@lem2617771 term43 term47). Qed.
Lemma lem2617774 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617775 : term47 = term128.
Proof. exact (@lem2617774 term48). Qed.
Lemma lem2617777 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617778 : term43 = term243.
Proof. exact (@lem2617777 (NUMERAL 0)). Qed.
Lemma lem2617779 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2617780 : term421 = term422.
Proof. exact (MK_COMB (@lem2617779) (@lem2617778)). Qed.
Lemma lem2617781 : term420 = term423.
Proof. exact (MK_COMB (@lem2617780) (@lem2617775)). Qed.
Lemma lem2617782 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2617784 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617785 : term420 = term426.
Proof. exact (@lem2617784 (NUMERAL 0) term48). Qed.
Lemma lem2617786 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617787 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617788 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617787 h1) (fun h1 : term426 = True => @lem2617786)). Qed.
Lemma lem2617789 : term426 = True.
Proof. exact (EQ_MP (@lem2617788) (@lem2617786)). Qed.
Lemma lem2617790 : term420 = True.
Proof. exact (TRANS (@lem2617785) (@lem2617789)). Qed.
Lemma lem2617791 : True = term420.
Proof. exact (SYM (@lem2617790)). Qed.
Lemma lem2617792 : term420.
Proof. exact (EQ_MP (@lem2617791) (@lem0)). Qed.
Lemma lem2617793 : term428.
Proof. exact (@lem2617782 (@lem2617792)). Qed.
Lemma lem2617795 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617796 : term420 = term426.
Proof. exact (@lem2617795 (NUMERAL 0) term48). Qed.
Lemma lem2617797 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617798 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617799 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617798 h1) (fun h1 : term426 = True => @lem2617797)). Qed.
Lemma lem2617800 : term426 = True.
Proof. exact (EQ_MP (@lem2617799) (@lem2617797)). Qed.
Lemma lem2617801 : term420 = True.
Proof. exact (TRANS (@lem2617796) (@lem2617800)). Qed.
Lemma lem2617802 : True = term420.
Proof. exact (SYM (@lem2617801)). Qed.
Lemma lem2617803 : term420.
Proof. exact (EQ_MP (@lem2617802) (@lem0)). Qed.
Lemma lem2617804 : term423 = term429.
Proof. exact (@lem2617793 (@lem2617803)). Qed.
Lemma lem2617806 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617807 : term140 = term141.
Proof. exact (@lem2617806 term48 term48). Qed.
Lemma lem2617808 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617809 : term143 = term48.
Proof. exact (EQ_MP (@lem2617808) (@lem940073)). Qed.
Lemma lem2617810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617811 : term141 = term47.
Proof. exact (MK_COMB (@lem2617810) (@lem2617809)). Qed.
Lemma lem2617812 : term140 = term47.
Proof. exact (TRANS (@lem2617807) (@lem2617811)). Qed.
Lemma lem2617814 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617815 : term431 = term43.
Proof. exact (@lem2617814 term48). Qed.
Lemma lem2617816 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2617817 : term432 = term421.
Proof. exact (MK_COMB (@lem2617816) (@lem2617815)). Qed.
Lemma lem2617818 : term429 = term420.
Proof. exact (MK_COMB (@lem2617817) (@lem2617812)). Qed.
Lemma lem2617820 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617821 : term420 = term426.
Proof. exact (@lem2617820 (NUMERAL 0) term48). Qed.
Lemma lem2617822 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617823 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617824 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617823 h1) (fun h1 : term426 = True => @lem2617822)). Qed.
Lemma lem2617825 : term426 = True.
Proof. exact (EQ_MP (@lem2617824) (@lem2617822)). Qed.
Lemma lem2617826 : term420 = True.
Proof. exact (TRANS (@lem2617821) (@lem2617825)). Qed.
Lemma lem2617827 : term429 = True.
Proof. exact (TRANS (@lem2617818) (@lem2617826)). Qed.
Lemma lem2617828 : term423 = True.
Proof. exact (TRANS (@lem2617804) (@lem2617827)). Qed.
Lemma lem2617829 : term420 = True.
Proof. exact (TRANS (@lem2617781) (@lem2617828)). Qed.
Lemma lem2617830 : term419 = True.
Proof. exact (TRANS (@lem2617772) (@lem2617829)). Qed.
Lemma lem2617831 : True = term419.
Proof. exact (SYM (@lem2617830)). Qed.
Lemma lem2617832 : term419.
Proof. exact (EQ_MP (@lem2617831) (@lem0)). Qed.
Lemma lem2617833 (a : int) (x : int) (h1 : term747 a x) : term784 a x.
Proof. exact (conj (@lem2617832) (@lem2617693 a x h1)). Qed.
Lemma lem2617835 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2617836 (a : int) (x : int) : term785 a x.
Proof. exact (@lem2617835 term47 (term654 a x)). Qed.
Lemma lem2617837 (a : int) (x : int) (h1 : term747 a x) : term786 a x.
Proof. exact (@lem2617836 a x (@lem2617833 a x h1)). Qed.
Lemma lem2617838 (a : int) (x : int) : (term787 a x) = (term654 a x).
Proof. exact (@lem1982733 (term654 a x)). Qed.
Lemma lem2617839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2617840 (a : int) (x : int) : (term788 a x) = (term656 a x).
Proof. exact (MK_COMB (@lem2617839) (@lem2617838 a x)). Qed.
Lemma lem2617841 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2617842 (a : int) (x : int) : (term786 a x) = (term657 a x).
Proof. exact (MK_COMB (@lem2617840 a x) (@lem2617841)). Qed.
Lemma lem2617843 (a : int) (x : int) (h1 : term747 a x) : term657 a x.
Proof. exact (EQ_MP (@lem2617842 a x) (@lem2617837 a x h1)). Qed.
Lemma lem2617844 (a : int) (x : int) (h1 : term747 a x) : term800 a x.
Proof. exact (conj (@lem2617843 a x h1) (@lem2617769 a x h1)). Qed.
Lemma lem2617846 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2617847 (a : int) (x : int) : term801 a x.
Proof. exact (@lem2617846 (term654 a x) (term401 a x)). Qed.
Lemma lem2617848 (a : int) (x : int) (h1 : term747 a x) : term802 a x.
Proof. exact (@lem2617847 a x (@lem2617844 a x h1)). Qed.
Lemma lem2617849 (a : int) (x : int) : (term803 a x) = (term804 a x).
Proof. exact (@lem1982753 (term198 a) (real_of_int a) (term150 x) (term198 x)). Qed.
Lemma lem2617850 (a : int) : (term472 a) = (term473 a).
Proof. exact (@lem1982713 term131 (real_of_int a)). Qed.
Lemma lem2617852 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617853 : term47 = term128.
Proof. exact (@lem2617852 term48). Qed.
Lemma lem2617855 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2617856 : term131 = term132.
Proof. exact (@lem2617855 term48). Qed.
Lemma lem2617857 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617858 : term452 = term453.
Proof. exact (MK_COMB (@lem2617857) (@lem2617856)). Qed.
Lemma lem2617859 : term454 = term455.
Proof. exact (MK_COMB (@lem2617858) (@lem2617853)). Qed.
Lemma lem2617860 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2617862 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617863 : term420 = term426.
Proof. exact (@lem2617862 (NUMERAL 0) term48). Qed.
Lemma lem2617864 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617865 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617866 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617865 h1) (fun h1 : term426 = True => @lem2617864)). Qed.
Lemma lem2617867 : term426 = True.
Proof. exact (EQ_MP (@lem2617866) (@lem2617864)). Qed.
Lemma lem2617868 : term420 = True.
Proof. exact (TRANS (@lem2617863) (@lem2617867)). Qed.
Lemma lem2617869 : True = term420.
Proof. exact (SYM (@lem2617868)). Qed.
Lemma lem2617870 : term420.
Proof. exact (EQ_MP (@lem2617869) (@lem0)). Qed.
Lemma lem2617871 : term457.
Proof. exact (@lem2617860 (@lem2617870)). Qed.
Lemma lem2617873 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617874 : term420 = term426.
Proof. exact (@lem2617873 (NUMERAL 0) term48). Qed.
Lemma lem2617875 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617876 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617877 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617876 h1) (fun h1 : term426 = True => @lem2617875)). Qed.
Lemma lem2617878 : term426 = True.
Proof. exact (EQ_MP (@lem2617877) (@lem2617875)). Qed.
Lemma lem2617879 : term420 = True.
Proof. exact (TRANS (@lem2617874) (@lem2617878)). Qed.
Lemma lem2617880 : True = term420.
Proof. exact (SYM (@lem2617879)). Qed.
Lemma lem2617881 : term420.
Proof. exact (EQ_MP (@lem2617880) (@lem0)). Qed.
Lemma lem2617882 : term458.
Proof. exact (@lem2617871 (@lem2617881)). Qed.
Lemma lem2617884 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617885 : term420 = term426.
Proof. exact (@lem2617884 (NUMERAL 0) term48). Qed.
Lemma lem2617886 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617887 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617888 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617887 h1) (fun h1 : term426 = True => @lem2617886)). Qed.
Lemma lem2617889 : term426 = True.
Proof. exact (EQ_MP (@lem2617888) (@lem2617886)). Qed.
Lemma lem2617890 : term420 = True.
Proof. exact (TRANS (@lem2617885) (@lem2617889)). Qed.
Lemma lem2617891 : True = term420.
Proof. exact (SYM (@lem2617890)). Qed.
Lemma lem2617892 : term420.
Proof. exact (EQ_MP (@lem2617891) (@lem0)). Qed.
Lemma lem2617893 : term459.
Proof. exact (@lem2617882 (@lem2617892)). Qed.
Lemma lem2617895 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617896 : term140 = term141.
Proof. exact (@lem2617895 term48 term48). Qed.
Lemma lem2617897 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617898 : term143 = term48.
Proof. exact (EQ_MP (@lem2617897) (@lem940073)). Qed.
Lemma lem2617899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617900 : term141 = term47.
Proof. exact (MK_COMB (@lem2617899) (@lem2617898)). Qed.
Lemma lem2617901 : term140 = term47.
Proof. exact (TRANS (@lem2617896) (@lem2617900)). Qed.
Lemma lem2617903 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2617904 : term135 = term146.
Proof. exact (@lem2617903 term48 term48). Qed.
Lemma lem2617905 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617906 : term143 = term48.
Proof. exact (EQ_MP (@lem2617905) (@lem940073)). Qed.
Lemma lem2617907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617908 : term141 = term47.
Proof. exact (MK_COMB (@lem2617907) (@lem2617906)). Qed.
Lemma lem2617909 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2617910 : term146 = term131.
Proof. exact (MK_COMB (@lem2617909) (@lem2617908)). Qed.
Lemma lem2617911 : term135 = term131.
Proof. exact (TRANS (@lem2617904) (@lem2617910)). Qed.
Lemma lem2617912 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617913 : term460 = term452.
Proof. exact (MK_COMB (@lem2617912) (@lem2617911)). Qed.
Lemma lem2617914 : term461 = term454.
Proof. exact (MK_COMB (@lem2617913) (@lem2617901)). Qed.
Lemma lem2617916 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2617917 : term454 = term43.
Proof. exact (@lem2617916 term48). Qed.
Lemma lem2617918 : term461 = term43.
Proof. exact (TRANS (@lem2617914) (@lem2617917)). Qed.
Lemma lem2617919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617920 : term463 = term464.
Proof. exact (MK_COMB (@lem2617919) (@lem2617918)). Qed.
Lemma lem2617921 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2617922 : term465 = term431.
Proof. exact (MK_COMB (@lem2617920) (@lem2617921)). Qed.
Lemma lem2617924 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617925 : term431 = term43.
Proof. exact (@lem2617924 term48). Qed.
Lemma lem2617926 : term465 = term43.
Proof. exact (TRANS (@lem2617922) (@lem2617925)). Qed.
Lemma lem2617928 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2617929 : term140 = term141.
Proof. exact (@lem2617928 term48 term48). Qed.
Lemma lem2617930 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2617931 : term143 = term48.
Proof. exact (EQ_MP (@lem2617930) (@lem940073)). Qed.
Lemma lem2617932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2617933 : term141 = term47.
Proof. exact (MK_COMB (@lem2617932) (@lem2617931)). Qed.
Lemma lem2617934 : term140 = term47.
Proof. exact (TRANS (@lem2617929) (@lem2617933)). Qed.
Lemma lem2617935 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2617936 : term466 = term431.
Proof. exact (MK_COMB (@lem2617935) (@lem2617934)). Qed.
Lemma lem2617938 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2617939 : term431 = term43.
Proof. exact (@lem2617938 term48). Qed.
Lemma lem2617940 : term466 = term43.
Proof. exact (TRANS (@lem2617936) (@lem2617939)). Qed.
Lemma lem2617941 : term43 = term466.
Proof. exact (SYM (@lem2617940)). Qed.
Lemma lem2617942 : term465 = term466.
Proof. exact (TRANS (@lem2617926) (@lem2617941)). Qed.
Lemma lem2617943 : term455 = term243.
Proof. exact (@lem2617893 (@lem2617942)). Qed.
Lemma lem2617944 : term454 = term243.
Proof. exact (TRANS (@lem2617859) (@lem2617943)). Qed.
Lemma lem2617946 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2617947 : term243 = term43.
Proof. exact (@lem2617946 term43). Qed.
Lemma lem2617948 : term454 = term43.
Proof. exact (TRANS (@lem2617944) (@lem2617947)). Qed.
Lemma lem2617949 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2617950 : term467 = term464.
Proof. exact (MK_COMB (@lem2617949) (@lem2617948)). Qed.
Lemma lem2617951 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2617952 (a : int) : (term473 a) = (term474 a).
Proof. exact (MK_COMB (@lem2617950) (@lem2617951 a)). Qed.
Lemma lem2617953 (a : int) : (term472 a) = (term474 a).
Proof. exact (TRANS (@lem2617850 a) (@lem2617952 a)). Qed.
Lemma lem2617954 (a : int) : (term474 a) = term43.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2617955 (a : int) : (term472 a) = term43.
Proof. exact (TRANS (@lem2617953 a) (@lem2617954 a)). Qed.
Lemma lem2617956 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617957 (a : int) : (term475 a) = term45.
Proof. exact (MK_COMB (@lem2617956) (@lem2617955 a)). Qed.
Lemma lem2617958 (x : int) : (term549 x) = (term508 x).
Proof. exact (@lem1982759 (real_of_int x) (term198 x) term131). Qed.
Lemma lem2617959 (x : int) : (term509 x) = (term473 x).
Proof. exact (@lem1982715 term131 (real_of_int x)). Qed.
Lemma lem2617961 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2617962 : term47 = term128.
Proof. exact (@lem2617961 term48). Qed.
Lemma lem2617964 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2617965 : term131 = term132.
Proof. exact (@lem2617964 term48). Qed.
Lemma lem2617966 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2617967 : term452 = term453.
Proof. exact (MK_COMB (@lem2617966) (@lem2617965)). Qed.
Lemma lem2617968 : term454 = term455.
Proof. exact (MK_COMB (@lem2617967) (@lem2617962)). Qed.
Lemma lem2617969 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2617971 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617972 : term420 = term426.
Proof. exact (@lem2617971 (NUMERAL 0) term48). Qed.
Lemma lem2617973 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617974 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617975 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617974 h1) (fun h1 : term426 = True => @lem2617973)). Qed.
Lemma lem2617976 : term426 = True.
Proof. exact (EQ_MP (@lem2617975) (@lem2617973)). Qed.
Lemma lem2617977 : term420 = True.
Proof. exact (TRANS (@lem2617972) (@lem2617976)). Qed.
Lemma lem2617978 : True = term420.
Proof. exact (SYM (@lem2617977)). Qed.
Lemma lem2617979 : term420.
Proof. exact (EQ_MP (@lem2617978) (@lem0)). Qed.
Lemma lem2617980 : term457.
Proof. exact (@lem2617969 (@lem2617979)). Qed.
Lemma lem2617982 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617983 : term420 = term426.
Proof. exact (@lem2617982 (NUMERAL 0) term48). Qed.
Lemma lem2617984 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617985 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617986 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617985 h1) (fun h1 : term426 = True => @lem2617984)). Qed.
Lemma lem2617987 : term426 = True.
Proof. exact (EQ_MP (@lem2617986) (@lem2617984)). Qed.
Lemma lem2617988 : term420 = True.
Proof. exact (TRANS (@lem2617983) (@lem2617987)). Qed.
Lemma lem2617989 : True = term420.
Proof. exact (SYM (@lem2617988)). Qed.
Lemma lem2617990 : term420.
Proof. exact (EQ_MP (@lem2617989) (@lem0)). Qed.
Lemma lem2617991 : term458.
Proof. exact (@lem2617980 (@lem2617990)). Qed.
Lemma lem2617993 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2617994 : term420 = term426.
Proof. exact (@lem2617993 (NUMERAL 0) term48). Qed.
Lemma lem2617995 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2617996 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2617997 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2617996 h1) (fun h1 : term426 = True => @lem2617995)). Qed.
Lemma lem2617998 : term426 = True.
Proof. exact (EQ_MP (@lem2617997) (@lem2617995)). Qed.
Lemma lem2617999 : term420 = True.
Proof. exact (TRANS (@lem2617994) (@lem2617998)). Qed.
Lemma lem2618000 : True = term420.
Proof. exact (SYM (@lem2617999)). Qed.
Lemma lem2618001 : term420.
Proof. exact (EQ_MP (@lem2618000) (@lem0)). Qed.
Lemma lem2618002 : term459.
Proof. exact (@lem2617991 (@lem2618001)). Qed.
Lemma lem2618004 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2618005 : term140 = term141.
Proof. exact (@lem2618004 term48 term48). Qed.
Lemma lem2618006 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618007 : term143 = term48.
Proof. exact (EQ_MP (@lem2618006) (@lem940073)). Qed.
Lemma lem2618008 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618009 : term141 = term47.
Proof. exact (MK_COMB (@lem2618008) (@lem2618007)). Qed.
Lemma lem2618010 : term140 = term47.
Proof. exact (TRANS (@lem2618005) (@lem2618009)). Qed.
Lemma lem2618012 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2618013 : term135 = term146.
Proof. exact (@lem2618012 term48 term48). Qed.
Lemma lem2618014 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618015 : term143 = term48.
Proof. exact (EQ_MP (@lem2618014) (@lem940073)). Qed.
Lemma lem2618016 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618017 : term141 = term47.
Proof. exact (MK_COMB (@lem2618016) (@lem2618015)). Qed.
Lemma lem2618018 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2618019 : term146 = term131.
Proof. exact (MK_COMB (@lem2618018) (@lem2618017)). Qed.
Lemma lem2618020 : term135 = term131.
Proof. exact (TRANS (@lem2618013) (@lem2618019)). Qed.
Lemma lem2618021 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2618022 : term460 = term452.
Proof. exact (MK_COMB (@lem2618021) (@lem2618020)). Qed.
Lemma lem2618023 : term461 = term454.
Proof. exact (MK_COMB (@lem2618022) (@lem2618010)). Qed.
Lemma lem2618025 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2618026 : term454 = term43.
Proof. exact (@lem2618025 term48). Qed.
Lemma lem2618027 : term461 = term43.
Proof. exact (TRANS (@lem2618023) (@lem2618026)). Qed.
Lemma lem2618028 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2618029 : term463 = term464.
Proof. exact (MK_COMB (@lem2618028) (@lem2618027)). Qed.
Lemma lem2618030 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2618031 : term465 = term431.
Proof. exact (MK_COMB (@lem2618029) (@lem2618030)). Qed.
Lemma lem2618033 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618034 : term431 = term43.
Proof. exact (@lem2618033 term48). Qed.
Lemma lem2618035 : term465 = term43.
Proof. exact (TRANS (@lem2618031) (@lem2618034)). Qed.
Lemma lem2618037 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2618038 : term140 = term141.
Proof. exact (@lem2618037 term48 term48). Qed.
Lemma lem2618039 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618040 : term143 = term48.
Proof. exact (EQ_MP (@lem2618039) (@lem940073)). Qed.
Lemma lem2618041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618042 : term141 = term47.
Proof. exact (MK_COMB (@lem2618041) (@lem2618040)). Qed.
Lemma lem2618043 : term140 = term47.
Proof. exact (TRANS (@lem2618038) (@lem2618042)). Qed.
Lemma lem2618044 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2618045 : term466 = term431.
Proof. exact (MK_COMB (@lem2618044) (@lem2618043)). Qed.
Lemma lem2618047 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618048 : term431 = term43.
Proof. exact (@lem2618047 term48). Qed.
Lemma lem2618049 : term466 = term43.
Proof. exact (TRANS (@lem2618045) (@lem2618048)). Qed.
Lemma lem2618050 : term43 = term466.
Proof. exact (SYM (@lem2618049)). Qed.
Lemma lem2618051 : term465 = term466.
Proof. exact (TRANS (@lem2618035) (@lem2618050)). Qed.
Lemma lem2618052 : term455 = term243.
Proof. exact (@lem2618002 (@lem2618051)). Qed.
Lemma lem2618053 : term454 = term243.
Proof. exact (TRANS (@lem2617968) (@lem2618052)). Qed.
Lemma lem2618055 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2618056 : term243 = term43.
Proof. exact (@lem2618055 term43). Qed.
Lemma lem2618057 : term454 = term43.
Proof. exact (TRANS (@lem2618053) (@lem2618056)). Qed.
Lemma lem2618058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2618059 : term467 = term464.
Proof. exact (MK_COMB (@lem2618058) (@lem2618057)). Qed.
Lemma lem2618060 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2618061 (x : int) : (term473 x) = (term474 x).
Proof. exact (MK_COMB (@lem2618059) (@lem2618060 x)). Qed.
Lemma lem2618062 (x : int) : (term509 x) = (term474 x).
Proof. exact (TRANS (@lem2617959 x) (@lem2618061 x)). Qed.
Lemma lem2618063 (x : int) : (term474 x) = term43.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2618064 (x : int) : (term509 x) = term43.
Proof. exact (TRANS (@lem2618062 x) (@lem2618063 x)). Qed.
Lemma lem2618065 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2618066 (x : int) : (term510 x) = term45.
Proof. exact (MK_COMB (@lem2618065) (@lem2618064 x)). Qed.
Lemma lem2618067 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2618068 (x : int) : (term508 x) = term476.
Proof. exact (MK_COMB (@lem2618066 x) (@lem2618067)). Qed.
Lemma lem2618069 (x : int) : (term549 x) = term476.
Proof. exact (TRANS (@lem2617958 x) (@lem2618068 x)). Qed.
Lemma lem2618070 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2618071 (x : int) : (term549 x) = term131.
Proof. exact (TRANS (@lem2618069 x) (@lem2618070)). Qed.
Lemma lem2618072 (a : int) (x : int) : (term804 a x) = term476.
Proof. exact (MK_COMB (@lem2617957 a) (@lem2618071 x)). Qed.
Lemma lem2618073 (a : int) (x : int) : (term803 a x) = term476.
Proof. exact (TRANS (@lem2617849 a x) (@lem2618072 a x)). Qed.
Lemma lem2618074 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2618075 (a : int) (x : int) : (term803 a x) = term131.
Proof. exact (TRANS (@lem2618073 a x) (@lem2618074)). Qed.
Lemma lem2618076 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2618077 (a : int) (x : int) : (term805 a x) = term478.
Proof. exact (MK_COMB (@lem2618076) (@lem2618075 a x)). Qed.
Lemma lem2618078 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2618079 (a : int) (x : int) : (term802 a x) = term479.
Proof. exact (MK_COMB (@lem2618077 a x) (@lem2618078)). Qed.
Lemma lem2618080 (a : int) (x : int) (h1 : term747 a x) : term479.
Proof. exact (EQ_MP (@lem2618079 a x) (@lem2617848 a x h1)). Qed.
Lemma lem2618082 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2618083 : term479 = term480.
Proof. exact (@lem2618082 term43 term131). Qed.
Lemma lem2618085 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2618086 : term131 = term132.
Proof. exact (@lem2618085 term48). Qed.
Lemma lem2618088 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2618089 : term43 = term243.
Proof. exact (@lem2618088 (NUMERAL 0)). Qed.
Lemma lem2618090 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2618091 : term481 = term482.
Proof. exact (MK_COMB (@lem2618090) (@lem2618089)). Qed.
Lemma lem2618092 : term480 = term483.
Proof. exact (MK_COMB (@lem2618091) (@lem2618086)). Qed.
Lemma lem2618093 : term484.
Proof. exact (@lem1980026 term43 term47 term131 term47). Qed.
Lemma lem2618095 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618096 : term420 = term426.
Proof. exact (@lem2618095 (NUMERAL 0) term48). Qed.
Lemma lem2618097 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618098 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618099 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618098 h1) (fun h1 : term426 = True => @lem2618097)). Qed.
Lemma lem2618100 : term426 = True.
Proof. exact (EQ_MP (@lem2618099) (@lem2618097)). Qed.
Lemma lem2618101 : term420 = True.
Proof. exact (TRANS (@lem2618096) (@lem2618100)). Qed.
Lemma lem2618102 : True = term420.
Proof. exact (SYM (@lem2618101)). Qed.
Lemma lem2618103 : term420.
Proof. exact (EQ_MP (@lem2618102) (@lem0)). Qed.
Lemma lem2618104 : term485.
Proof. exact (@lem2618093 (@lem2618103)). Qed.
Lemma lem2618106 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618107 : term420 = term426.
Proof. exact (@lem2618106 (NUMERAL 0) term48). Qed.
Lemma lem2618108 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618109 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618110 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618109 h1) (fun h1 : term426 = True => @lem2618108)). Qed.
Lemma lem2618111 : term426 = True.
Proof. exact (EQ_MP (@lem2618110) (@lem2618108)). Qed.
Lemma lem2618112 : term420 = True.
Proof. exact (TRANS (@lem2618107) (@lem2618111)). Qed.
Lemma lem2618113 : True = term420.
Proof. exact (SYM (@lem2618112)). Qed.
Lemma lem2618114 : term420.
Proof. exact (EQ_MP (@lem2618113) (@lem0)). Qed.
Lemma lem2618115 : term483 = term486.
Proof. exact (@lem2618104 (@lem2618114)). Qed.
Lemma lem2618117 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2618118 : term135 = term146.
Proof. exact (@lem2618117 term48 term48). Qed.
Lemma lem2618119 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618120 : term143 = term48.
Proof. exact (EQ_MP (@lem2618119) (@lem940073)). Qed.
Lemma lem2618121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618122 : term141 = term47.
Proof. exact (MK_COMB (@lem2618121) (@lem2618120)). Qed.
Lemma lem2618123 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2618124 : term146 = term131.
Proof. exact (MK_COMB (@lem2618123) (@lem2618122)). Qed.
Lemma lem2618125 : term135 = term131.
Proof. exact (TRANS (@lem2618118) (@lem2618124)). Qed.
Lemma lem2618127 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618128 : term431 = term43.
Proof. exact (@lem2618127 term48). Qed.
Lemma lem2618129 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2618130 : term487 = term481.
Proof. exact (MK_COMB (@lem2618129) (@lem2618128)). Qed.
Lemma lem2618131 : term486 = term480.
Proof. exact (MK_COMB (@lem2618130) (@lem2618125)). Qed.
Lemma lem2618133 (m : nat) (n : nat) : (term488 m n) = (term489 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2618134 : term480 = term490.
Proof. exact (@lem2618133 (NUMERAL 0) term48). Qed.
Lemma lem2618135 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618136 (h1 : term427 = (BIT1 0)) : (term48 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2618137 : (term427 = (BIT1 0)) = ((term48 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618136 h1) (fun h1 : (term48 = (NUMERAL 0)) = False => @lem2618135)). Qed.
Lemma lem2618138 : (term48 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2618137) (@lem2618135)). Qed.
Lemma lem2618139 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2618140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2618141 : term491 = (and True).
Proof. exact (MK_COMB (@lem2618140) (@lem2618139)). Qed.
Lemma lem2618142 : term490 = (True /\ False).
Proof. exact (MK_COMB (@lem2618141) (@lem2618138)). Qed.
Lemma lem2618144 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2618145 : term490 = False.
Proof. exact (TRANS (@lem2618142) (@lem2618144)). Qed.
Lemma lem2618146 : term480 = False.
Proof. exact (TRANS (@lem2618134) (@lem2618145)). Qed.
Lemma lem2618147 : term486 = False.
Proof. exact (TRANS (@lem2618131) (@lem2618146)). Qed.
Lemma lem2618148 : term483 = False.
Proof. exact (TRANS (@lem2618115) (@lem2618147)). Qed.
Lemma lem2618149 : term480 = False.
Proof. exact (TRANS (@lem2618092) (@lem2618148)). Qed.
Lemma lem2618150 : term479 = False.
Proof. exact (TRANS (@lem2618083) (@lem2618149)). Qed.
Lemma lem2618151 (a : int) (x : int) (h1 : term747 a x) : False.
Proof. exact (EQ_MP (@lem2618150) (@lem2618080 a x h1)). Qed.
Lemma lem2618152 (a : int) (x : int) (h1 : term763 a x) : term763 a x.
Proof. exact (h1). Qed.
Lemma lem2618153 (a : int) (x : int) (h1 : term763 a x) : term762 a x.
Proof. exact (proj2 (@lem2618152 a x h1)). Qed.
Lemma lem2618155 (a : int) (x : int) (h1 : term763 a x) : term684 a x.
Proof. exact (proj2 (@lem2618153 a x h1)). Qed.
Lemma lem2618156 (a : int) (x : int) (h1 : term763 a x) : term649 a x.
Proof. exact (proj1 (@lem2618153 a x h1)). Qed.
Lemma lem2618158 (a : int) (x : int) (h1 : term763 a x) : term677 a x.
Proof. exact (proj1 (@lem2618155 a x h1)). Qed.
Lemma lem2618160 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2618161 : term419 = term420.
Proof. exact (@lem2618160 term43 term47). Qed.
Lemma lem2618163 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2618164 : term47 = term128.
Proof. exact (@lem2618163 term48). Qed.
Lemma lem2618166 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2618167 : term43 = term243.
Proof. exact (@lem2618166 (NUMERAL 0)). Qed.
Lemma lem2618168 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2618169 : term421 = term422.
Proof. exact (MK_COMB (@lem2618168) (@lem2618167)). Qed.
Lemma lem2618170 : term420 = term423.
Proof. exact (MK_COMB (@lem2618169) (@lem2618164)). Qed.
Lemma lem2618171 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2618173 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618174 : term420 = term426.
Proof. exact (@lem2618173 (NUMERAL 0) term48). Qed.
Lemma lem2618175 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618176 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618177 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618176 h1) (fun h1 : term426 = True => @lem2618175)). Qed.
Lemma lem2618178 : term426 = True.
Proof. exact (EQ_MP (@lem2618177) (@lem2618175)). Qed.
Lemma lem2618179 : term420 = True.
Proof. exact (TRANS (@lem2618174) (@lem2618178)). Qed.
Lemma lem2618180 : True = term420.
Proof. exact (SYM (@lem2618179)). Qed.
Lemma lem2618181 : term420.
Proof. exact (EQ_MP (@lem2618180) (@lem0)). Qed.
Lemma lem2618182 : term428.
Proof. exact (@lem2618171 (@lem2618181)). Qed.
Lemma lem2618184 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618185 : term420 = term426.
Proof. exact (@lem2618184 (NUMERAL 0) term48). Qed.
Lemma lem2618186 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618187 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618188 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618187 h1) (fun h1 : term426 = True => @lem2618186)). Qed.
Lemma lem2618189 : term426 = True.
Proof. exact (EQ_MP (@lem2618188) (@lem2618186)). Qed.
Lemma lem2618190 : term420 = True.
Proof. exact (TRANS (@lem2618185) (@lem2618189)). Qed.
Lemma lem2618191 : True = term420.
Proof. exact (SYM (@lem2618190)). Qed.
Lemma lem2618192 : term420.
Proof. exact (EQ_MP (@lem2618191) (@lem0)). Qed.
Lemma lem2618193 : term423 = term429.
Proof. exact (@lem2618182 (@lem2618192)). Qed.
Lemma lem2618195 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2618196 : term140 = term141.
Proof. exact (@lem2618195 term48 term48). Qed.
Lemma lem2618197 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618198 : term143 = term48.
Proof. exact (EQ_MP (@lem2618197) (@lem940073)). Qed.
Lemma lem2618199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618200 : term141 = term47.
Proof. exact (MK_COMB (@lem2618199) (@lem2618198)). Qed.
Lemma lem2618201 : term140 = term47.
Proof. exact (TRANS (@lem2618196) (@lem2618200)). Qed.
Lemma lem2618203 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618204 : term431 = term43.
Proof. exact (@lem2618203 term48). Qed.
Lemma lem2618205 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2618206 : term432 = term421.
Proof. exact (MK_COMB (@lem2618205) (@lem2618204)). Qed.
Lemma lem2618207 : term429 = term420.
Proof. exact (MK_COMB (@lem2618206) (@lem2618201)). Qed.
Lemma lem2618209 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618210 : term420 = term426.
Proof. exact (@lem2618209 (NUMERAL 0) term48). Qed.
Lemma lem2618211 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618212 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618213 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618212 h1) (fun h1 : term426 = True => @lem2618211)). Qed.
Lemma lem2618214 : term426 = True.
Proof. exact (EQ_MP (@lem2618213) (@lem2618211)). Qed.
Lemma lem2618215 : term420 = True.
Proof. exact (TRANS (@lem2618210) (@lem2618214)). Qed.
Lemma lem2618216 : term429 = True.
Proof. exact (TRANS (@lem2618207) (@lem2618215)). Qed.
Lemma lem2618217 : term423 = True.
Proof. exact (TRANS (@lem2618193) (@lem2618216)). Qed.
Lemma lem2618218 : term420 = True.
Proof. exact (TRANS (@lem2618170) (@lem2618217)). Qed.
Lemma lem2618219 : term419 = True.
Proof. exact (TRANS (@lem2618161) (@lem2618218)). Qed.
Lemma lem2618220 : True = term419.
Proof. exact (SYM (@lem2618219)). Qed.
Lemma lem2618221 : term419.
Proof. exact (EQ_MP (@lem2618220) (@lem0)). Qed.
Lemma lem2618222 (a : int) (x : int) (h1 : term763 a x) : term768 a x.
Proof. exact (conj (@lem2618221) (@lem2618158 a x h1)). Qed.
Lemma lem2618224 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2618225 (a : int) (x : int) : term769 a x.
Proof. exact (@lem2618224 term47 (term37 a x)). Qed.
Lemma lem2618226 (a : int) (x : int) (h1 : term763 a x) : term770 a x.
Proof. exact (@lem2618225 a x (@lem2618222 a x h1)). Qed.
Lemma lem2618227 (a : int) (x : int) : (term771 a x) = (term37 a x).
Proof. exact (@lem1982733 (term37 a x)). Qed.
Lemma lem2618228 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2618229 (a : int) (x : int) : (term772 a x) = (term676 a x).
Proof. exact (MK_COMB (@lem2618228) (@lem2618227 a x)). Qed.
Lemma lem2618230 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2618231 (a : int) (x : int) : (term770 a x) = (term677 a x).
Proof. exact (MK_COMB (@lem2618229 a x) (@lem2618230)). Qed.
Lemma lem2618232 (a : int) (x : int) (h1 : term763 a x) : term677 a x.
Proof. exact (EQ_MP (@lem2618231 a x) (@lem2618226 a x h1)). Qed.
Lemma lem2618234 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2618235 : term419 = term420.
Proof. exact (@lem2618234 term43 term47). Qed.
Lemma lem2618237 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2618238 : term47 = term128.
Proof. exact (@lem2618237 term48). Qed.
Lemma lem2618240 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2618241 : term43 = term243.
Proof. exact (@lem2618240 (NUMERAL 0)). Qed.
Lemma lem2618242 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2618243 : term421 = term422.
Proof. exact (MK_COMB (@lem2618242) (@lem2618241)). Qed.
Lemma lem2618244 : term420 = term423.
Proof. exact (MK_COMB (@lem2618243) (@lem2618238)). Qed.
Lemma lem2618245 : term424.
Proof. exact (@lem1980255 term43 term47 term47 term47). Qed.
Lemma lem2618247 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618248 : term420 = term426.
Proof. exact (@lem2618247 (NUMERAL 0) term48). Qed.
Lemma lem2618249 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618250 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618251 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618250 h1) (fun h1 : term426 = True => @lem2618249)). Qed.
Lemma lem2618252 : term426 = True.
Proof. exact (EQ_MP (@lem2618251) (@lem2618249)). Qed.
Lemma lem2618253 : term420 = True.
Proof. exact (TRANS (@lem2618248) (@lem2618252)). Qed.
Lemma lem2618254 : True = term420.
Proof. exact (SYM (@lem2618253)). Qed.
Lemma lem2618255 : term420.
Proof. exact (EQ_MP (@lem2618254) (@lem0)). Qed.
Lemma lem2618256 : term428.
Proof. exact (@lem2618245 (@lem2618255)). Qed.
Lemma lem2618258 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618259 : term420 = term426.
Proof. exact (@lem2618258 (NUMERAL 0) term48). Qed.
Lemma lem2618260 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618261 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618262 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618261 h1) (fun h1 : term426 = True => @lem2618260)). Qed.
Lemma lem2618263 : term426 = True.
Proof. exact (EQ_MP (@lem2618262) (@lem2618260)). Qed.
Lemma lem2618264 : term420 = True.
Proof. exact (TRANS (@lem2618259) (@lem2618263)). Qed.
Lemma lem2618265 : True = term420.
Proof. exact (SYM (@lem2618264)). Qed.
Lemma lem2618266 : term420.
Proof. exact (EQ_MP (@lem2618265) (@lem0)). Qed.
Lemma lem2618267 : term423 = term429.
Proof. exact (@lem2618256 (@lem2618266)). Qed.
Lemma lem2618269 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2618270 : term140 = term141.
Proof. exact (@lem2618269 term48 term48). Qed.
Lemma lem2618271 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618272 : term143 = term48.
Proof. exact (EQ_MP (@lem2618271) (@lem940073)). Qed.
Lemma lem2618273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618274 : term141 = term47.
Proof. exact (MK_COMB (@lem2618273) (@lem2618272)). Qed.
Lemma lem2618275 : term140 = term47.
Proof. exact (TRANS (@lem2618270) (@lem2618274)). Qed.
Lemma lem2618277 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618278 : term431 = term43.
Proof. exact (@lem2618277 term48). Qed.
Lemma lem2618279 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2618280 : term432 = term421.
Proof. exact (MK_COMB (@lem2618279) (@lem2618278)). Qed.
Lemma lem2618281 : term429 = term420.
Proof. exact (MK_COMB (@lem2618280) (@lem2618275)). Qed.
Lemma lem2618283 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618284 : term420 = term426.
Proof. exact (@lem2618283 (NUMERAL 0) term48). Qed.
Lemma lem2618285 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618286 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618287 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618286 h1) (fun h1 : term426 = True => @lem2618285)). Qed.
Lemma lem2618288 : term426 = True.
Proof. exact (EQ_MP (@lem2618287) (@lem2618285)). Qed.
Lemma lem2618289 : term420 = True.
Proof. exact (TRANS (@lem2618284) (@lem2618288)). Qed.
Lemma lem2618290 : term429 = True.
Proof. exact (TRANS (@lem2618281) (@lem2618289)). Qed.
Lemma lem2618291 : term423 = True.
Proof. exact (TRANS (@lem2618267) (@lem2618290)). Qed.
Lemma lem2618292 : term420 = True.
Proof. exact (TRANS (@lem2618244) (@lem2618291)). Qed.
Lemma lem2618293 : term419 = True.
Proof. exact (TRANS (@lem2618235) (@lem2618292)). Qed.
Lemma lem2618294 : True = term419.
Proof. exact (SYM (@lem2618293)). Qed.
Lemma lem2618295 : term419.
Proof. exact (EQ_MP (@lem2618294) (@lem0)). Qed.
Lemma lem2618296 (a : int) (x : int) (h1 : term763 a x) : term773 a x.
Proof. exact (conj (@lem2618295) (@lem2618156 a x h1)). Qed.
Lemma lem2618298 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2618299 (a : int) (x : int) : term774 a x.
Proof. exact (@lem2618298 term47 (term646 a x)). Qed.
Lemma lem2618300 (a : int) (x : int) (h1 : term763 a x) : term775 a x.
Proof. exact (@lem2618299 a x (@lem2618296 a x h1)). Qed.
Lemma lem2618301 (a : int) (x : int) : (term776 a x) = (term646 a x).
Proof. exact (@lem1982733 (term646 a x)). Qed.
Lemma lem2618302 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2618303 (a : int) (x : int) : (term777 a x) = (term648 a x).
Proof. exact (MK_COMB (@lem2618302) (@lem2618301 a x)). Qed.
Lemma lem2618304 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2618305 (a : int) (x : int) : (term775 a x) = (term649 a x).
Proof. exact (MK_COMB (@lem2618303 a x) (@lem2618304)). Qed.
Lemma lem2618306 (a : int) (x : int) (h1 : term763 a x) : term649 a x.
Proof. exact (EQ_MP (@lem2618305 a x) (@lem2618300 a x h1)). Qed.
Lemma lem2618307 (a : int) (x : int) (h1 : term763 a x) : term778 a x.
Proof. exact (conj (@lem2618306 a x h1) (@lem2618232 a x h1)). Qed.
Lemma lem2618309 (x : real) (y : real) : term445 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2618310 (a : int) (x : int) : term779 a x.
Proof. exact (@lem2618309 (term646 a x) (term37 a x)). Qed.
Lemma lem2618311 (a : int) (x : int) (h1 : term763 a x) : term780 a x.
Proof. exact (@lem2618310 a x (@lem2618307 a x h1)). Qed.
Lemma lem2618312 (a : int) (x : int) : (term781 a x) = (term782 a x).
Proof. exact (@lem1982753 (term198 a) (real_of_int a) (term178 x) (real_of_int x)). Qed.
Lemma lem2618313 (a : int) : (term472 a) = (term473 a).
Proof. exact (@lem1982713 term131 (real_of_int a)). Qed.
Lemma lem2618315 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2618316 : term47 = term128.
Proof. exact (@lem2618315 term48). Qed.
Lemma lem2618318 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2618319 : term131 = term132.
Proof. exact (@lem2618318 term48). Qed.
Lemma lem2618320 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2618321 : term452 = term453.
Proof. exact (MK_COMB (@lem2618320) (@lem2618319)). Qed.
Lemma lem2618322 : term454 = term455.
Proof. exact (MK_COMB (@lem2618321) (@lem2618316)). Qed.
Lemma lem2618323 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2618325 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618326 : term420 = term426.
Proof. exact (@lem2618325 (NUMERAL 0) term48). Qed.
Lemma lem2618327 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618328 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618329 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618328 h1) (fun h1 : term426 = True => @lem2618327)). Qed.
Lemma lem2618330 : term426 = True.
Proof. exact (EQ_MP (@lem2618329) (@lem2618327)). Qed.
Lemma lem2618331 : term420 = True.
Proof. exact (TRANS (@lem2618326) (@lem2618330)). Qed.
Lemma lem2618332 : True = term420.
Proof. exact (SYM (@lem2618331)). Qed.
Lemma lem2618333 : term420.
Proof. exact (EQ_MP (@lem2618332) (@lem0)). Qed.
Lemma lem2618334 : term457.
Proof. exact (@lem2618323 (@lem2618333)). Qed.
Lemma lem2618336 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618337 : term420 = term426.
Proof. exact (@lem2618336 (NUMERAL 0) term48). Qed.
Lemma lem2618338 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618339 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618340 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618339 h1) (fun h1 : term426 = True => @lem2618338)). Qed.
Lemma lem2618341 : term426 = True.
Proof. exact (EQ_MP (@lem2618340) (@lem2618338)). Qed.
Lemma lem2618342 : term420 = True.
Proof. exact (TRANS (@lem2618337) (@lem2618341)). Qed.
Lemma lem2618343 : True = term420.
Proof. exact (SYM (@lem2618342)). Qed.
Lemma lem2618344 : term420.
Proof. exact (EQ_MP (@lem2618343) (@lem0)). Qed.
Lemma lem2618345 : term458.
Proof. exact (@lem2618334 (@lem2618344)). Qed.
Lemma lem2618347 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618348 : term420 = term426.
Proof. exact (@lem2618347 (NUMERAL 0) term48). Qed.
Lemma lem2618349 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618350 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618351 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618350 h1) (fun h1 : term426 = True => @lem2618349)). Qed.
Lemma lem2618352 : term426 = True.
Proof. exact (EQ_MP (@lem2618351) (@lem2618349)). Qed.
Lemma lem2618353 : term420 = True.
Proof. exact (TRANS (@lem2618348) (@lem2618352)). Qed.
Lemma lem2618354 : True = term420.
Proof. exact (SYM (@lem2618353)). Qed.
Lemma lem2618355 : term420.
Proof. exact (EQ_MP (@lem2618354) (@lem0)). Qed.
Lemma lem2618356 : term459.
Proof. exact (@lem2618345 (@lem2618355)). Qed.
Lemma lem2618358 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2618359 : term140 = term141.
Proof. exact (@lem2618358 term48 term48). Qed.
Lemma lem2618360 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618361 : term143 = term48.
Proof. exact (EQ_MP (@lem2618360) (@lem940073)). Qed.
Lemma lem2618362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618363 : term141 = term47.
Proof. exact (MK_COMB (@lem2618362) (@lem2618361)). Qed.
Lemma lem2618364 : term140 = term47.
Proof. exact (TRANS (@lem2618359) (@lem2618363)). Qed.
Lemma lem2618366 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2618367 : term135 = term146.
Proof. exact (@lem2618366 term48 term48). Qed.
Lemma lem2618368 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618369 : term143 = term48.
Proof. exact (EQ_MP (@lem2618368) (@lem940073)). Qed.
Lemma lem2618370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618371 : term141 = term47.
Proof. exact (MK_COMB (@lem2618370) (@lem2618369)). Qed.
Lemma lem2618372 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2618373 : term146 = term131.
Proof. exact (MK_COMB (@lem2618372) (@lem2618371)). Qed.
Lemma lem2618374 : term135 = term131.
Proof. exact (TRANS (@lem2618367) (@lem2618373)). Qed.
Lemma lem2618375 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2618376 : term460 = term452.
Proof. exact (MK_COMB (@lem2618375) (@lem2618374)). Qed.
Lemma lem2618377 : term461 = term454.
Proof. exact (MK_COMB (@lem2618376) (@lem2618364)). Qed.
Lemma lem2618379 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2618380 : term454 = term43.
Proof. exact (@lem2618379 term48). Qed.
Lemma lem2618381 : term461 = term43.
Proof. exact (TRANS (@lem2618377) (@lem2618380)). Qed.
Lemma lem2618382 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2618383 : term463 = term464.
Proof. exact (MK_COMB (@lem2618382) (@lem2618381)). Qed.
Lemma lem2618384 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2618385 : term465 = term431.
Proof. exact (MK_COMB (@lem2618383) (@lem2618384)). Qed.
Lemma lem2618387 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618388 : term431 = term43.
Proof. exact (@lem2618387 term48). Qed.
Lemma lem2618389 : term465 = term43.
Proof. exact (TRANS (@lem2618385) (@lem2618388)). Qed.
Lemma lem2618391 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2618392 : term140 = term141.
Proof. exact (@lem2618391 term48 term48). Qed.
Lemma lem2618393 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618394 : term143 = term48.
Proof. exact (EQ_MP (@lem2618393) (@lem940073)). Qed.
Lemma lem2618395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618396 : term141 = term47.
Proof. exact (MK_COMB (@lem2618395) (@lem2618394)). Qed.
Lemma lem2618397 : term140 = term47.
Proof. exact (TRANS (@lem2618392) (@lem2618396)). Qed.
Lemma lem2618398 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2618399 : term466 = term431.
Proof. exact (MK_COMB (@lem2618398) (@lem2618397)). Qed.
Lemma lem2618401 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618402 : term431 = term43.
Proof. exact (@lem2618401 term48). Qed.
Lemma lem2618403 : term466 = term43.
Proof. exact (TRANS (@lem2618399) (@lem2618402)). Qed.
Lemma lem2618404 : term43 = term466.
Proof. exact (SYM (@lem2618403)). Qed.
Lemma lem2618405 : term465 = term466.
Proof. exact (TRANS (@lem2618389) (@lem2618404)). Qed.
Lemma lem2618406 : term455 = term243.
Proof. exact (@lem2618356 (@lem2618405)). Qed.
Lemma lem2618407 : term454 = term243.
Proof. exact (TRANS (@lem2618322) (@lem2618406)). Qed.
Lemma lem2618409 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2618410 : term243 = term43.
Proof. exact (@lem2618409 term43). Qed.
Lemma lem2618411 : term454 = term43.
Proof. exact (TRANS (@lem2618407) (@lem2618410)). Qed.
Lemma lem2618412 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2618413 : term467 = term464.
Proof. exact (MK_COMB (@lem2618412) (@lem2618411)). Qed.
Lemma lem2618414 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2618415 (a : int) : (term473 a) = (term474 a).
Proof. exact (MK_COMB (@lem2618413) (@lem2618414 a)). Qed.
Lemma lem2618416 (a : int) : (term472 a) = (term474 a).
Proof. exact (TRANS (@lem2618313 a) (@lem2618415 a)). Qed.
Lemma lem2618417 (a : int) : (term474 a) = term43.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2618418 (a : int) : (term472 a) = term43.
Proof. exact (TRANS (@lem2618416 a) (@lem2618417 a)). Qed.
Lemma lem2618419 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2618420 (a : int) : (term475 a) = term45.
Proof. exact (MK_COMB (@lem2618419) (@lem2618418 a)). Qed.
Lemma lem2618421 (x : int) : (term470 x) = (term471 x).
Proof. exact (@lem1982759 (term198 x) (real_of_int x) term131). Qed.
Lemma lem2618422 (x : int) : (term472 x) = (term473 x).
Proof. exact (@lem1982713 term131 (real_of_int x)). Qed.
Lemma lem2618424 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2618425 : term47 = term128.
Proof. exact (@lem2618424 term48). Qed.
Lemma lem2618427 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2618428 : term131 = term132.
Proof. exact (@lem2618427 term48). Qed.
Lemma lem2618429 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2618430 : term452 = term453.
Proof. exact (MK_COMB (@lem2618429) (@lem2618428)). Qed.
Lemma lem2618431 : term454 = term455.
Proof. exact (MK_COMB (@lem2618430) (@lem2618425)). Qed.
Lemma lem2618432 : term456.
Proof. exact (@lem1981473 term131 term47 term47 term47 term43 term47). Qed.
Lemma lem2618434 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618435 : term420 = term426.
Proof. exact (@lem2618434 (NUMERAL 0) term48). Qed.
Lemma lem2618436 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618437 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618438 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618437 h1) (fun h1 : term426 = True => @lem2618436)). Qed.
Lemma lem2618439 : term426 = True.
Proof. exact (EQ_MP (@lem2618438) (@lem2618436)). Qed.
Lemma lem2618440 : term420 = True.
Proof. exact (TRANS (@lem2618435) (@lem2618439)). Qed.
Lemma lem2618441 : True = term420.
Proof. exact (SYM (@lem2618440)). Qed.
Lemma lem2618442 : term420.
Proof. exact (EQ_MP (@lem2618441) (@lem0)). Qed.
Lemma lem2618443 : term457.
Proof. exact (@lem2618432 (@lem2618442)). Qed.
Lemma lem2618445 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618446 : term420 = term426.
Proof. exact (@lem2618445 (NUMERAL 0) term48). Qed.
Lemma lem2618447 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618448 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618449 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618448 h1) (fun h1 : term426 = True => @lem2618447)). Qed.
Lemma lem2618450 : term426 = True.
Proof. exact (EQ_MP (@lem2618449) (@lem2618447)). Qed.
Lemma lem2618451 : term420 = True.
Proof. exact (TRANS (@lem2618446) (@lem2618450)). Qed.
Lemma lem2618452 : True = term420.
Proof. exact (SYM (@lem2618451)). Qed.
Lemma lem2618453 : term420.
Proof. exact (EQ_MP (@lem2618452) (@lem0)). Qed.
Lemma lem2618454 : term458.
Proof. exact (@lem2618443 (@lem2618453)). Qed.
Lemma lem2618456 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618457 : term420 = term426.
Proof. exact (@lem2618456 (NUMERAL 0) term48). Qed.
Lemma lem2618458 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618459 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618460 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618459 h1) (fun h1 : term426 = True => @lem2618458)). Qed.
Lemma lem2618461 : term426 = True.
Proof. exact (EQ_MP (@lem2618460) (@lem2618458)). Qed.
Lemma lem2618462 : term420 = True.
Proof. exact (TRANS (@lem2618457) (@lem2618461)). Qed.
Lemma lem2618463 : True = term420.
Proof. exact (SYM (@lem2618462)). Qed.
Lemma lem2618464 : term420.
Proof. exact (EQ_MP (@lem2618463) (@lem0)). Qed.
Lemma lem2618465 : term459.
Proof. exact (@lem2618454 (@lem2618464)). Qed.
Lemma lem2618467 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2618468 : term140 = term141.
Proof. exact (@lem2618467 term48 term48). Qed.
Lemma lem2618469 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618470 : term143 = term48.
Proof. exact (EQ_MP (@lem2618469) (@lem940073)). Qed.
Lemma lem2618471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618472 : term141 = term47.
Proof. exact (MK_COMB (@lem2618471) (@lem2618470)). Qed.
Lemma lem2618473 : term140 = term47.
Proof. exact (TRANS (@lem2618468) (@lem2618472)). Qed.
Lemma lem2618475 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2618476 : term135 = term146.
Proof. exact (@lem2618475 term48 term48). Qed.
Lemma lem2618477 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618478 : term143 = term48.
Proof. exact (EQ_MP (@lem2618477) (@lem940073)). Qed.
Lemma lem2618479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618480 : term141 = term47.
Proof. exact (MK_COMB (@lem2618479) (@lem2618478)). Qed.
Lemma lem2618481 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2618482 : term146 = term131.
Proof. exact (MK_COMB (@lem2618481) (@lem2618480)). Qed.
Lemma lem2618483 : term135 = term131.
Proof. exact (TRANS (@lem2618476) (@lem2618482)). Qed.
Lemma lem2618484 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2618485 : term460 = term452.
Proof. exact (MK_COMB (@lem2618484) (@lem2618483)). Qed.
Lemma lem2618486 : term461 = term454.
Proof. exact (MK_COMB (@lem2618485) (@lem2618473)). Qed.
Lemma lem2618488 (m : nat) : (term462 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2618489 : term454 = term43.
Proof. exact (@lem2618488 term48). Qed.
Lemma lem2618490 : term461 = term43.
Proof. exact (TRANS (@lem2618486) (@lem2618489)). Qed.
Lemma lem2618491 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2618492 : term463 = term464.
Proof. exact (MK_COMB (@lem2618491) (@lem2618490)). Qed.
Lemma lem2618493 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2618494 : term465 = term431.
Proof. exact (MK_COMB (@lem2618492) (@lem2618493)). Qed.
Lemma lem2618496 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618497 : term431 = term43.
Proof. exact (@lem2618496 term48). Qed.
Lemma lem2618498 : term465 = term43.
Proof. exact (TRANS (@lem2618494) (@lem2618497)). Qed.
Lemma lem2618500 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2618501 : term140 = term141.
Proof. exact (@lem2618500 term48 term48). Qed.
Lemma lem2618502 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618503 : term143 = term48.
Proof. exact (EQ_MP (@lem2618502) (@lem940073)). Qed.
Lemma lem2618504 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618505 : term141 = term47.
Proof. exact (MK_COMB (@lem2618504) (@lem2618503)). Qed.
Lemma lem2618506 : term140 = term47.
Proof. exact (TRANS (@lem2618501) (@lem2618505)). Qed.
Lemma lem2618507 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem2618508 : term466 = term431.
Proof. exact (MK_COMB (@lem2618507) (@lem2618506)). Qed.
Lemma lem2618510 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618511 : term431 = term43.
Proof. exact (@lem2618510 term48). Qed.
Lemma lem2618512 : term466 = term43.
Proof. exact (TRANS (@lem2618508) (@lem2618511)). Qed.
Lemma lem2618513 : term43 = term466.
Proof. exact (SYM (@lem2618512)). Qed.
Lemma lem2618514 : term465 = term466.
Proof. exact (TRANS (@lem2618498) (@lem2618513)). Qed.
Lemma lem2618515 : term455 = term243.
Proof. exact (@lem2618465 (@lem2618514)). Qed.
Lemma lem2618516 : term454 = term243.
Proof. exact (TRANS (@lem2618431) (@lem2618515)). Qed.
Lemma lem2618518 (x : real) : (term149 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2618519 : term243 = term43.
Proof. exact (@lem2618518 term43). Qed.
Lemma lem2618520 : term454 = term43.
Proof. exact (TRANS (@lem2618516) (@lem2618519)). Qed.
Lemma lem2618521 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2618522 : term467 = term464.
Proof. exact (MK_COMB (@lem2618521) (@lem2618520)). Qed.
Lemma lem2618523 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2618524 (x : int) : (term473 x) = (term474 x).
Proof. exact (MK_COMB (@lem2618522) (@lem2618523 x)). Qed.
Lemma lem2618525 (x : int) : (term472 x) = (term474 x).
Proof. exact (TRANS (@lem2618422 x) (@lem2618524 x)). Qed.
Lemma lem2618526 (x : int) : (term474 x) = term43.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2618527 (x : int) : (term472 x) = term43.
Proof. exact (TRANS (@lem2618525 x) (@lem2618526 x)). Qed.
Lemma lem2618528 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2618529 (x : int) : (term475 x) = term45.
Proof. exact (MK_COMB (@lem2618528) (@lem2618527 x)). Qed.
Lemma lem2618530 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2618531 (x : int) : (term471 x) = term476.
Proof. exact (MK_COMB (@lem2618529 x) (@lem2618530)). Qed.
Lemma lem2618532 (x : int) : (term470 x) = term476.
Proof. exact (TRANS (@lem2618421 x) (@lem2618531 x)). Qed.
Lemma lem2618533 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2618534 (x : int) : (term470 x) = term131.
Proof. exact (TRANS (@lem2618532 x) (@lem2618533)). Qed.
Lemma lem2618535 (a : int) (x : int) : (term782 a x) = term476.
Proof. exact (MK_COMB (@lem2618420 a) (@lem2618534 x)). Qed.
Lemma lem2618536 (a : int) (x : int) : (term781 a x) = term476.
Proof. exact (TRANS (@lem2618312 a x) (@lem2618535 a x)). Qed.
Lemma lem2618537 : term476 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem2618538 (a : int) (x : int) : (term781 a x) = term131.
Proof. exact (TRANS (@lem2618536 a x) (@lem2618537)). Qed.
Lemma lem2618539 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2618540 (a : int) (x : int) : (term783 a x) = term478.
Proof. exact (MK_COMB (@lem2618539) (@lem2618538 a x)). Qed.
Lemma lem2618541 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2618542 (a : int) (x : int) : (term780 a x) = term479.
Proof. exact (MK_COMB (@lem2618540 a x) (@lem2618541)). Qed.
Lemma lem2618543 (a : int) (x : int) (h1 : term763 a x) : term479.
Proof. exact (EQ_MP (@lem2618542 a x) (@lem2618311 a x h1)). Qed.
Lemma lem2618545 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2618546 : term479 = term480.
Proof. exact (@lem2618545 term43 term131). Qed.
Lemma lem2618548 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2618549 : term131 = term132.
Proof. exact (@lem2618548 term48). Qed.
Lemma lem2618551 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2618552 : term43 = term243.
Proof. exact (@lem2618551 (NUMERAL 0)). Qed.
Lemma lem2618553 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2618554 : term481 = term482.
Proof. exact (MK_COMB (@lem2618553) (@lem2618552)). Qed.
Lemma lem2618555 : term480 = term483.
Proof. exact (MK_COMB (@lem2618554) (@lem2618549)). Qed.
Lemma lem2618556 : term484.
Proof. exact (@lem1980026 term43 term47 term131 term47). Qed.
Lemma lem2618558 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618559 : term420 = term426.
Proof. exact (@lem2618558 (NUMERAL 0) term48). Qed.
Lemma lem2618560 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618561 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618562 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618561 h1) (fun h1 : term426 = True => @lem2618560)). Qed.
Lemma lem2618563 : term426 = True.
Proof. exact (EQ_MP (@lem2618562) (@lem2618560)). Qed.
Lemma lem2618564 : term420 = True.
Proof. exact (TRANS (@lem2618559) (@lem2618563)). Qed.
Lemma lem2618565 : True = term420.
Proof. exact (SYM (@lem2618564)). Qed.
Lemma lem2618566 : term420.
Proof. exact (EQ_MP (@lem2618565) (@lem0)). Qed.
Lemma lem2618567 : term485.
Proof. exact (@lem2618556 (@lem2618566)). Qed.
Lemma lem2618569 (m : nat) (n : nat) : (term425 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2618570 : term420 = term426.
Proof. exact (@lem2618569 (NUMERAL 0) term48). Qed.
Lemma lem2618571 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618572 (h1 : term427 = (BIT1 0)) : term426 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2618573 : (term427 = (BIT1 0)) = (term426 = True).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618572 h1) (fun h1 : term426 = True => @lem2618571)). Qed.
Lemma lem2618574 : term426 = True.
Proof. exact (EQ_MP (@lem2618573) (@lem2618571)). Qed.
Lemma lem2618575 : term420 = True.
Proof. exact (TRANS (@lem2618570) (@lem2618574)). Qed.
Lemma lem2618576 : True = term420.
Proof. exact (SYM (@lem2618575)). Qed.
Lemma lem2618577 : term420.
Proof. exact (EQ_MP (@lem2618576) (@lem0)). Qed.
Lemma lem2618578 : term483 = term486.
Proof. exact (@lem2618567 (@lem2618577)). Qed.
Lemma lem2618580 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2618581 : term135 = term146.
Proof. exact (@lem2618580 term48 term48). Qed.
Lemma lem2618582 : (term142 = (BIT1 0)) = (term143 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2618583 : term143 = term48.
Proof. exact (EQ_MP (@lem2618582) (@lem940073)). Qed.
Lemma lem2618584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2618585 : term141 = term47.
Proof. exact (MK_COMB (@lem2618584) (@lem2618583)). Qed.
Lemma lem2618586 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2618587 : term146 = term131.
Proof. exact (MK_COMB (@lem2618586) (@lem2618585)). Qed.
Lemma lem2618588 : term135 = term131.
Proof. exact (TRANS (@lem2618581) (@lem2618587)). Qed.
Lemma lem2618590 (x : nat) : (term430 x) = term43.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2618591 : term431 = term43.
Proof. exact (@lem2618590 term48). Qed.
Lemma lem2618592 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2618593 : term487 = term481.
Proof. exact (MK_COMB (@lem2618592) (@lem2618591)). Qed.
Lemma lem2618594 : term486 = term480.
Proof. exact (MK_COMB (@lem2618593) (@lem2618588)). Qed.
Lemma lem2618596 (m : nat) (n : nat) : (term488 m n) = (term489 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2618597 : term480 = term490.
Proof. exact (@lem2618596 (NUMERAL 0) term48). Qed.
Lemma lem2618598 : term427 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2618599 (h1 : term427 = (BIT1 0)) : (term48 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2618600 : (term427 = (BIT1 0)) = ((term48 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term427 = (BIT1 0) => @lem2618599 h1) (fun h1 : (term48 = (NUMERAL 0)) = False => @lem2618598)). Qed.
Lemma lem2618601 : (term48 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2618600) (@lem2618598)). Qed.
Lemma lem2618602 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2618603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2618604 : term491 = (and True).
Proof. exact (MK_COMB (@lem2618603) (@lem2618602)). Qed.
Lemma lem2618605 : term490 = (True /\ False).
Proof. exact (MK_COMB (@lem2618604) (@lem2618601)). Qed.
Lemma lem2618607 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2618608 : term490 = False.
Proof. exact (TRANS (@lem2618605) (@lem2618607)). Qed.
Lemma lem2618609 : term480 = False.
Proof. exact (TRANS (@lem2618597) (@lem2618608)). Qed.
Lemma lem2618610 : term486 = False.
Proof. exact (TRANS (@lem2618594) (@lem2618609)). Qed.
Lemma lem2618611 : term483 = False.
Proof. exact (TRANS (@lem2618578) (@lem2618610)). Qed.
Lemma lem2618612 : term480 = False.
Proof. exact (TRANS (@lem2618555) (@lem2618611)). Qed.
Lemma lem2618613 : term479 = False.
Proof. exact (TRANS (@lem2618546) (@lem2618612)). Qed.
Lemma lem2618614 (a : int) (x : int) (h1 : term763 a x) : False.
Proof. exact (EQ_MP (@lem2618613) (@lem2618543 a x h1)). Qed.
Lemma lem2618615 (a : int) (x : int) (h1 : term765 a x) : False.
Proof. exact (or_elim (@lem2617688 a x h1) (fun h0 : term747 a x => @lem2618151 a x h0) (fun h0 : term763 a x => @lem2618614 a x h0)). Qed.
Lemma lem2618616 (a : int) (x : int) (h1 : term767 a x) : False.
Proof. exact (or_elim (@lem2616763 a x h1) (fun h0 : term706 a x => @lem2617687 a x h0) (fun h0 : term765 a x => @lem2618615 a x h0)). Qed.
Lemma lem2618617 (a : int) (x : int) (h1 : term691 a x) : term691 a x.
Proof. exact (h1). Qed.
Lemma lem2618618 (a : int) (x : int) (h1 : term691 a x) : term767 a x.
Proof. exact (EQ_MP (@lem2616762 a x) (@lem2618617 a x h1)). Qed.
Lemma lem2618619 (a : int) (x : int) (h1 : term691 a x) : (term767 a x) = False.
Proof. exact (prop_ext (fun h2 : term767 a x => @lem2618616 a x h2) (fun h2 : False => @lem2618618 a x h1)). Qed.
Lemma lem2618620 (a : int) (x : int) (h1 : term691 a x) : False.
Proof. exact (EQ_MP (@lem2618619 a x h1) (@lem2618618 a x h1)). Qed.
Lemma lem2618621 (x : int) (a : int) (h1 : term632 x a) : term632 x a.
Proof. exact (h1). Qed.
Lemma lem2618622 (x : int) (a : int) (h1 : term632 x a) : term691 a x.
Proof. exact (EQ_MP (@lem2616285 a x) (@lem2618621 x a h1)). Qed.
Lemma lem2618623 (x : int) (a : int) (h1 : term632 x a) : (term691 a x) = False.
Proof. exact (prop_ext (fun h2 : term691 a x => @lem2618620 a x h2) (fun h2 : False => @lem2618622 x a h1)). Qed.
Lemma lem2618624 (x : int) (a : int) (h1 : term632 x a) : False.
Proof. exact (EQ_MP (@lem2618623 x a h1) (@lem2618622 x a h1)). Qed.
Lemma lem2618625 (x : int) (a : int) : term806 x a.
Proof. exact (fun h0 : term632 x a => @lem2618624 x a h0). Qed.
Lemma lem2618626 (x : int) (a : int) : term807 x a.
Proof. exact (@lem1386578 (term808 x a)). Qed.
Lemma lem2618629 (x : int) (a : int) : term808 x a.
Proof. exact (@lem2618626 x a (@lem2618625 x a)). Qed.
Lemma lem2618630 (x : int) (a : int) : (term631 x a) = (term600 x a).
Proof. exact (SYM (@lem2615849 x a)). Qed.
Lemma lem2618631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2618632 (x : int) (a : int) : (term808 x a) = (term586 x a).
Proof. exact (MK_COMB (@lem2618631) (@lem2618630 x a)). Qed.
Lemma lem2618633 (x : int) (a : int) : term586 x a.
Proof. exact (EQ_MP (@lem2618632 x a) (@lem2618629 x a)). Qed.
Lemma lem2618635 (n : nat) : term809 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem2618636 (n : nat) : (term809 n) = (term810 n).
Proof. exact (eq_refl (term809 n)). Qed.
Lemma lem2618637 (n : nat) : term810 n.
Proof. exact (EQ_MP (@lem2618636 n) (@lem2618635 n)). Qed.
Lemma lem2618639 (n : nat) (h1 : term811 n) : term811 n.
Proof. exact (h1). Qed.
Lemma lem2618640 {A B : Type'} (P : type1413 A B) : term812 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem2618641 {A B : Type'} (P : type1413 A B) : (term812 A B P) = ((term813 A B P) = (term814 A B P)).
Proof. exact (eq_refl (term812 A B P)). Qed.
Lemma lem2618643 (x : int) : term815 x.
Proof. exact (@lem2300452 x). Qed.
Lemma lem2618644 (x : int) : (term815 x) = ((term816 x) = (int_abs x)).
Proof. exact (eq_refl (term815 x)). Qed.
Lemma lem2618646 (m : int) : term817 m.
Proof. exact (@lem2519806 m). Qed.
Lemma lem2618647 (m : int) : (term817 m) = (term818 m).
Proof. exact (eq_refl (term817 m)). Qed.
Lemma lem2618648 (m : int) : term818 m.
Proof. exact (EQ_MP (@lem2618647 m) (@lem2618646 m)). Qed.
Lemma lem2618649 (m : int) (n : int) : term819 m n.
Proof. exact (@lem2618648 m n). Qed.
Lemma lem2618650 (m : int) (n : int) : (term819 m n) = ((term820 m n) = (term821 m n)).
Proof. exact (eq_refl (term819 m n)). Qed.
Lemma lem2618652 (P : int -> Prop) : term822 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem2618653 (P : int -> Prop) : (term822 P) = ((term823 P) = (term824 P)).
Proof. exact (eq_refl (term822 P)). Qed.
Lemma lem2618656 (P : int -> Prop) : (term823 P) = (term824 P).
Proof. exact (EQ_MP (@lem2618653 P) (@lem2618652 P)). Qed.
Lemma lem2618657 (m : int) : (term825 m) = (term826 m).
Proof. exact (@lem2618656 (term827 m)). Qed.
Lemma lem2618658 (n : int) (m : int) : (term828 m n) = (term829 n m).
Proof. exact (eq_refl (term828 m n)). Qed.
Lemma lem2618659 (m : int) : (term830 m) = (term827 m).
Proof. exact (fun_ext (fun n : int => @lem2618658 n m)). Qed.
Lemma lem2618660 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2618661 (m : int) : (term825 m) = (term831 m).
Proof. exact (MK_COMB (@lem2618660) (@lem2618659 m)). Qed.
Lemma lem2618662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2618663 (m : int) : (term832 m) = (term833 m).
Proof. exact (MK_COMB (@lem2618662) (@lem2618661 m)). Qed.
Lemma lem2618664 (n : nat) (m : int) : (term834 m n) = (term835 n m).
Proof. exact (eq_refl (term834 m n)). Qed.
Lemma lem2618665 (m : int) : (term836 m) = (term837 m).
Proof. exact (fun_ext (fun n : nat => @lem2618664 n m)). Qed.
Lemma lem2618666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2618667 (m : int) : (term838 m) = (term839 m).
Proof. exact (MK_COMB (@lem2618666) (@lem2618665 m)). Qed.
Lemma lem2618668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2618669 (m : int) : (term840 m) = (term841 m).
Proof. exact (MK_COMB (@lem2618668) (@lem2618667 m)). Qed.
Lemma lem2618670 (n : nat) (m : int) : (term842 m n) = (term843 n m).
Proof. exact (eq_refl (term842 m n)). Qed.
Lemma lem2618671 (m : int) : (term844 m) = (term845 m).
Proof. exact (fun_ext (fun n : nat => @lem2618670 n m)). Qed.
Lemma lem2618672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2618673 (m : int) : (term846 m) = (term847 m).
Proof. exact (MK_COMB (@lem2618672) (@lem2618671 m)). Qed.
Lemma lem2618674 (m : int) : (term826 m) = (term848 m).
Proof. exact (MK_COMB (@lem2618669 m) (@lem2618673 m)). Qed.
Lemma lem2618675 (m : int) : ((term825 m) = (term826 m)) = ((term831 m) = (term848 m)).
Proof. exact (MK_COMB (@lem2618663 m) (@lem2618674 m)). Qed.
Lemma lem2618676 (m : int) : (term831 m) = (term848 m).
Proof. exact (EQ_MP (@lem2618675 m) (@lem2618657 m)). Qed.
Lemma lem2618677 : term849 = term850.
Proof. exact (fun_ext (fun m : int => @lem2618676 m)). Qed.
Lemma lem2618678 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2618679 : term851 = term852.
Proof. exact (MK_COMB (@lem2618678) (@lem2618677)). Qed.
Lemma lem2618680 : term852 = term851.
Proof. exact (SYM (@lem2618679)). Qed.
Lemma lem2618696 (m : int) (n : int) : (term820 m n) = (term821 m n).
Proof. exact (EQ_MP (@lem2618650 m n) (@lem2618649 m n)). Qed.
Lemma lem2618697 (m : int) (n : nat) : (term853 m n) = (term854 m n).
Proof. exact (@lem2618696 m (int_of_num n)). Qed.
Lemma lem2618698 : int_abs = int_abs.
Proof. exact (eq_refl int_abs). Qed.
Lemma lem2618699 (m : int) (n : nat) : (term855 m n) = (term856 m n).
Proof. exact (MK_COMB (@lem2618698) (@lem2618697 m n)). Qed.
Lemma lem2618701 (x : int) : (term816 x) = (int_abs x).
Proof. exact (EQ_MP (@lem2618644 x) (@lem2618643 x)). Qed.
Lemma lem2618702 (m : int) (n : nat) : (term856 m n) = (term857 m n).
Proof. exact (@lem2618701 (term858 m n)). Qed.
Lemma lem2618703 (m : int) (n : nat) : (term855 m n) = (term857 m n).
Proof. exact (TRANS (@lem2618699 m n) (@lem2618702 m n)). Qed.
Lemma lem2618704 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem2618705 (m : int) (n : nat) : (term859 m n) = (term860 m n).
Proof. exact (MK_COMB (@lem2618704) (@lem2618703 m n)). Qed.
Lemma lem2618706 (m : int) : (int_abs m) = (int_abs m).
Proof. exact (eq_refl (int_abs m)). Qed.
Lemma lem2618707 (n : nat) (m : int) : (term843 n m) = (term835 n m).
Proof. exact (MK_COMB (@lem2618705 m n) (@lem2618706 m)). Qed.
Lemma lem2618708 (m : int) : (term845 m) = (term837 m).
Proof. exact (fun_ext (fun n : nat => @lem2618707 n m)). Qed.
Lemma lem2618709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2618710 (m : int) : (term847 m) = (term839 m).
Proof. exact (MK_COMB (@lem2618709) (@lem2618708 m)). Qed.
Lemma lem2618715 (m : int) : (term841 m) = (term841 m).
Proof. exact (eq_refl (term841 m)). Qed.
Lemma lem2618716 (m : int) : (term848 m) = (term861 m).
Proof. exact (MK_COMB (@lem2618715 m) (@lem2618710 m)). Qed.
Lemma lem2618718 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem2618719 (m : int) : (term861 m) = (term839 m).
Proof. exact (@lem2618718 (term839 m)). Qed.
Lemma lem2618724 (m : int) : (term848 m) = (term839 m).
Proof. exact (TRANS (@lem2618716 m) (@lem2618719 m)). Qed.
Lemma lem2618725 : term850 = term862.
Proof. exact (fun_ext (fun m : int => @lem2618724 m)). Qed.
Lemma lem2618726 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2618727 : term852 = term863.
Proof. exact (MK_COMB (@lem2618726) (@lem2618725)). Qed.
Lemma lem2618732 : term863 = term852.
Proof. exact (SYM (@lem2618727)). Qed.
Lemma lem2618734 {A B : Type'} (P : type1413 A B) : (term813 A B P) = (term814 A B P).
Proof. exact (EQ_MP (@lem2618641 A B P) (@lem2618640 A B P)). Qed.
Lemma lem2618735 (P : type1552) : (term864 P) = (term865 P).
Proof. exact (@lem2618734 int nat P). Qed.
Lemma lem2618736 : term866 = term867.
Proof. exact (@lem2618735 term868). Qed.
Lemma lem2618737 (m : int) : (term869 m) = (term837 m).
Proof. exact (eq_refl (term869 m)). Qed.
Lemma lem2618738 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2618739 (m : int) (n : nat) : (term870 m n) = (term871 m n).
Proof. exact (MK_COMB (@lem2618737 m) (@lem2618738 n)). Qed.
Lemma lem2618740 (n : nat) (m : int) : (term871 m n) = (term835 n m).
Proof. exact (eq_refl (term871 m n)). Qed.
Lemma lem2618741 (n : nat) (m : int) : (term870 m n) = (term835 n m).
Proof. exact (TRANS (@lem2618739 m n) (@lem2618740 n m)). Qed.
Lemma lem2618742 (m : int) : (term872 m) = (term837 m).
Proof. exact (fun_ext (fun n : nat => @lem2618741 n m)). Qed.
Lemma lem2618743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2618744 (m : int) : (term873 m) = (term839 m).
Proof. exact (MK_COMB (@lem2618743) (@lem2618742 m)). Qed.
Lemma lem2618745 : term874 = term862.
Proof. exact (fun_ext (fun m : int => @lem2618744 m)). Qed.
Lemma lem2618746 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2618747 : term866 = term863.
Proof. exact (MK_COMB (@lem2618746) (@lem2618745)). Qed.
Lemma lem2618748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2618749 : term875 = term876.
Proof. exact (MK_COMB (@lem2618748) (@lem2618747)). Qed.
Lemma lem2618750 (m : int) : (term869 m) = (term837 m).
Proof. exact (eq_refl (term869 m)). Qed.
Lemma lem2618751 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2618752 (m : int) (n : nat) : (term870 m n) = (term871 m n).
Proof. exact (MK_COMB (@lem2618750 m) (@lem2618751 n)). Qed.
Lemma lem2618753 (n : nat) (m : int) : (term871 m n) = (term835 n m).
Proof. exact (eq_refl (term871 m n)). Qed.
Lemma lem2618754 (n : nat) (m : int) : (term870 m n) = (term835 n m).
Proof. exact (TRANS (@lem2618752 m n) (@lem2618753 n m)). Qed.
Lemma lem2618755 (n : nat) : (term877 n) = (term878 n).
Proof. exact (fun_ext (fun m : int => @lem2618754 n m)). Qed.
Lemma lem2618756 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2618757 (n : nat) : (term879 n) = (term880 n).
Proof. exact (MK_COMB (@lem2618756) (@lem2618755 n)). Qed.
Lemma lem2618758 : term881 = term882.
Proof. exact (fun_ext (fun n : nat => @lem2618757 n)). Qed.
Lemma lem2618759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2618760 : term867 = term883.
Proof. exact (MK_COMB (@lem2618759) (@lem2618758)). Qed.
Lemma lem2618761 : (term866 = term867) = (term863 = term883).
Proof. exact (MK_COMB (@lem2618749) (@lem2618760)). Qed.
Lemma lem2618762 : term863 = term883.
Proof. exact (EQ_MP (@lem2618761) (@lem2618736)). Qed.
Lemma lem2618763 : term883 = term863.
Proof. exact (SYM (@lem2618762)). Qed.
Lemma lem2618764 (x : int) : term0 x.
Proof. exact (@lem2300522 x). Qed.
Lemma lem2618765 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2618766 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2618765 x) (@lem2618764 x)). Qed.
Lemma lem2618767 (x : int) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem2618769 (n : nat) : term884 n.
Proof. exact (@lem2300474 n). Qed.
Lemma lem2618770 (n : nat) : (term884 n) = ((term885 n) = (int_of_num n)).
Proof. exact (eq_refl (term884 n)). Qed.
Lemma lem2618772 (m : int) : term886 m.
Proof. exact (@lem2395867 m). Qed.
Lemma lem2618773 (m : int) : (term886 m) = ((term887 m) = term32).
Proof. exact (eq_refl (term886 m)). Qed.
Lemma lem2618780 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2618781 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2618782 (n : nat) (h1 : n = (NUMERAL 0)) : (int_of_num n) = term32.
Proof. exact (MK_COMB (@lem2618781) (@lem2618780 n h1)). Qed.
Lemma lem2618783 (m : int) : (div m) = (div m).
Proof. exact (eq_refl (div m)). Qed.
Lemma lem2618784 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term858 m n) = (term887 m).
Proof. exact (MK_COMB (@lem2618783 m) (@lem2618782 n h1)). Qed.
Lemma lem2618786 (m : int) : (term887 m) = term32.
Proof. exact (EQ_MP (@lem2618773 m) (@lem2618772 m)). Qed.
Lemma lem2618787 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term858 m n) = term32.
Proof. exact (TRANS (@lem2618784 m n h1) (@lem2618786 m)). Qed.
Lemma lem2618788 : int_abs = int_abs.
Proof. exact (eq_refl int_abs). Qed.
Lemma lem2618789 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term857 m n) = term888.
Proof. exact (MK_COMB (@lem2618788) (@lem2618787 m n h1)). Qed.
Lemma lem2618791 (n : nat) : (term885 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2618770 n) (@lem2618769 n)). Qed.
Lemma lem2618792 : term888 = term32.
Proof. exact (@lem2618791 (NUMERAL 0)). Qed.
Lemma lem2618793 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term857 m n) = term32.
Proof. exact (TRANS (@lem2618789 m n h1) (@lem2618792)). Qed.
Lemma lem2618794 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem2618795 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term860 m n) = term889.
Proof. exact (MK_COMB (@lem2618794) (@lem2618793 m n h1)). Qed.
Lemma lem2618796 (m : int) : (int_abs m) = (int_abs m).
Proof. exact (eq_refl (int_abs m)). Qed.
Lemma lem2618797 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term835 n m) = (term1 m).
Proof. exact (MK_COMB (@lem2618795 m n h1) (@lem2618796 m)). Qed.
Lemma lem2618799 (x : int) : (term1 x) = True.
Proof. exact (EQ_MP (@lem2618767 x) (@lem2618766 x)). Qed.
Lemma lem2618800 (m : int) : (term1 m) = True.
Proof. exact (@lem2618799 m). Qed.
Lemma lem2618801 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term835 n m) = True.
Proof. exact (TRANS (@lem2618797 m n h1) (@lem2618800 m)). Qed.
Lemma lem2618802 (n : nat) (h1 : n = (NUMERAL 0)) : (term878 n) = term890.
Proof. exact (fun_ext (fun m : int => @lem2618801 m n h1)). Qed.
Lemma lem2618803 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2618804 (n : nat) (h1 : n = (NUMERAL 0)) : (term880 n) = term891.
Proof. exact (MK_COMB (@lem2618803) (@lem2618802 n h1)). Qed.
Lemma lem2618806 {A : Type'} (t : Prop) : (term892 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2618807 (t : Prop) : (term893 t) = t.
Proof. exact (@lem2618806 int t). Qed.
Lemma lem2618808 : term891 = True.
Proof. exact (@lem2618807 True). Qed.
Lemma lem2618809 (n : nat) (h1 : n = (NUMERAL 0)) : (term880 n) = True.
Proof. exact (TRANS (@lem2618804 n h1) (@lem2618808)). Qed.
Lemma lem2618810 (n : nat) (h1 : n = (NUMERAL 0)) : True = (term880 n).
Proof. exact (SYM (@lem2618809 n h1)). Qed.
Lemma lem2618811 (n : nat) (h1 : n = (NUMERAL 0)) : term880 n.
Proof. exact (EQ_MP (@lem2618810 n h1) (@lem0)). Qed.
Lemma lem2618847 (x : int) (a : int) : (term587 x a) = (term588 x a).
Proof. exact (EQ_MP (@lem2615676 x a) (@lem2618633 x a)). Qed.
Lemma lem2618848 (n : nat) (m : int) : (term835 n m) = (term894 n m).
Proof. exact (@lem2618847 (term858 m n) (int_abs m)). Qed.
Lemma lem2618851 (n : nat) : (term878 n) = (term895 n).
Proof. exact (fun_ext (fun m : int => @lem2618848 n m)). Qed.
Lemma lem2618852 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2618853 (n : nat) : (term880 n) = (term896 n).
Proof. exact (MK_COMB (@lem2618852) (@lem2618851 n)). Qed.
Lemma lem2618858 (n : nat) : (term896 n) = (term880 n).
Proof. exact (SYM (@lem2618853 n)). Qed.
Lemma lem2618859 : term897.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem2618860 : term898.
Proof. exact (proj2 (@lem2618859)). Qed.
Lemma lem2618861 : term899.
Proof. exact (proj2 (@lem2618860)). Qed.
Lemma lem2618862 : term900.
Proof. exact (proj2 (@lem2618861)). Qed.
Lemma lem2618892 : term901.
Proof. exact (proj1 (@lem2618862)). Qed.
Lemma lem2618893 (n : nat) : term902 n.
Proof. exact (@lem2618892 n). Qed.
Lemma lem2618894 (n : nat) : (term902 n) = (term903 n).
Proof. exact (eq_refl (term902 n)). Qed.
Lemma lem2618895 (n : nat) : term903 n.
Proof. exact (EQ_MP (@lem2618894 n) (@lem2618893 n)). Qed.
Lemma lem2618896 (n : nat) (h1 : term904 n) : term904 n.
Proof. exact (h1). Qed.
Lemma lem2618897 (n : nat) (h1 : term904 n) : term905 n.
Proof. exact (@lem2618895 n (@lem2618896 n h1)). Qed.
Lemma lem2618898 (n : nat) : (term905 n) = ((term905 n) = True).
Proof. exact (@lem7 (term905 n)). Qed.
Lemma lem2618899 (n : nat) (h1 : term904 n) : (term905 n) = True.
Proof. exact (EQ_MP (@lem2618898 n) (@lem2618897 n h1)). Qed.
Lemma lem2618947 : term906.
Proof. exact (proj1 (@lem2618859)). Qed.
Lemma lem2618948 (n : nat) : term907 n.
Proof. exact (@lem2618947 n). Qed.
Lemma lem2618949 (n : nat) : (term907 n) = (term908 n).
Proof. exact (eq_refl (term907 n)). Qed.
Lemma lem2618950 (n : nat) : term908 n.
Proof. exact (EQ_MP (@lem2618949 n) (@lem2618948 n)). Qed.
Lemma lem2618951 (n : nat) (h1 : term811 n) : term811 n.
Proof. exact (h1). Qed.
Lemma lem2618952 (n : nat) (h1 : term811 n) : term904 n.
Proof. exact (@lem2618950 n (@lem2618951 n h1)). Qed.
Lemma lem2618953 (n : nat) : (term904 n) = ((term904 n) = True).
Proof. exact (@lem7 (term904 n)). Qed.
Lemma lem2618954 (n : nat) (h1 : term811 n) : (term904 n) = True.
Proof. exact (EQ_MP (@lem2618953 n) (@lem2618952 n h1)). Qed.
Lemma lem2618973 (m : nat) : term909 m.
Proof. exact (@lem2307247 m). Qed.
Lemma lem2618974 (m : nat) : (term909 m) = (term910 m).
Proof. exact (eq_refl (term909 m)). Qed.
Lemma lem2618975 (m : nat) : term910 m.
Proof. exact (EQ_MP (@lem2618974 m) (@lem2618973 m)). Qed.
Lemma lem2618976 (m : nat) (n : nat) : term911 m n.
Proof. exact (@lem2618975 m n). Qed.
Lemma lem2618977 (m : nat) (n : nat) : (term911 m n) = ((term912 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term911 m n)). Qed.
Lemma lem2618979 (a : int) : term913 a.
Proof. exact (@lem2611502 a). Qed.
Lemma lem2618980 (a : int) : (term913 a) = (term914 a).
Proof. exact (eq_refl (term913 a)). Qed.
Lemma lem2618981 (a : int) : term914 a.
Proof. exact (EQ_MP (@lem2618980 a) (@lem2618979 a)). Qed.
Lemma lem2618982 (a : int) (b : int) : term915 a b.
Proof. exact (@lem2618981 a b). Qed.
Lemma lem2618983 (b : int) (a : int) : (term915 a b) = (term916 b a).
Proof. exact (eq_refl (term915 a b)). Qed.
Lemma lem2618984 (b : int) (a : int) : term916 b a.
Proof. exact (EQ_MP (@lem2618983 b a) (@lem2618982 a b)). Qed.
Lemma lem2618985 (b : int) (a : int) (c : int) : term917 b a c.
Proof. exact (@lem2618984 b a c). Qed.
Lemma lem2618986 (b : int) (a : int) (c : int) : (term917 b a c) = (term918 b a c).
Proof. exact (eq_refl (term917 b a c)). Qed.
Lemma lem2618987 (b : int) (a : int) (c : int) : term918 b a c.
Proof. exact (EQ_MP (@lem2618986 b a c) (@lem2618985 b a c)). Qed.
Lemma lem2618988 (a : int) (h1 : term30 a) : term30 a.
Proof. exact (h1). Qed.
Lemma lem2618989 (b : int) (c : int) (a : int) (h1 : term30 a) : (term919 b a c) = (term920 b a c).
Proof. exact (@lem2618987 b a c (@lem2618988 a h1)). Qed.
Lemma lem2618995 (a : int) : term921 a.
Proof. exact (@lem2611393 a). Qed.
Lemma lem2618996 (a : int) : (term921 a) = (term922 a).
Proof. exact (eq_refl (term921 a)). Qed.
Lemma lem2618997 (a : int) : term922 a.
Proof. exact (EQ_MP (@lem2618996 a) (@lem2618995 a)). Qed.
Lemma lem2618998 (a : int) (b : int) : term923 a b.
Proof. exact (@lem2618997 a b). Qed.
Lemma lem2618999 (a : int) (b : int) : (term923 a b) = (term924 a b).
Proof. exact (eq_refl (term923 a b)). Qed.
Lemma lem2619000 (a : int) (b : int) : term924 a b.
Proof. exact (EQ_MP (@lem2618999 a b) (@lem2618998 a b)). Qed.
Lemma lem2619001 (a : int) (b : int) (c : int) : term925 a b c.
Proof. exact (@lem2619000 a b c). Qed.
Lemma lem2619002 (a : int) (c : int) (b : int) : (term925 a b c) = (term926 a c b).
Proof. exact (eq_refl (term925 a b c)). Qed.
Lemma lem2619003 (a : int) (c : int) (b : int) : term926 a c b.
Proof. exact (EQ_MP (@lem2619002 a c b) (@lem2619001 a b c)). Qed.
Lemma lem2619004 (a : int) (h1 : term30 a) : term30 a.
Proof. exact (h1). Qed.
Lemma lem2619005 (c : int) (b : int) (a : int) (h1 : term30 a) : (term927 c b a) = (term928 a c b).
Proof. exact (@lem2619003 a c b (@lem2619004 a h1)). Qed.
Lemma lem2619011 (n : nat) : term929 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem2619031 (a : int) (c : int) (b : int) : term926 a c b.
Proof. exact (fun h0 : term30 a => @lem2619005 c b a h0). Qed.
Lemma lem2619032 (n : nat) (m : int) : term930 n m.
Proof. exact (@lem2619031 (int_of_num n) (term89 m) m). Qed.
Lemma lem2619034 (m : nat) (n : nat) : (term912 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2618977 m n) (@lem2618976 m n)). Qed.
Lemma lem2619035 (n : nat) : (term931 n) = (term905 n).
Proof. exact (@lem2619034 (NUMERAL 0) n). Qed.
Lemma lem2619037 (n : nat) : term932 n.
Proof. exact (fun h0 : term904 n => @lem2618899 n h0). Qed.
Lemma lem2619047 (n : nat) : term933 n.
Proof. exact (fun h0 : term811 n => @lem2618954 n h0). Qed.
Lemma lem2619049 (n : nat) (h1 : term811 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2619011 n (@lem2618639 n h1)). Qed.
Lemma lem2619050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2619051 (n : nat) (h1 : term811 n) : (term811 n) = (~ False).
Proof. exact (MK_COMB (@lem2619050) (@lem2619049 n h1)). Qed.
Lemma lem2619053 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2619054 (n : nat) (h1 : term811 n) : (term811 n) = True.
Proof. exact (TRANS (@lem2619051 n h1) (@lem2619053)). Qed.
Lemma lem2619055 (n : nat) (h1 : term811 n) : True = (term811 n).
Proof. exact (SYM (@lem2619054 n h1)). Qed.
Lemma lem2619056 (n : nat) (h1 : term811 n) : term811 n.
Proof. exact (EQ_MP (@lem2619055 n h1) (@lem0)). Qed.
Lemma lem2619057 (n : nat) (h1 : term811 n) : (term904 n) = True.
Proof. exact (@lem2619047 n (@lem2619056 n h1)). Qed.
Lemma lem2619058 (n : nat) (h1 : term811 n) : True = (term904 n).
Proof. exact (SYM (@lem2619057 n h1)). Qed.
Lemma lem2619059 (n : nat) (h1 : term811 n) : term904 n.
Proof. exact (EQ_MP (@lem2619058 n h1) (@lem0)). Qed.
Lemma lem2619060 (n : nat) (h1 : term811 n) : (term905 n) = True.
Proof. exact (@lem2619037 n (@lem2619059 n h1)). Qed.
Lemma lem2619061 (n : nat) (h1 : term811 n) : (term931 n) = True.
Proof. exact (TRANS (@lem2619035 n) (@lem2619060 n h1)). Qed.
Lemma lem2619062 (n : nat) (h1 : term811 n) : True = (term931 n).
Proof. exact (SYM (@lem2619061 n h1)). Qed.
Lemma lem2619063 (n : nat) (h1 : term811 n) : term931 n.
Proof. exact (EQ_MP (@lem2619062 n h1) (@lem0)). Qed.
Lemma lem2619064 (m : int) (n : nat) (h1 : term811 n) : (term934 m n) = (term935 n m).
Proof. exact (@lem2619032 n m (@lem2619063 n h1)). Qed.
Lemma lem2619065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2619066 (m : int) (n : nat) (h1 : term811 n) : (term936 m n) = (term937 n m).
Proof. exact (MK_COMB (@lem2619065) (@lem2619064 m n h1)). Qed.
Lemma lem2619068 (b : int) (a : int) (c : int) : term918 b a c.
Proof. exact (fun h0 : term30 a => @lem2618989 b c a h0). Qed.
Lemma lem2619069 (n : nat) (m : int) : term938 n m.
Proof. exact (@lem2619068 m (int_of_num n) (int_abs m)). Qed.
Lemma lem2619071 (m : nat) (n : nat) : (term912 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2618977 m n) (@lem2618976 m n)). Qed.
Lemma lem2619072 (n : nat) : (term931 n) = (term905 n).
Proof. exact (@lem2619071 (NUMERAL 0) n). Qed.
Lemma lem2619074 (n : nat) : term932 n.
Proof. exact (fun h0 : term904 n => @lem2618899 n h0). Qed.
Lemma lem2619084 (n : nat) : term933 n.
Proof. exact (fun h0 : term811 n => @lem2618954 n h0). Qed.
Lemma lem2619086 (n : nat) (h1 : term811 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2619011 n (@lem2618639 n h1)). Qed.
Lemma lem2619087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2619088 (n : nat) (h1 : term811 n) : (term811 n) = (~ False).
Proof. exact (MK_COMB (@lem2619087) (@lem2619086 n h1)). Qed.
Lemma lem2619090 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2619091 (n : nat) (h1 : term811 n) : (term811 n) = True.
Proof. exact (TRANS (@lem2619088 n h1) (@lem2619090)). Qed.
Lemma lem2619092 (n : nat) (h1 : term811 n) : True = (term811 n).
Proof. exact (SYM (@lem2619091 n h1)). Qed.
Lemma lem2619093 (n : nat) (h1 : term811 n) : term811 n.
Proof. exact (EQ_MP (@lem2619092 n h1) (@lem0)). Qed.
Lemma lem2619094 (n : nat) (h1 : term811 n) : (term904 n) = True.
Proof. exact (@lem2619084 n (@lem2619093 n h1)). Qed.
Lemma lem2619095 (n : nat) (h1 : term811 n) : True = (term904 n).
Proof. exact (SYM (@lem2619094 n h1)). Qed.
Lemma lem2619096 (n : nat) (h1 : term811 n) : term904 n.
Proof. exact (EQ_MP (@lem2619095 n h1) (@lem0)). Qed.
Lemma lem2619097 (n : nat) (h1 : term811 n) : (term905 n) = True.
Proof. exact (@lem2619074 n (@lem2619096 n h1)). Qed.
Lemma lem2619098 (n : nat) (h1 : term811 n) : (term931 n) = True.
Proof. exact (TRANS (@lem2619072 n) (@lem2619097 n h1)). Qed.
Lemma lem2619099 (n : nat) (h1 : term811 n) : True = (term931 n).
Proof. exact (SYM (@lem2619098 n h1)). Qed.
Lemma lem2619100 (n : nat) (h1 : term811 n) : term931 n.
Proof. exact (EQ_MP (@lem2619099 n h1) (@lem0)). Qed.
Lemma lem2619101 (m : int) (n : nat) (h1 : term811 n) : (term939 n m) = (term940 n m).
Proof. exact (@lem2619069 n m (@lem2619100 n h1)). Qed.
Lemma lem2619102 (m : int) (n : nat) (h1 : term811 n) : (term894 n m) = (term941 n m).
Proof. exact (MK_COMB (@lem2619066 m n h1) (@lem2619101 m n h1)). Qed.
Lemma lem2619105 (n : nat) (h1 : term811 n) : (term895 n) = (term942 n).
Proof. exact (fun_ext (fun m : int => @lem2619102 m n h1)). Qed.
Lemma lem2619108 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2619109 (n : nat) (h1 : term811 n) : (term896 n) = (term943 n).
Proof. exact (MK_COMB (@lem2619108) (@lem2619105 n h1)). Qed.
Lemma lem2619116 (n : nat) (h1 : term811 n) : (term943 n) = (term896 n).
Proof. exact (SYM (@lem2619109 n h1)). Qed.
Lemma lem2619118 (n : int) (m : int) : term18 n m.
Proof. exact (@lem2615674 n m (@lem2615666 n m)). Qed.
Lemma lem2619119 (n : nat) (m : int) : term944 n m.
Proof. exact (@lem2619118 (int_of_num n) m). Qed.
Lemma lem2619120 : term897.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem2619121 : term898.
Proof. exact (proj2 (@lem2619120)). Qed.
Lemma lem2619122 : term899.
Proof. exact (proj2 (@lem2619121)). Qed.
Lemma lem2619123 : term900.
Proof. exact (proj2 (@lem2619122)). Qed.
Lemma lem2619153 : term901.
Proof. exact (proj1 (@lem2619123)). Qed.
Lemma lem2619154 (n : nat) : term902 n.
Proof. exact (@lem2619153 n). Qed.
Lemma lem2619155 (n : nat) : (term902 n) = (term903 n).
Proof. exact (eq_refl (term902 n)). Qed.
Lemma lem2619156 (n : nat) : term903 n.
Proof. exact (EQ_MP (@lem2619155 n) (@lem2619154 n)). Qed.
Lemma lem2619157 (n : nat) (h1 : term904 n) : term904 n.
Proof. exact (h1). Qed.
Lemma lem2619158 (n : nat) (h1 : term904 n) : term905 n.
Proof. exact (@lem2619156 n (@lem2619157 n h1)). Qed.
Lemma lem2619159 (n : nat) : (term905 n) = ((term905 n) = True).
Proof. exact (@lem7 (term905 n)). Qed.
Lemma lem2619160 (n : nat) (h1 : term904 n) : (term905 n) = True.
Proof. exact (EQ_MP (@lem2619159 n) (@lem2619158 n h1)). Qed.
Lemma lem2619166 : term945.
Proof. exact (proj1 (@lem2619122)). Qed.
Lemma lem2619167 (n : nat) : term946 n.
Proof. exact (@lem2619166 n). Qed.
Lemma lem2619168 (n : nat) : (term946 n) = (term947 n).
Proof. exact (eq_refl (term946 n)). Qed.
Lemma lem2619169 (n : nat) : term947 n.
Proof. exact (EQ_MP (@lem2619168 n) (@lem2619167 n)). Qed.
Lemma lem2619170 (n : nat) (h1 : term905 n) : term905 n.
Proof. exact (h1). Qed.
Lemma lem2619171 (n : nat) (h1 : term905 n) : term904 n.
Proof. exact (@lem2619169 n (@lem2619170 n h1)). Qed.
Lemma lem2619172 (n : nat) : (term904 n) = ((term904 n) = True).
Proof. exact (@lem7 (term904 n)). Qed.
Lemma lem2619173 (n : nat) (h1 : term905 n) : (term904 n) = True.
Proof. exact (EQ_MP (@lem2619172 n) (@lem2619171 n h1)). Qed.
Lemma lem2619221 : term948.
Proof. exact (proj1 (@lem99082)). Qed.
Lemma lem2619222 (n : nat) : term949 n.
Proof. exact (@lem2619221 n). Qed.
Lemma lem2619223 (n : nat) : (term949 n) = (term950 n).
Proof. exact (eq_refl (term949 n)). Qed.
Lemma lem2619224 (n : nat) : term950 n.
Proof. exact (EQ_MP (@lem2619223 n) (@lem2619222 n)). Qed.
Lemma lem2619225 (n : nat) (h1 : term811 n) : term811 n.
Proof. exact (h1). Qed.
Lemma lem2619226 (n : nat) (h1 : term811 n) : term905 n.
Proof. exact (@lem2619224 n (@lem2619225 n h1)). Qed.
Lemma lem2619227 (n : nat) : (term905 n) = ((term905 n) = True).
Proof. exact (@lem7 (term905 n)). Qed.
Lemma lem2619228 (n : nat) (h1 : term811 n) : (term905 n) = True.
Proof. exact (EQ_MP (@lem2619227 n) (@lem2619226 n h1)). Qed.
Lemma lem2619234 (m : nat) : term909 m.
Proof. exact (@lem2307247 m). Qed.
Lemma lem2619235 (m : nat) : (term909 m) = (term910 m).
Proof. exact (eq_refl (term909 m)). Qed.
Lemma lem2619236 (m : nat) : term910 m.
Proof. exact (EQ_MP (@lem2619235 m) (@lem2619234 m)). Qed.
Lemma lem2619237 (m : nat) (n : nat) : term911 m n.
Proof. exact (@lem2619236 m n). Qed.
Lemma lem2619238 (m : nat) (n : nat) : (term911 m n) = ((term912 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term911 m n)). Qed.
Lemma lem2619240 (n : nat) : term929 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem2619256 (m : nat) (n : nat) : (term912 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2619238 m n) (@lem2619237 m n)). Qed.
Lemma lem2619257 (n : nat) : (term931 n) = (term905 n).
Proof. exact (@lem2619256 (NUMERAL 0) n). Qed.
Lemma lem2619259 (n : nat) : term932 n.
Proof. exact (fun h0 : term904 n => @lem2619160 n h0). Qed.
Lemma lem2619261 (n : nat) : term951 n.
Proof. exact (fun h0 : term905 n => @lem2619173 n h0). Qed.
Lemma lem2619271 (n : nat) : term952 n.
Proof. exact (fun h0 : term811 n => @lem2619228 n h0). Qed.
Lemma lem2619273 (n : nat) (h1 : term811 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2619240 n (@lem2618639 n h1)). Qed.
Lemma lem2619274 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2619275 (n : nat) (h1 : term811 n) : (term811 n) = (~ False).
Proof. exact (MK_COMB (@lem2619274) (@lem2619273 n h1)). Qed.
Lemma lem2619277 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2619278 (n : nat) (h1 : term811 n) : (term811 n) = True.
Proof. exact (TRANS (@lem2619275 n h1) (@lem2619277)). Qed.
Lemma lem2619279 (n : nat) (h1 : term811 n) : True = (term811 n).
Proof. exact (SYM (@lem2619278 n h1)). Qed.
Lemma lem2619280 (n : nat) (h1 : term811 n) : term811 n.
Proof. exact (EQ_MP (@lem2619279 n h1) (@lem0)). Qed.
Lemma lem2619281 (n : nat) (h1 : term811 n) : (term905 n) = True.
Proof. exact (@lem2619271 n (@lem2619280 n h1)). Qed.
Lemma lem2619282 (n : nat) (h1 : term811 n) : True = (term905 n).
Proof. exact (SYM (@lem2619281 n h1)). Qed.
Lemma lem2619283 (n : nat) (h1 : term811 n) : term905 n.
Proof. exact (EQ_MP (@lem2619282 n h1) (@lem0)). Qed.
Lemma lem2619284 (n : nat) (h1 : term811 n) : (term904 n) = True.
Proof. exact (@lem2619261 n (@lem2619283 n h1)). Qed.
Lemma lem2619285 (n : nat) (h1 : term811 n) : True = (term904 n).
Proof. exact (SYM (@lem2619284 n h1)). Qed.
Lemma lem2619286 (n : nat) (h1 : term811 n) : term904 n.
Proof. exact (EQ_MP (@lem2619285 n h1) (@lem0)). Qed.
Lemma lem2619287 (n : nat) (h1 : term811 n) : (term905 n) = True.
Proof. exact (@lem2619259 n (@lem2619286 n h1)). Qed.
Lemma lem2619288 (n : nat) (h1 : term811 n) : (term931 n) = True.
Proof. exact (TRANS (@lem2619257 n) (@lem2619287 n h1)). Qed.
Lemma lem2619289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2619290 (n : nat) (h1 : term811 n) : (term953 n) = (and True).
Proof. exact (MK_COMB (@lem2619289) (@lem2619288 n h1)). Qed.
Lemma lem2619291 (m : int) (n : nat) : (term954 m n) = (term954 m n).
Proof. exact (eq_refl (term954 m n)). Qed.
Lemma lem2619292 (m : int) (n : nat) (h1 : term811 n) : (term955 m n) = (term956 m n).
Proof. exact (MK_COMB (@lem2619290 n h1) (@lem2619291 m n)). Qed.
Lemma lem2619294 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2619295 (m : int) (n : nat) : (term956 m n) = (term954 m n).
Proof. exact (@lem2619294 (term954 m n)). Qed.
Lemma lem2619296 (m : int) (n : nat) (h1 : term811 n) : (term955 m n) = (term954 m n).
Proof. exact (TRANS (@lem2619292 m n h1) (@lem2619295 m n)). Qed.
Lemma lem2619297 (m : int) (n : nat) (h1 : term811 n) : (term954 m n) = (term955 m n).
Proof. exact (SYM (@lem2619296 m n h1)). Qed.
Lemma lem2619299 (y : int) (x : int) (z : int) : term8 y x z.
Proof. exact (EQ_MP (@lem2611679 y x z) (@lem2611678 y x z)). Qed.
Lemma lem2619300 (m : int) (n : nat) : term957 m n.
Proof. exact (@lem2619299 term40 (int_abs m) (int_of_num n)). Qed.
Lemma lem2619304 (x : int) : (term1 x) = True.
Proof. exact (EQ_MP (@lem2611649 x) (@lem2611648 x)). Qed.
Lemma lem2619305 (m : int) : (term1 m) = True.
Proof. exact (@lem2619304 m). Qed.
Lemma lem2619306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2619307 (m : int) : (term958 m) = (and True).
Proof. exact (MK_COMB (@lem2619306) (@lem2619305 m)). Qed.
Lemma lem2619308 (n : nat) : (term959 n) = (term959 n).
Proof. exact (eq_refl (term959 n)). Qed.
Lemma lem2619309 (m : int) (n : nat) : (term960 m n) = (term961 n).
Proof. exact (MK_COMB (@lem2619307 m) (@lem2619308 n)). Qed.
Lemma lem2619311 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2619312 (n : nat) : (term961 n) = (term959 n).
Proof. exact (@lem2619311 (term959 n)). Qed.
Lemma lem2619313 (m : int) (n : nat) : (term960 m n) = (term959 n).
Proof. exact (TRANS (@lem2619309 m n) (@lem2619312 n)). Qed.
Lemma lem2619314 (m : int) (n : nat) : (term959 n) = (term960 m n).
Proof. exact (SYM (@lem2619313 m n)). Qed.
Lemma lem2619315 : term897.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem2619316 : term898.
Proof. exact (proj2 (@lem2619315)). Qed.
Lemma lem2619317 : term899.
Proof. exact (proj2 (@lem2619316)). Qed.
Lemma lem2619318 : term900.
Proof. exact (proj2 (@lem2619317)). Qed.
Lemma lem2619348 : term901.
Proof. exact (proj1 (@lem2619318)). Qed.
Lemma lem2619349 (n : nat) : term902 n.
Proof. exact (@lem2619348 n). Qed.
Lemma lem2619350 (n : nat) : (term902 n) = (term903 n).
Proof. exact (eq_refl (term902 n)). Qed.
Lemma lem2619351 (n : nat) : term903 n.
Proof. exact (EQ_MP (@lem2619350 n) (@lem2619349 n)). Qed.
Lemma lem2619352 (n : nat) (h1 : term904 n) : term904 n.
Proof. exact (h1). Qed.
Lemma lem2619353 (n : nat) (h1 : term904 n) : term905 n.
Proof. exact (@lem2619351 n (@lem2619352 n h1)). Qed.
Lemma lem2619354 (n : nat) : (term905 n) = ((term905 n) = True).
Proof. exact (@lem7 (term905 n)). Qed.
Lemma lem2619355 (n : nat) (h1 : term904 n) : (term905 n) = True.
Proof. exact (EQ_MP (@lem2619354 n) (@lem2619353 n h1)). Qed.
Lemma lem2619361 : term945.
Proof. exact (proj1 (@lem2619317)). Qed.
Lemma lem2619362 (n : nat) : term946 n.
Proof. exact (@lem2619361 n). Qed.
Lemma lem2619363 (n : nat) : (term946 n) = (term947 n).
Proof. exact (eq_refl (term946 n)). Qed.
Lemma lem2619364 (n : nat) : term947 n.
Proof. exact (EQ_MP (@lem2619363 n) (@lem2619362 n)). Qed.
Lemma lem2619365 (n : nat) (h1 : term905 n) : term905 n.
Proof. exact (h1). Qed.
Lemma lem2619366 (n : nat) (h1 : term905 n) : term904 n.
Proof. exact (@lem2619364 n (@lem2619365 n h1)). Qed.
Lemma lem2619367 (n : nat) : (term904 n) = ((term904 n) = True).
Proof. exact (@lem7 (term904 n)). Qed.
Lemma lem2619368 (n : nat) (h1 : term905 n) : (term904 n) = True.
Proof. exact (EQ_MP (@lem2619367 n) (@lem2619366 n h1)). Qed.
Lemma lem2619403 : term906.
Proof. exact (proj1 (@lem2619315)). Qed.
Lemma lem2619404 (n : nat) : term907 n.
Proof. exact (@lem2619403 n). Qed.
Lemma lem2619405 (n : nat) : (term907 n) = (term908 n).
Proof. exact (eq_refl (term907 n)). Qed.
Lemma lem2619406 (n : nat) : term908 n.
Proof. exact (EQ_MP (@lem2619405 n) (@lem2619404 n)). Qed.
Lemma lem2619407 (n : nat) (h1 : term811 n) : term811 n.
Proof. exact (h1). Qed.
Lemma lem2619408 (n : nat) (h1 : term811 n) : term904 n.
Proof. exact (@lem2619406 n (@lem2619407 n h1)). Qed.
Lemma lem2619409 (n : nat) : (term904 n) = ((term904 n) = True).
Proof. exact (@lem7 (term904 n)). Qed.
Lemma lem2619410 (n : nat) (h1 : term811 n) : (term904 n) = True.
Proof. exact (EQ_MP (@lem2619409 n) (@lem2619408 n h1)). Qed.
Lemma lem2619429 (m : nat) : term962 m.
Proof. exact (@lem2307222 m). Qed.
Lemma lem2619430 (m : nat) : (term962 m) = (term963 m).
Proof. exact (eq_refl (term962 m)). Qed.
Lemma lem2619431 (m : nat) : term963 m.
Proof. exact (EQ_MP (@lem2619430 m) (@lem2619429 m)). Qed.
Lemma lem2619432 (m : nat) (n : nat) : term964 m n.
Proof. exact (@lem2619431 m n). Qed.
Lemma lem2619433 (m : nat) (n : nat) : (term964 m n) = ((term965 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term964 m n)). Qed.
Lemma lem2619435 (n : nat) : term929 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem2619449 (m : nat) (n : nat) : (term965 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2619433 m n) (@lem2619432 m n)). Qed.
Lemma lem2619450 (n : nat) : (term959 n) = (term904 n).
Proof. exact (@lem2619449 term48 n). Qed.
Lemma lem2619452 (n : nat) : term951 n.
Proof. exact (fun h0 : term905 n => @lem2619368 n h0). Qed.
Lemma lem2619454 (n : nat) : term932 n.
Proof. exact (fun h0 : term904 n => @lem2619355 n h0). Qed.
Lemma lem2619464 (n : nat) : term933 n.
Proof. exact (fun h0 : term811 n => @lem2619410 n h0). Qed.
Lemma lem2619466 (n : nat) (h1 : term811 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2619435 n (@lem2618639 n h1)). Qed.
Lemma lem2619467 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2619468 (n : nat) (h1 : term811 n) : (term811 n) = (~ False).
Proof. exact (MK_COMB (@lem2619467) (@lem2619466 n h1)). Qed.
Lemma lem2619470 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2619471 (n : nat) (h1 : term811 n) : (term811 n) = True.
Proof. exact (TRANS (@lem2619468 n h1) (@lem2619470)). Qed.
Lemma lem2619472 (n : nat) (h1 : term811 n) : True = (term811 n).
Proof. exact (SYM (@lem2619471 n h1)). Qed.
Lemma lem2619473 (n : nat) (h1 : term811 n) : term811 n.
Proof. exact (EQ_MP (@lem2619472 n h1) (@lem0)). Qed.
Lemma lem2619474 (n : nat) (h1 : term811 n) : (term904 n) = True.
Proof. exact (@lem2619464 n (@lem2619473 n h1)). Qed.
Lemma lem2619475 (n : nat) (h1 : term811 n) : True = (term904 n).
Proof. exact (SYM (@lem2619474 n h1)). Qed.
Lemma lem2619476 (n : nat) (h1 : term811 n) : term904 n.
Proof. exact (EQ_MP (@lem2619475 n h1) (@lem0)). Qed.
Lemma lem2619477 (n : nat) (h1 : term811 n) : (term905 n) = True.
Proof. exact (@lem2619454 n (@lem2619476 n h1)). Qed.
Lemma lem2619478 (n : nat) (h1 : term811 n) : True = (term905 n).
Proof. exact (SYM (@lem2619477 n h1)). Qed.
Lemma lem2619479 (n : nat) (h1 : term811 n) : term905 n.
Proof. exact (EQ_MP (@lem2619478 n h1) (@lem0)). Qed.
Lemma lem2619480 (n : nat) (h1 : term811 n) : (term904 n) = True.
Proof. exact (@lem2619452 n (@lem2619479 n h1)). Qed.
Lemma lem2619481 (n : nat) (h1 : term811 n) : (term959 n) = True.
Proof. exact (TRANS (@lem2619450 n) (@lem2619480 n h1)). Qed.
Lemma lem2619482 (n : nat) (h1 : term811 n) : True = (term959 n).
Proof. exact (SYM (@lem2619481 n h1)). Qed.
Lemma lem2619483 (n : nat) (h1 : term811 n) : term959 n.
Proof. exact (EQ_MP (@lem2619482 n h1) (@lem0)). Qed.
Lemma lem2619484 (m : int) (n : nat) (h1 : term811 n) : term960 m n.
Proof. exact (EQ_MP (@lem2619314 m n) (@lem2619483 n h1)). Qed.
Lemma lem2619485 (m : int) (n : nat) (h1 : term811 n) : term954 m n.
Proof. exact (@lem2619300 m n (@lem2619484 m n h1)). Qed.
Lemma lem2619486 (m : int) (n : nat) (h1 : term811 n) : term955 m n.
Proof. exact (EQ_MP (@lem2619297 m n h1) (@lem2619485 m n h1)). Qed.
Lemma lem2619487 (m : int) (n : nat) (h1 : term811 n) : term941 n m.
Proof. exact (@lem2619119 n m (@lem2619486 m n h1)). Qed.
Lemma lem2619492 (n : nat) (h1 : term811 n) : term943 n.
Proof. exact (fun m : int => @lem2619487 m n h1). Qed.
Lemma lem2619493 (n : nat) (h1 : term811 n) : term896 n.
Proof. exact (EQ_MP (@lem2619116 n h1) (@lem2619492 n h1)). Qed.
Lemma lem2619495 (n : nat) (h1 : term811 n) : term880 n.
Proof. exact (EQ_MP (@lem2618858 n) (@lem2619493 n h1)). Qed.
Lemma lem2619496 (n : nat) : term880 n.
Proof. exact (or_elim (@lem2618637 n) (fun h0 : n = (NUMERAL 0) => @lem2618811 n h0) (fun h0 : term811 n => @lem2619495 n h0)). Qed.
Lemma lem2619501 : term883.
Proof. exact (fun n : nat => @lem2619496 n). Qed.
Lemma lem2619502 : term863.
Proof. exact (EQ_MP (@lem2618763) (@lem2619501)). Qed.
Lemma lem2619503 : term852.
Proof. exact (EQ_MP (@lem2618732) (@lem2619502)). Qed.
Lemma lem2619504 : term851.
Proof. exact (EQ_MP (@lem2618680) (@lem2619503)). Qed.
