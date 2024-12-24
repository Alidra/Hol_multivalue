Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_PARTIAL_SUC_term_abbrevs.
Require Import ADD1_spec.
Require Import ADD_CLAUSES_spec.
Require Import INT_POS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import NOT_LT_spec.
Require Import SUM_CLAUSES_NUMSEG_spec.
Require Import SUM_TRIV_NUMSEG_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
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
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
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
Require Import thm1988318_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm7_spec.
Require Import thm706821_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7226631 (m : nat) (h1 : (S m) = (term0 m)) : (S m) = (term0 m).
Proof. exact (h1). Qed.
Lemma lem7226632 (m : nat) (h1 : (S m) = (term0 m)) : (term0 m) = (S m).
Proof. exact (SYM (@lem7226631 m h1)). Qed.
Lemma lem7226633 (m : nat) (h1 : (term0 m) = (S m)) : (term0 m) = (S m).
Proof. exact (h1). Qed.
Lemma lem7226634 (m : nat) (h1 : (term0 m) = (S m)) : (S m) = (term0 m).
Proof. exact (SYM (@lem7226633 m h1)). Qed.
Lemma lem7226635 (m : nat) : ((S m) = (term0 m)) = ((term0 m) = (S m)).
Proof. exact (prop_ext (fun h1 : (S m) = (term0 m) => @lem7226632 m h1) (fun h1 : (term0 m) = (S m) => @lem7226634 m h1)). Qed.
Lemma lem7226636 : term1 = term2.
Proof. exact (fun_ext (fun m : nat => @lem7226635 m)). Qed.
Lemma lem7226637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7226638 : term3 = term4.
Proof. exact (MK_COMB (@lem7226637) (@lem7226636)). Qed.
Lemma lem7226639 : term4.
Proof. exact (EQ_MP (@lem7226638) (@lem80621)). Qed.
Lemma lem7226652 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem7226653 (n : nat) : (S n) = (term0 n).
Proof. exact (@lem7226652 n). Qed.
Lemma lem7226654 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem7226670 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem7226654 n) (@lem7226653 n)). Qed.
Lemma lem7226672 (m : nat) (n : nat) : (Peano.lt m n) = (term7 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7226673 (n : nat) : (term6 n) = (term8 n).
Proof. exact (@lem7226672 n (term0 n)). Qed.
Lemma lem7226675 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7226676 (n : nat) : (term11 n) = (term12 n).
Proof. exact (@lem7226675 n term13). Qed.
Lemma lem7226677 (n : nat) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem7226678 (n : nat) : (term8 n) = (term15 n).
Proof. exact (MK_COMB (@lem7226677 n) (@lem7226676 n)). Qed.
Lemma lem7226679 (n : nat) : (term6 n) = (term15 n).
Proof. exact (TRANS (@lem7226673 n) (@lem7226678 n)). Qed.
Lemma lem7226680 (n : nat) : (term5 n) = (term15 n).
Proof. exact (TRANS (@lem7226670 n) (@lem7226679 n)). Qed.
Lemma lem7226681 (n : nat) : term16 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem7226682 (n : nat) : (term16 n) = (term17 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem7226683 (n : nat) : term17 n.
Proof. exact (EQ_MP (@lem7226682 n) (@lem7226681 n)). Qed.
Lemma lem7226684 (_96851 : int) : (term18 _96851) = (term19 _96851).
Proof. exact (@lem2318604 (term19 _96851)). Qed.
Lemma lem7226707 (_96851 : int) : (term20 _96851) = (term21 _96851).
Proof. exact (@lem17362 (term22 _96851) (term23 _96851)). Qed.
Lemma lem7226710 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7226711 (_96851 : int) : (term22 _96851) = (term25 _96851).
Proof. exact (@lem7226710 term26 _96851). Qed.
Lemma lem7226713 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7226714 : term28 = term29.
Proof. exact (@lem7226713 (NUMERAL 0)). Qed.
Lemma lem7226715 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7226716 : term30 = term31.
Proof. exact (MK_COMB (@lem7226715) (@lem7226714)). Qed.
Lemma lem7226717 (_96851 : int) : (real_of_int _96851) = (real_of_int _96851).
Proof. exact (eq_refl (real_of_int _96851)). Qed.
Lemma lem7226718 (_96851 : int) : (term25 _96851) = (term32 _96851).
Proof. exact (MK_COMB (@lem7226716) (@lem7226717 _96851)). Qed.
Lemma lem7226720 (_96851 : int) : (term22 _96851) = (term32 _96851).
Proof. exact (TRANS (@lem7226711 _96851) (@lem7226718 _96851)). Qed.
Lemma lem7226722 (y : int) (x : int) : (term33 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem7226723 (_96851 : int) : (term34 _96851) = (term35 _96851).
Proof. exact (@lem7226722 (term36 _96851) _96851). Qed.
Lemma lem7226725 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7226726 (_96851 : int) : (term35 _96851) = (term37 _96851).
Proof. exact (@lem7226725 (term36 _96851) _96851). Qed.
Lemma lem7226728 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7226729 (_96851 : int) : (term40 _96851) = (term41 _96851).
Proof. exact (@lem7226728 _96851 term42). Qed.
Lemma lem7226731 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7226732 : term43 = term44.
Proof. exact (@lem7226731 term13). Qed.
Lemma lem7226733 (_96851 : int) : (term45 _96851) = (term45 _96851).
Proof. exact (eq_refl (term45 _96851)). Qed.
Lemma lem7226734 (_96851 : int) : (term41 _96851) = (term46 _96851).
Proof. exact (MK_COMB (@lem7226733 _96851) (@lem7226732)). Qed.
Lemma lem7226735 (_96851 : int) : (term40 _96851) = (term46 _96851).
Proof. exact (TRANS (@lem7226729 _96851) (@lem7226734 _96851)). Qed.
Lemma lem7226736 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7226737 (_96851 : int) : (term47 _96851) = (term48 _96851).
Proof. exact (MK_COMB (@lem7226736) (@lem7226735 _96851)). Qed.
Lemma lem7226738 (_96851 : int) : (real_of_int _96851) = (real_of_int _96851).
Proof. exact (eq_refl (real_of_int _96851)). Qed.
Lemma lem7226739 (_96851 : int) : (term37 _96851) = (term49 _96851).
Proof. exact (MK_COMB (@lem7226737 _96851) (@lem7226738 _96851)). Qed.
Lemma lem7226740 (_96851 : int) : (term35 _96851) = (term49 _96851).
Proof. exact (TRANS (@lem7226726 _96851) (@lem7226739 _96851)). Qed.
Lemma lem7226741 (_96851 : int) : (term34 _96851) = (term49 _96851).
Proof. exact (TRANS (@lem7226723 _96851) (@lem7226740 _96851)). Qed.
Lemma lem7226742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7226743 (_96851 : int) : (term50 _96851) = (term51 _96851).
Proof. exact (MK_COMB (@lem7226742) (@lem7226720 _96851)). Qed.
Lemma lem7226744 (_96851 : int) : (term21 _96851) = (term52 _96851).
Proof. exact (MK_COMB (@lem7226743 _96851) (@lem7226741 _96851)). Qed.
Lemma lem7226745 (_96851 : int) : (term20 _96851) = (term52 _96851).
Proof. exact (TRANS (@lem7226707 _96851) (@lem7226744 _96851)). Qed.
Lemma lem7226749 (t : Prop) : (term53 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7226765 (_96851 : int) : (term54 _96851) = (term52 _96851).
Proof. exact (@lem7226749 (term52 _96851)). Qed.
Lemma lem7226766 (_96851 : int) : (term32 _96851) = (term55 _96851).
Proof. exact (@lem1988287 (real_of_int _96851) term29). Qed.
Lemma lem7226772 (_96851 : int) : (term56 _96851) = (term57 _96851).
Proof. exact (@lem1982792 (real_of_int _96851) term29). Qed.
Lemma lem7226774 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7226775 : term29 = term59.
Proof. exact (@lem7226774 (NUMERAL 0)). Qed.
Lemma lem7226777 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7226778 : term62 = term63.
Proof. exact (@lem7226777 term13). Qed.
Lemma lem7226779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7226780 : term64 = term65.
Proof. exact (MK_COMB (@lem7226779) (@lem7226778)). Qed.
Lemma lem7226781 : term66 = term67.
Proof. exact (MK_COMB (@lem7226780) (@lem7226775)). Qed.
Lemma lem7226782 : term67 = term68.
Proof. exact (@lem1981613 term62 term29 term44 term44). Qed.
Lemma lem7226784 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7226785 : term71 = term72.
Proof. exact (@lem7226784 term13 term13). Qed.
Lemma lem7226786 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7226787 : term74 = term13.
Proof. exact (EQ_MP (@lem7226786) (@lem940073)). Qed.
Lemma lem7226788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7226789 : term72 = term44.
Proof. exact (MK_COMB (@lem7226788) (@lem7226787)). Qed.
Lemma lem7226790 : term71 = term44.
Proof. exact (TRANS (@lem7226785) (@lem7226789)). Qed.
Lemma lem7226792 (x : nat) : (term75 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7226793 : term66 = term29.
Proof. exact (@lem7226792 term13). Qed.
Lemma lem7226794 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7226795 : term76 = term77.
Proof. exact (MK_COMB (@lem7226794) (@lem7226793)). Qed.
Lemma lem7226796 : term68 = term59.
Proof. exact (MK_COMB (@lem7226795) (@lem7226790)). Qed.
Lemma lem7226797 : term67 = term59.
Proof. exact (TRANS (@lem7226782) (@lem7226796)). Qed.
Lemma lem7226798 : term66 = term59.
Proof. exact (TRANS (@lem7226781) (@lem7226797)). Qed.
Lemma lem7226800 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7226801 : term59 = term29.
Proof. exact (@lem7226800 term29). Qed.
Lemma lem7226802 : term66 = term29.
Proof. exact (TRANS (@lem7226798) (@lem7226801)). Qed.
Lemma lem7226803 (_96851 : int) : (term45 _96851) = (term45 _96851).
Proof. exact (eq_refl (term45 _96851)). Qed.
Lemma lem7226804 (_96851 : int) : (term57 _96851) = (term79 _96851).
Proof. exact (MK_COMB (@lem7226803 _96851) (@lem7226802)). Qed.
Lemma lem7226805 (_96851 : int) : (term79 _96851) = (real_of_int _96851).
Proof. exact (@lem1982723 (real_of_int _96851)). Qed.
Lemma lem7226806 (_96851 : int) : (term57 _96851) = (real_of_int _96851).
Proof. exact (TRANS (@lem7226804 _96851) (@lem7226805 _96851)). Qed.
Lemma lem7226808 (_96851 : int) : (term56 _96851) = (real_of_int _96851).
Proof. exact (TRANS (@lem7226772 _96851) (@lem7226806 _96851)). Qed.
Lemma lem7226809 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7226810 (_96851 : int) : (term80 _96851) = (term81 _96851).
Proof. exact (MK_COMB (@lem7226809) (@lem7226808 _96851)). Qed.
Lemma lem7226811 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7226812 (_96851 : int) : (term55 _96851) = (term82 _96851).
Proof. exact (MK_COMB (@lem7226810 _96851) (@lem7226811)). Qed.
Lemma lem7226813 (_96851 : int) : (term32 _96851) = (term82 _96851).
Proof. exact (TRANS (@lem7226766 _96851) (@lem7226812 _96851)). Qed.
Lemma lem7226814 (_96851 : int) : (term49 _96851) = (term83 _96851).
Proof. exact (@lem1988287 (real_of_int _96851) (term46 _96851)). Qed.
Lemma lem7226826 (_96851 : int) : (term84 _96851) = (term85 _96851).
Proof. exact (@lem1982792 (real_of_int _96851) (term46 _96851)). Qed.
Lemma lem7226827 (_96851 : int) : (term86 _96851) = (term87 _96851).
Proof. exact (@lem1982781 (real_of_int _96851) term62 term44). Qed.
Lemma lem7226829 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7226830 : term44 = term88.
Proof. exact (@lem7226829 term13). Qed.
Lemma lem7226832 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7226833 : term62 = term63.
Proof. exact (@lem7226832 term13). Qed.
Lemma lem7226834 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7226835 : term64 = term65.
Proof. exact (MK_COMB (@lem7226834) (@lem7226833)). Qed.
Lemma lem7226836 : term89 = term90.
Proof. exact (MK_COMB (@lem7226835) (@lem7226830)). Qed.
Lemma lem7226837 : term90 = term91.
Proof. exact (@lem1981613 term62 term44 term44 term44). Qed.
Lemma lem7226839 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7226840 : term71 = term72.
Proof. exact (@lem7226839 term13 term13). Qed.
Lemma lem7226841 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7226842 : term74 = term13.
Proof. exact (EQ_MP (@lem7226841) (@lem940073)). Qed.
Lemma lem7226843 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7226844 : term72 = term44.
Proof. exact (MK_COMB (@lem7226843) (@lem7226842)). Qed.
Lemma lem7226845 : term71 = term44.
Proof. exact (TRANS (@lem7226840) (@lem7226844)). Qed.
Lemma lem7226847 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7226848 : term89 = term94.
Proof. exact (@lem7226847 term13 term13). Qed.
Lemma lem7226849 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7226850 : term74 = term13.
Proof. exact (EQ_MP (@lem7226849) (@lem940073)). Qed.
Lemma lem7226851 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7226852 : term72 = term44.
Proof. exact (MK_COMB (@lem7226851) (@lem7226850)). Qed.
Lemma lem7226853 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7226854 : term94 = term62.
Proof. exact (MK_COMB (@lem7226853) (@lem7226852)). Qed.
Lemma lem7226855 : term89 = term62.
Proof. exact (TRANS (@lem7226848) (@lem7226854)). Qed.
Lemma lem7226856 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7226857 : term95 = term96.
Proof. exact (MK_COMB (@lem7226856) (@lem7226855)). Qed.
Lemma lem7226858 : term91 = term63.
Proof. exact (MK_COMB (@lem7226857) (@lem7226845)). Qed.
Lemma lem7226859 : term90 = term63.
Proof. exact (TRANS (@lem7226837) (@lem7226858)). Qed.
Lemma lem7226860 : term89 = term63.
Proof. exact (TRANS (@lem7226836) (@lem7226859)). Qed.
Lemma lem7226862 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7226863 : term63 = term62.
Proof. exact (@lem7226862 term62). Qed.
Lemma lem7226864 : term89 = term62.
Proof. exact (TRANS (@lem7226860) (@lem7226863)). Qed.
Lemma lem7226867 (_96851 : int) : (term97 _96851) = (term97 _96851).
Proof. exact (eq_refl (term97 _96851)). Qed.
Lemma lem7226868 (_96851 : int) : (term87 _96851) = (term98 _96851).
Proof. exact (MK_COMB (@lem7226867 _96851) (@lem7226864)). Qed.
Lemma lem7226869 (_96851 : int) : (term86 _96851) = (term98 _96851).
Proof. exact (TRANS (@lem7226827 _96851) (@lem7226868 _96851)). Qed.
Lemma lem7226870 (_96851 : int) : (term45 _96851) = (term45 _96851).
Proof. exact (eq_refl (term45 _96851)). Qed.
Lemma lem7226871 (_96851 : int) : (term85 _96851) = (term99 _96851).
Proof. exact (MK_COMB (@lem7226870 _96851) (@lem7226869 _96851)). Qed.
Lemma lem7226872 (_96851 : int) : (term99 _96851) = (term100 _96851).
Proof. exact (@lem1982763 (real_of_int _96851) (term101 _96851) term62). Qed.
Lemma lem7226873 (_96851 : int) : (term102 _96851) = (term103 _96851).
Proof. exact (@lem1982715 term62 (real_of_int _96851)). Qed.
Lemma lem7226875 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7226876 : term44 = term88.
Proof. exact (@lem7226875 term13). Qed.
Lemma lem7226878 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7226879 : term62 = term63.
Proof. exact (@lem7226878 term13). Qed.
Lemma lem7226880 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7226881 : term104 = term105.
Proof. exact (MK_COMB (@lem7226880) (@lem7226879)). Qed.
Lemma lem7226882 : term106 = term107.
Proof. exact (MK_COMB (@lem7226881) (@lem7226876)). Qed.
Lemma lem7226883 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7226885 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7226886 : term110 = term111.
Proof. exact (@lem7226885 (NUMERAL 0) term13). Qed.
Lemma lem7226887 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7226888 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7226889 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7226888 h1) (fun h1 : term111 = True => @lem7226887)). Qed.
Lemma lem7226890 : term111 = True.
Proof. exact (EQ_MP (@lem7226889) (@lem7226887)). Qed.
Lemma lem7226891 : term110 = True.
Proof. exact (TRANS (@lem7226886) (@lem7226890)). Qed.
Lemma lem7226892 : True = term110.
Proof. exact (SYM (@lem7226891)). Qed.
Lemma lem7226893 : term110.
Proof. exact (EQ_MP (@lem7226892) (@lem0)). Qed.
Lemma lem7226894 : term113.
Proof. exact (@lem7226883 (@lem7226893)). Qed.
Lemma lem7226896 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7226897 : term110 = term111.
Proof. exact (@lem7226896 (NUMERAL 0) term13). Qed.
Lemma lem7226898 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7226899 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7226900 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7226899 h1) (fun h1 : term111 = True => @lem7226898)). Qed.
Lemma lem7226901 : term111 = True.
Proof. exact (EQ_MP (@lem7226900) (@lem7226898)). Qed.
Lemma lem7226902 : term110 = True.
Proof. exact (TRANS (@lem7226897) (@lem7226901)). Qed.
Lemma lem7226903 : True = term110.
Proof. exact (SYM (@lem7226902)). Qed.
Lemma lem7226904 : term110.
Proof. exact (EQ_MP (@lem7226903) (@lem0)). Qed.
Lemma lem7226905 : term114.
Proof. exact (@lem7226894 (@lem7226904)). Qed.
Lemma lem7226907 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7226908 : term110 = term111.
Proof. exact (@lem7226907 (NUMERAL 0) term13). Qed.
Lemma lem7226909 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7226910 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7226911 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7226910 h1) (fun h1 : term111 = True => @lem7226909)). Qed.
Lemma lem7226912 : term111 = True.
Proof. exact (EQ_MP (@lem7226911) (@lem7226909)). Qed.
Lemma lem7226913 : term110 = True.
Proof. exact (TRANS (@lem7226908) (@lem7226912)). Qed.
Lemma lem7226914 : True = term110.
Proof. exact (SYM (@lem7226913)). Qed.
Lemma lem7226915 : term110.
Proof. exact (EQ_MP (@lem7226914) (@lem0)). Qed.
Lemma lem7226916 : term115.
Proof. exact (@lem7226905 (@lem7226915)). Qed.
Lemma lem7226918 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7226919 : term71 = term72.
Proof. exact (@lem7226918 term13 term13). Qed.
Lemma lem7226920 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7226921 : term74 = term13.
Proof. exact (EQ_MP (@lem7226920) (@lem940073)). Qed.
Lemma lem7226922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7226923 : term72 = term44.
Proof. exact (MK_COMB (@lem7226922) (@lem7226921)). Qed.
Lemma lem7226924 : term71 = term44.
Proof. exact (TRANS (@lem7226919) (@lem7226923)). Qed.
Lemma lem7226926 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7226927 : term89 = term94.
Proof. exact (@lem7226926 term13 term13). Qed.
Lemma lem7226928 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7226929 : term74 = term13.
Proof. exact (EQ_MP (@lem7226928) (@lem940073)). Qed.
Lemma lem7226930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7226931 : term72 = term44.
Proof. exact (MK_COMB (@lem7226930) (@lem7226929)). Qed.
Lemma lem7226932 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7226933 : term94 = term62.
Proof. exact (MK_COMB (@lem7226932) (@lem7226931)). Qed.
Lemma lem7226934 : term89 = term62.
Proof. exact (TRANS (@lem7226927) (@lem7226933)). Qed.
Lemma lem7226935 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7226936 : term116 = term104.
Proof. exact (MK_COMB (@lem7226935) (@lem7226934)). Qed.
Lemma lem7226937 : term117 = term106.
Proof. exact (MK_COMB (@lem7226936) (@lem7226924)). Qed.
Lemma lem7226939 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7226940 : term106 = term29.
Proof. exact (@lem7226939 term13). Qed.
Lemma lem7226941 : term117 = term29.
Proof. exact (TRANS (@lem7226937) (@lem7226940)). Qed.
Lemma lem7226942 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7226943 : term119 = term120.
Proof. exact (MK_COMB (@lem7226942) (@lem7226941)). Qed.
Lemma lem7226944 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7226945 : term121 = term122.
Proof. exact (MK_COMB (@lem7226943) (@lem7226944)). Qed.
Lemma lem7226947 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7226948 : term122 = term29.
Proof. exact (@lem7226947 term13). Qed.
Lemma lem7226949 : term121 = term29.
Proof. exact (TRANS (@lem7226945) (@lem7226948)). Qed.
Lemma lem7226951 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7226952 : term71 = term72.
Proof. exact (@lem7226951 term13 term13). Qed.
Lemma lem7226953 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7226954 : term74 = term13.
Proof. exact (EQ_MP (@lem7226953) (@lem940073)). Qed.
Lemma lem7226955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7226956 : term72 = term44.
Proof. exact (MK_COMB (@lem7226955) (@lem7226954)). Qed.
Lemma lem7226957 : term71 = term44.
Proof. exact (TRANS (@lem7226952) (@lem7226956)). Qed.
Lemma lem7226958 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7226959 : term124 = term122.
Proof. exact (MK_COMB (@lem7226958) (@lem7226957)). Qed.
Lemma lem7226961 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7226962 : term122 = term29.
Proof. exact (@lem7226961 term13). Qed.
Lemma lem7226963 : term124 = term29.
Proof. exact (TRANS (@lem7226959) (@lem7226962)). Qed.
Lemma lem7226964 : term29 = term124.
Proof. exact (SYM (@lem7226963)). Qed.
Lemma lem7226965 : term121 = term124.
Proof. exact (TRANS (@lem7226949) (@lem7226964)). Qed.
Lemma lem7226966 : term107 = term59.
Proof. exact (@lem7226916 (@lem7226965)). Qed.
Lemma lem7226967 : term106 = term59.
Proof. exact (TRANS (@lem7226882) (@lem7226966)). Qed.
Lemma lem7226969 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7226970 : term59 = term29.
Proof. exact (@lem7226969 term29). Qed.
Lemma lem7226971 : term106 = term29.
Proof. exact (TRANS (@lem7226967) (@lem7226970)). Qed.
Lemma lem7226972 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7226973 : term125 = term120.
Proof. exact (MK_COMB (@lem7226972) (@lem7226971)). Qed.
Lemma lem7226974 (_96851 : int) : (real_of_int _96851) = (real_of_int _96851).
Proof. exact (eq_refl (real_of_int _96851)). Qed.
Lemma lem7226975 (_96851 : int) : (term103 _96851) = (term126 _96851).
Proof. exact (MK_COMB (@lem7226973) (@lem7226974 _96851)). Qed.
Lemma lem7226976 (_96851 : int) : (term102 _96851) = (term126 _96851).
Proof. exact (TRANS (@lem7226873 _96851) (@lem7226975 _96851)). Qed.
Lemma lem7226977 (_96851 : int) : (term126 _96851) = term29.
Proof. exact (@lem1982719 (real_of_int _96851)). Qed.
Lemma lem7226978 (_96851 : int) : (term102 _96851) = term29.
Proof. exact (TRANS (@lem7226976 _96851) (@lem7226977 _96851)). Qed.
Lemma lem7226979 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7226980 (_96851 : int) : (term127 _96851) = term128.
Proof. exact (MK_COMB (@lem7226979) (@lem7226978 _96851)). Qed.
Lemma lem7226981 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem7226982 (_96851 : int) : (term100 _96851) = term129.
Proof. exact (MK_COMB (@lem7226980 _96851) (@lem7226981)). Qed.
Lemma lem7226983 (_96851 : int) : (term99 _96851) = term129.
Proof. exact (TRANS (@lem7226872 _96851) (@lem7226982 _96851)). Qed.
Lemma lem7226984 : term129 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem7226985 (_96851 : int) : (term99 _96851) = term62.
Proof. exact (TRANS (@lem7226983 _96851) (@lem7226984)). Qed.
Lemma lem7226986 (_96851 : int) : (term85 _96851) = term62.
Proof. exact (TRANS (@lem7226871 _96851) (@lem7226985 _96851)). Qed.
Lemma lem7226988 (_96851 : int) : (term84 _96851) = term62.
Proof. exact (TRANS (@lem7226826 _96851) (@lem7226986 _96851)). Qed.
Lemma lem7226989 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7226990 (_96851 : int) : (term130 _96851) = term131.
Proof. exact (MK_COMB (@lem7226989) (@lem7226988 _96851)). Qed.
Lemma lem7226991 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7226992 (_96851 : int) : (term83 _96851) = term132.
Proof. exact (MK_COMB (@lem7226990 _96851) (@lem7226991)). Qed.
Lemma lem7226993 (_96851 : int) : (term49 _96851) = term132.
Proof. exact (TRANS (@lem7226814 _96851) (@lem7226992 _96851)). Qed.
Lemma lem7226994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7226995 (_96851 : int) : (term51 _96851) = (term133 _96851).
Proof. exact (MK_COMB (@lem7226994) (@lem7226813 _96851)). Qed.
Lemma lem7226996 (_96851 : int) : (term52 _96851) = (term134 _96851).
Proof. exact (MK_COMB (@lem7226995 _96851) (@lem7226993 _96851)). Qed.
Lemma lem7227011 (_96851 : int) : (term54 _96851) = (term134 _96851).
Proof. exact (TRANS (@lem7226765 _96851) (@lem7226996 _96851)). Qed.
Lemma lem7227015 (_96851 : int) (h1 : term134 _96851) : term134 _96851.
Proof. exact (h1). Qed.
Lemma lem7227016 (_96851 : int) (h1 : term134 _96851) : term132.
Proof. exact (proj2 (@lem7227015 _96851 h1)). Qed.
Lemma lem7227019 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7227020 : term132 = term135.
Proof. exact (@lem7227019 term29 term62). Qed.
Lemma lem7227022 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7227023 : term62 = term63.
Proof. exact (@lem7227022 term13). Qed.
Lemma lem7227025 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7227026 : term29 = term59.
Proof. exact (@lem7227025 (NUMERAL 0)). Qed.
Lemma lem7227027 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7227028 : term31 = term136.
Proof. exact (MK_COMB (@lem7227027) (@lem7227026)). Qed.
Lemma lem7227029 : term135 = term137.
Proof. exact (MK_COMB (@lem7227028) (@lem7227023)). Qed.
Lemma lem7227030 : term138.
Proof. exact (@lem1980026 term29 term44 term62 term44). Qed.
Lemma lem7227032 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7227033 : term110 = term111.
Proof. exact (@lem7227032 (NUMERAL 0) term13). Qed.
Lemma lem7227034 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7227035 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7227036 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7227035 h1) (fun h1 : term111 = True => @lem7227034)). Qed.
Lemma lem7227037 : term111 = True.
Proof. exact (EQ_MP (@lem7227036) (@lem7227034)). Qed.
Lemma lem7227038 : term110 = True.
Proof. exact (TRANS (@lem7227033) (@lem7227037)). Qed.
Lemma lem7227039 : True = term110.
Proof. exact (SYM (@lem7227038)). Qed.
Lemma lem7227040 : term110.
Proof. exact (EQ_MP (@lem7227039) (@lem0)). Qed.
Lemma lem7227041 : term139.
Proof. exact (@lem7227030 (@lem7227040)). Qed.
Lemma lem7227043 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7227044 : term110 = term111.
Proof. exact (@lem7227043 (NUMERAL 0) term13). Qed.
Lemma lem7227045 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7227046 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7227047 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7227046 h1) (fun h1 : term111 = True => @lem7227045)). Qed.
Lemma lem7227048 : term111 = True.
Proof. exact (EQ_MP (@lem7227047) (@lem7227045)). Qed.
Lemma lem7227049 : term110 = True.
Proof. exact (TRANS (@lem7227044) (@lem7227048)). Qed.
Lemma lem7227050 : True = term110.
Proof. exact (SYM (@lem7227049)). Qed.
Lemma lem7227051 : term110.
Proof. exact (EQ_MP (@lem7227050) (@lem0)). Qed.
Lemma lem7227052 : term137 = term140.
Proof. exact (@lem7227041 (@lem7227051)). Qed.
Lemma lem7227054 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7227055 : term89 = term94.
Proof. exact (@lem7227054 term13 term13). Qed.
Lemma lem7227056 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7227057 : term74 = term13.
Proof. exact (EQ_MP (@lem7227056) (@lem940073)). Qed.
Lemma lem7227058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7227059 : term72 = term44.
Proof. exact (MK_COMB (@lem7227058) (@lem7227057)). Qed.
Lemma lem7227060 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7227061 : term94 = term62.
Proof. exact (MK_COMB (@lem7227060) (@lem7227059)). Qed.
Lemma lem7227062 : term89 = term62.
Proof. exact (TRANS (@lem7227055) (@lem7227061)). Qed.
Lemma lem7227064 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7227065 : term122 = term29.
Proof. exact (@lem7227064 term13). Qed.
Lemma lem7227066 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7227067 : term141 = term31.
Proof. exact (MK_COMB (@lem7227066) (@lem7227065)). Qed.
Lemma lem7227068 : term140 = term135.
Proof. exact (MK_COMB (@lem7227067) (@lem7227062)). Qed.
Lemma lem7227070 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7227071 : term135 = term144.
Proof. exact (@lem7227070 (NUMERAL 0) term13). Qed.
Lemma lem7227072 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7227073 (h1 : term112 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7227074 : (term112 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7227073 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem7227072)). Qed.
Lemma lem7227075 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7227074) (@lem7227072)). Qed.
Lemma lem7227076 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7227077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7227078 : term145 = (and True).
Proof. exact (MK_COMB (@lem7227077) (@lem7227076)). Qed.
Lemma lem7227079 : term144 = (True /\ False).
Proof. exact (MK_COMB (@lem7227078) (@lem7227075)). Qed.
Lemma lem7227081 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7227082 : term144 = False.
Proof. exact (TRANS (@lem7227079) (@lem7227081)). Qed.
Lemma lem7227083 : term135 = False.
Proof. exact (TRANS (@lem7227071) (@lem7227082)). Qed.
Lemma lem7227084 : term140 = False.
Proof. exact (TRANS (@lem7227068) (@lem7227083)). Qed.
Lemma lem7227085 : term137 = False.
Proof. exact (TRANS (@lem7227052) (@lem7227084)). Qed.
Lemma lem7227086 : term135 = False.
Proof. exact (TRANS (@lem7227029) (@lem7227085)). Qed.
Lemma lem7227087 : term132 = False.
Proof. exact (TRANS (@lem7227020) (@lem7227086)). Qed.
Lemma lem7227088 (_96851 : int) (h1 : term134 _96851) : False.
Proof. exact (EQ_MP (@lem7227087) (@lem7227016 _96851 h1)). Qed.
Lemma lem7227090 (_96851 : int) (h1 : term134 _96851) : term134 _96851.
Proof. exact (h1). Qed.
Lemma lem7227091 (_96851 : int) (h1 : term134 _96851) : (term134 _96851) = False.
Proof. exact (prop_ext (fun h2 : term134 _96851 => @lem7227088 _96851 h1) (fun h2 : False => @lem7227090 _96851 h1)). Qed.
Lemma lem7227092 (_96851 : int) (h1 : term134 _96851) : False.
Proof. exact (EQ_MP (@lem7227091 _96851 h1) (@lem7227090 _96851 h1)). Qed.
Lemma lem7227093 (_96851 : int) (h1 : term54 _96851) : term54 _96851.
Proof. exact (h1). Qed.
Lemma lem7227094 (_96851 : int) (h1 : term54 _96851) : term134 _96851.
Proof. exact (EQ_MP (@lem7227011 _96851) (@lem7227093 _96851 h1)). Qed.
Lemma lem7227095 (_96851 : int) (h1 : term54 _96851) : (term134 _96851) = False.
Proof. exact (prop_ext (fun h2 : term134 _96851 => @lem7227092 _96851 h2) (fun h2 : False => @lem7227094 _96851 h1)). Qed.
Lemma lem7227096 (_96851 : int) (h1 : term54 _96851) : False.
Proof. exact (EQ_MP (@lem7227095 _96851 h1) (@lem7227094 _96851 h1)). Qed.
Lemma lem7227097 (_96851 : int) : term146 _96851.
Proof. exact (fun h0 : term54 _96851 => @lem7227096 _96851 h0). Qed.
Lemma lem7227098 (_96851 : int) : term147 _96851.
Proof. exact (@lem1386578 (term148 _96851)). Qed.
Lemma lem7227101 (_96851 : int) : term148 _96851.
Proof. exact (@lem7227098 _96851 (@lem7227097 _96851)). Qed.
Lemma lem7227102 (_96851 : int) : (term52 _96851) = (term20 _96851).
Proof. exact (SYM (@lem7226745 _96851)). Qed.
Lemma lem7227103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7227104 (_96851 : int) : (term148 _96851) = (term18 _96851).
Proof. exact (MK_COMB (@lem7227103) (@lem7227102 _96851)). Qed.
Lemma lem7227105 (_96851 : int) : term18 _96851.
Proof. exact (EQ_MP (@lem7227104 _96851) (@lem7227101 _96851)). Qed.
Lemma lem7227106 (_96851 : int) : term19 _96851.
Proof. exact (EQ_MP (@lem7226684 _96851) (@lem7227105 _96851)). Qed.
Lemma lem7227107 (n : nat) : term149 n.
Proof. exact (@lem7227106 (int_of_num n)). Qed.
Lemma lem7227108 (n : nat) : term15 n.
Proof. exact (@lem7227107 n (@lem7226683 n)). Qed.
Lemma lem7227109 (n : nat) : (term15 n) = (term5 n).
Proof. exact (SYM (@lem7226680 n)). Qed.
Lemma lem7227110 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem7227109 n) (@lem7227108 n)). Qed.
Lemma lem7227113 (n : nat) (m : nat) (h1 : (term150 m n) = (Peano.le n m)) : (term150 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem7227114 (n : nat) (m : nat) (h1 : (term150 m n) = (Peano.le n m)) : (Peano.le n m) = (term150 m n).
Proof. exact (SYM (@lem7227113 n m h1)). Qed.
Lemma lem7227115 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term150 m n)) : (Peano.le n m) = (term150 m n).
Proof. exact (h1). Qed.
Lemma lem7227116 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term150 m n)) : (term150 m n) = (Peano.le n m).
Proof. exact (SYM (@lem7227115 m n h1)). Qed.
Lemma lem7227117 (m : nat) (n : nat) : ((term150 m n) = (Peano.le n m)) = ((Peano.le n m) = (term150 m n)).
Proof. exact (prop_ext (fun h1 : (term150 m n) = (Peano.le n m) => @lem7227114 n m h1) (fun h1 : (Peano.le n m) = (term150 m n) => @lem7227116 m n h1)). Qed.
Lemma lem7227118 (m : nat) : (term151 m) = (term152 m).
Proof. exact (fun_ext (fun n : nat => @lem7227117 m n)). Qed.
Lemma lem7227119 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7227120 (m : nat) : (term153 m) = (term154 m).
Proof. exact (MK_COMB (@lem7227119) (@lem7227118 m)). Qed.
Lemma lem7227121 : term155 = term156.
Proof. exact (fun_ext (fun m : nat => @lem7227120 m)). Qed.
Lemma lem7227122 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7227123 : term157 = term158.
Proof. exact (MK_COMB (@lem7227122) (@lem7227121)). Qed.
Lemma lem7227124 : term158.
Proof. exact (EQ_MP (@lem7227123) (@lem98377)). Qed.
Lemma lem7227125 : term159.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem7227126 (m : nat) : term160 m.
Proof. exact (@lem7227125 m). Qed.
Lemma lem7227127 (m : nat) : (term160 m) = (term161 m).
Proof. exact (eq_refl (term160 m)). Qed.
Lemma lem7227128 (m : nat) : term161 m.
Proof. exact (EQ_MP (@lem7227127 m) (@lem7227126 m)). Qed.
Lemma lem7227129 (m : nat) (n : nat) : term162 m n.
Proof. exact (@lem7227128 m n). Qed.
Lemma lem7227130 (m : nat) (n : nat) : (term162 m n) = ((term163 m n) = (term164 m n)).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem7227138 (n : nat) (m : nat) (h1 : (term165 m n) = (Peano.lt n m)) : (term165 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem7227139 (n : nat) (m : nat) (h1 : (term165 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term165 m n).
Proof. exact (SYM (@lem7227138 n m h1)). Qed.
Lemma lem7227140 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term165 m n)) : (Peano.lt n m) = (term165 m n).
Proof. exact (h1). Qed.
Lemma lem7227141 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term165 m n)) : (term165 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem7227140 m n h1)). Qed.
Lemma lem7227142 (m : nat) (n : nat) : ((term165 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term165 m n)).
Proof. exact (prop_ext (fun h1 : (term165 m n) = (Peano.lt n m) => @lem7227139 n m h1) (fun h1 : (Peano.lt n m) = (term165 m n) => @lem7227141 m n h1)). Qed.
Lemma lem7227143 (m : nat) : (term166 m) = (term167 m).
Proof. exact (fun_ext (fun n : nat => @lem7227142 m n)). Qed.
Lemma lem7227144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7227145 (m : nat) : (term168 m) = (term169 m).
Proof. exact (MK_COMB (@lem7227144) (@lem7227143 m)). Qed.
Lemma lem7227146 : term170 = term171.
Proof. exact (fun_ext (fun m : nat => @lem7227145 m)). Qed.
Lemma lem7227147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7227148 : term172 = term173.
Proof. exact (MK_COMB (@lem7227147) (@lem7227146)). Qed.
Lemma lem7227149 : term173.
Proof. exact (EQ_MP (@lem7227148) (@lem97961)). Qed.
Lemma lem7227151 (P : nat -> Prop) : term174 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem7227152 (m : nat) (g : nat -> real) (f : nat -> real) : term175 m g f.
Proof. exact (@lem7227151 (term176 m g f)). Qed.
Lemma lem7227153 (m : nat) (g : nat -> real) (f : nat -> real) : (term177 m g f) = ((term178 m f g) = (term179 m g f)).
Proof. exact (eq_refl (term177 m g f)). Qed.
Lemma lem7227154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7227155 (m : nat) (g : nat -> real) (f : nat -> real) : (term180 m g f) = (term181 m g f).
Proof. exact (MK_COMB (@lem7227154) (@lem7227153 m g f)). Qed.
Lemma lem7227156 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term182 m g f n) = ((term183 m n f g) = (term184 m n g f)).
Proof. exact (eq_refl (term182 m g f n)). Qed.
Lemma lem7227157 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7227158 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term185 m g f n) = (term186 m n g f).
Proof. exact (MK_COMB (@lem7227157) (@lem7227156 m n g f)). Qed.
Lemma lem7227159 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term187 m g f n) = ((term188 m n f g) = (term189 m n g f)).
Proof. exact (eq_refl (term187 m g f n)). Qed.
Lemma lem7227160 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term190 m g f n) = (term191 m n g f).
Proof. exact (MK_COMB (@lem7227158 m n g f) (@lem7227159 m n g f)). Qed.
Lemma lem7227161 (m : nat) (g : nat -> real) (f : nat -> real) : (term192 m g f) = (term193 m g f).
Proof. exact (fun_ext (fun n : nat => @lem7227160 m n g f)). Qed.
Lemma lem7227162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7227163 (m : nat) (g : nat -> real) (f : nat -> real) : (term194 m g f) = (term195 m g f).
Proof. exact (MK_COMB (@lem7227162) (@lem7227161 m g f)). Qed.
Lemma lem7227164 (m : nat) (g : nat -> real) (f : nat -> real) : (term196 m g f) = (term197 m g f).
Proof. exact (MK_COMB (@lem7227155 m g f) (@lem7227163 m g f)). Qed.
Lemma lem7227165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7227166 (m : nat) (g : nat -> real) (f : nat -> real) : (term198 m g f) = (term199 m g f).
Proof. exact (MK_COMB (@lem7227165) (@lem7227164 m g f)). Qed.
Lemma lem7227167 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term182 m g f n) = ((term183 m n f g) = (term184 m n g f)).
Proof. exact (eq_refl (term182 m g f n)). Qed.
Lemma lem7227168 (m : nat) (g : nat -> real) (f : nat -> real) : (term200 m g f) = (term176 m g f).
Proof. exact (fun_ext (fun n : nat => @lem7227167 m n g f)). Qed.
Lemma lem7227169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7227170 (m : nat) (g : nat -> real) (f : nat -> real) : (term201 m g f) = (term202 m g f).
Proof. exact (MK_COMB (@lem7227169) (@lem7227168 m g f)). Qed.
Lemma lem7227171 (m : nat) (g : nat -> real) (f : nat -> real) : (term175 m g f) = (term203 m g f).
Proof. exact (MK_COMB (@lem7227166 m g f) (@lem7227170 m g f)). Qed.
Lemma lem7227172 (m : nat) (g : nat -> real) (f : nat -> real) : term203 m g f.
Proof. exact (EQ_MP (@lem7227171 m g f) (@lem7227152 m g f)). Qed.
Lemma lem7227174 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term204 _476 _475 _474 _477) = (term205 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem7227175 (_474 : real) (_475 : Prop) (m : nat) (f : nat -> real) (g : nat -> real) (_477 : real) : (term206 m f g _475 _474 _477) = (term207 _474 _475 m f g _477).
Proof. exact (@lem7227174 _474 _475 (term208 m f g) _477). Qed.
Lemma lem7227176 (m : nat) (f : nat -> real) (g : nat -> real) : (term209 m g f) = (term210 m f g).
Proof. exact (@lem7227175 (term211 m g f) (term212 m) m f g term29). Qed.
Lemma lem7227177 (m : nat) (f : nat -> real) (g : nat -> real) : (term213 m f g) = ((term178 m f g) = term29).
Proof. exact (eq_refl (term213 m f g)). Qed.
Lemma lem7227178 (m : nat) : (term214 m) = (term214 m).
Proof. exact (eq_refl (term214 m)). Qed.
Lemma lem7227179 (m : nat) (f : nat -> real) (g : nat -> real) : (term215 m f g) = (term216 m f g).
Proof. exact (MK_COMB (@lem7227178 m) (@lem7227177 m f g)). Qed.
Lemma lem7227180 (m : nat) (g : nat -> real) (f : nat -> real) : (term217 m g f) = ((term178 m f g) = (term211 m g f)).
Proof. exact (eq_refl (term217 m g f)). Qed.
Lemma lem7227181 (m : nat) : (term218 m) = (term218 m).
Proof. exact (eq_refl (term218 m)). Qed.
Lemma lem7227182 (m : nat) (g : nat -> real) (f : nat -> real) : (term219 m g f) = (term220 m g f).
Proof. exact (MK_COMB (@lem7227181 m) (@lem7227180 m g f)). Qed.
Lemma lem7227183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7227184 (m : nat) (g : nat -> real) (f : nat -> real) : (term221 m g f) = (term222 m g f).
Proof. exact (MK_COMB (@lem7227183) (@lem7227182 m g f)). Qed.
Lemma lem7227185 (m : nat) (f : nat -> real) (g : nat -> real) : (term210 m f g) = (term223 m f g).
Proof. exact (MK_COMB (@lem7227184 m g f) (@lem7227179 m f g)). Qed.
Lemma lem7227186 (m : nat) (g : nat -> real) (f : nat -> real) : (term209 m g f) = ((term178 m f g) = (term179 m g f)).
Proof. exact (eq_refl (term209 m g f)). Qed.
Lemma lem7227187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7227188 (m : nat) (g : nat -> real) (f : nat -> real) : (term224 m g f) = (term225 m g f).
Proof. exact (MK_COMB (@lem7227187) (@lem7227186 m g f)). Qed.
Lemma lem7227189 (m : nat) (f : nat -> real) (g : nat -> real) : ((term209 m g f) = (term210 m f g)) = (((term178 m f g) = (term179 m g f)) = (term223 m f g)).
Proof. exact (MK_COMB (@lem7227188 m g f) (@lem7227185 m f g)). Qed.
Lemma lem7227190 (m : nat) (f : nat -> real) (g : nat -> real) : ((term178 m f g) = (term179 m g f)) = (term223 m f g).
Proof. exact (EQ_MP (@lem7227189 m f g) (@lem7227176 m f g)). Qed.
Lemma lem7227191 (m : nat) (g : nat -> real) (f : nat -> real) : (term223 m f g) = ((term178 m f g) = (term179 m g f)).
Proof. exact (SYM (@lem7227190 m f g)). Qed.
Lemma lem7227192 (m : nat) (h1 : term212 m) : term212 m.
Proof. exact (h1). Qed.
Lemma lem7227209 (m : nat) (h1 : term226 m) : term226 m.
Proof. exact (h1). Qed.
Lemma lem7227226 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term204 _476 _475 _474 _477) = (term205 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem7227227 (_474 : real) (_475 : Prop) (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (_477 : real) : (term227 m n f g _475 _474 _477) = (term228 _474 _475 m n f g _477).
Proof. exact (@lem7227226 _474 _475 (term229 m n f g) _477). Qed.
Lemma lem7227228 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term230 m n g f) = (term231 m n f g).
Proof. exact (@lem7227227 (term232 m n g f) (term163 m n) m n f g term29). Qed.
Lemma lem7227229 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term233 m n f g) = ((term188 m n f g) = term29).
Proof. exact (eq_refl (term233 m n f g)). Qed.
Lemma lem7227230 (m : nat) (n : nat) : (term234 m n) = (term234 m n).
Proof. exact (eq_refl (term234 m n)). Qed.
Lemma lem7227231 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term235 m n f g) = (term236 m n f g).
Proof. exact (MK_COMB (@lem7227230 m n) (@lem7227229 m n f g)). Qed.
Lemma lem7227232 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term237 m n g f) = ((term188 m n f g) = (term232 m n g f)).
Proof. exact (eq_refl (term237 m n g f)). Qed.
Lemma lem7227233 (m : nat) (n : nat) : (term238 m n) = (term238 m n).
Proof. exact (eq_refl (term238 m n)). Qed.
Lemma lem7227234 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term239 m n g f) = (term240 m n g f).
Proof. exact (MK_COMB (@lem7227233 m n) (@lem7227232 m n g f)). Qed.
Lemma lem7227235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7227236 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term241 m n g f) = (term242 m n g f).
Proof. exact (MK_COMB (@lem7227235) (@lem7227234 m n g f)). Qed.
Lemma lem7227237 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term231 m n f g) = (term243 m n f g).
Proof. exact (MK_COMB (@lem7227236 m n g f) (@lem7227231 m n f g)). Qed.
Lemma lem7227238 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term230 m n g f) = ((term188 m n f g) = (term189 m n g f)).
Proof. exact (eq_refl (term230 m n g f)). Qed.
Lemma lem7227239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7227240 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term244 m n g f) = (term245 m n g f).
Proof. exact (MK_COMB (@lem7227239) (@lem7227238 m n g f)). Qed.
Lemma lem7227241 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : ((term230 m n g f) = (term231 m n f g)) = (((term188 m n f g) = (term189 m n g f)) = (term243 m n f g)).
Proof. exact (MK_COMB (@lem7227240 m n g f) (@lem7227237 m n f g)). Qed.
Lemma lem7227242 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : ((term188 m n f g) = (term189 m n g f)) = (term243 m n f g).
Proof. exact (EQ_MP (@lem7227241 m n f g) (@lem7227228 m n f g)). Qed.
Lemma lem7227243 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term243 m n f g) = ((term188 m n f g) = (term189 m n g f)).
Proof. exact (SYM (@lem7227242 m n f g)). Qed.
Lemma lem7227244 (m : nat) (n : nat) (h1 : term163 m n) : term163 m n.
Proof. exact (h1). Qed.
Lemma lem7227261 (m : nat) (n : nat) (h1 : term246 m n) : term246 m n.
Proof. exact (h1). Qed.
Lemma lem7227336 (m : nat) : term247 m.
Proof. exact (@lem7227149 m). Qed.
Lemma lem7227337 (m : nat) : (term247 m) = (term169 m).
Proof. exact (eq_refl (term247 m)). Qed.
Lemma lem7227338 (m : nat) : term169 m.
Proof. exact (EQ_MP (@lem7227337 m) (@lem7227336 m)). Qed.
Lemma lem7227339 (m : nat) (n : nat) : term248 m n.
Proof. exact (@lem7227338 m n). Qed.
Lemma lem7227340 (m : nat) (n : nat) : (term248 m n) = ((Peano.lt n m) = (term165 m n)).
Proof. exact (eq_refl (term248 m n)). Qed.
Lemma lem7227342 (f : nat -> real) : term249 f.
Proof. exact (@lem7216202 f). Qed.
Lemma lem7227343 (f : nat -> real) : (term249 f) = (term250 f).
Proof. exact (eq_refl (term249 f)). Qed.
Lemma lem7227344 (f : nat -> real) : term250 f.
Proof. exact (EQ_MP (@lem7227343 f) (@lem7227342 f)). Qed.
Lemma lem7227345 (f : nat -> real) (m : nat) : term251 f m.
Proof. exact (@lem7227344 f m). Qed.
Lemma lem7227346 (m : nat) (f : nat -> real) : (term251 f m) = (term252 m f).
Proof. exact (eq_refl (term251 f m)). Qed.
Lemma lem7227347 (m : nat) (f : nat -> real) : term252 m f.
Proof. exact (EQ_MP (@lem7227346 m f) (@lem7227345 f m)). Qed.
Lemma lem7227348 (m : nat) (f : nat -> real) (n : nat) : term253 m f n.
Proof. exact (@lem7227347 m f n). Qed.
Lemma lem7227349 (m : nat) (n : nat) (f : nat -> real) : (term253 m f n) = (term254 m n f).
Proof. exact (eq_refl (term253 m f n)). Qed.
Lemma lem7227350 (m : nat) (n : nat) (f : nat -> real) : term254 m n f.
Proof. exact (EQ_MP (@lem7227349 m n f) (@lem7227348 m f n)). Qed.
Lemma lem7227351 (n : nat) (m : nat) (h1 : Peano.lt n m) : Peano.lt n m.
Proof. exact (h1). Qed.
Lemma lem7227352 (f : nat -> real) (n : nat) (m : nat) (h1 : Peano.lt n m) : (term255 m n f) = term29.
Proof. exact (@lem7227350 m n f (@lem7227351 n m h1)). Qed.
Lemma lem7227358 (m : nat) : term256 m.
Proof. exact (@lem82 (term212 m)). Qed.
Lemma lem7227363 (m : nat) (n : nat) (f : nat -> real) : term254 m n f.
Proof. exact (fun h0 : Peano.lt n m => @lem7227352 f n m h0). Qed.
Lemma lem7227364 (m : nat) (f : nat -> real) (g : nat -> real) : term257 m f g.
Proof. exact (@lem7227363 m (NUMERAL 0) (term258 f g)). Qed.
Lemma lem7227366 (m : nat) (n : nat) : (Peano.lt n m) = (term165 m n).
Proof. exact (EQ_MP (@lem7227340 m n) (@lem7227339 m n)). Qed.
Lemma lem7227367 (m : nat) : (term259 m) = (term226 m).
Proof. exact (@lem7227366 m (NUMERAL 0)). Qed.
Lemma lem7227369 (m : nat) (h1 : term226 m) : (term212 m) = False.
Proof. exact (@lem7227358 m (@lem7227209 m h1)). Qed.
Lemma lem7227370 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7227371 (m : nat) (h1 : term226 m) : (term226 m) = (~ False).
Proof. exact (MK_COMB (@lem7227370) (@lem7227369 m h1)). Qed.
Lemma lem7227373 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7227374 (m : nat) (h1 : term226 m) : (term226 m) = True.
Proof. exact (TRANS (@lem7227371 m h1) (@lem7227373)). Qed.
Lemma lem7227375 (m : nat) (h1 : term226 m) : (term259 m) = True.
Proof. exact (TRANS (@lem7227367 m) (@lem7227374 m h1)). Qed.
Lemma lem7227376 (m : nat) (h1 : term226 m) : True = (term259 m).
Proof. exact (SYM (@lem7227375 m h1)). Qed.
Lemma lem7227377 (m : nat) (h1 : term226 m) : term259 m.
Proof. exact (EQ_MP (@lem7227376 m h1) (@lem0)). Qed.
Lemma lem7227378 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term226 m) : (term178 m f g) = term29.
Proof. exact (@lem7227364 m f g (@lem7227377 m h1)). Qed.
Lemma lem7227379 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7227380 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term226 m) : (term260 m f g) = term261.
Proof. exact (MK_COMB (@lem7227379) (@lem7227378 f g m h1)). Qed.
Lemma lem7227381 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7227382 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term226 m) : ((term178 m f g) = term29) = (term29 = term29).
Proof. exact (MK_COMB (@lem7227380 f g m h1) (@lem7227381)). Qed.
Lemma lem7227384 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7227385 (x : real) : (x = x) = True.
Proof. exact (@lem7227384 real x). Qed.
Lemma lem7227386 : (term29 = term29) = True.
Proof. exact (@lem7227385 term29). Qed.
Lemma lem7227387 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term226 m) : ((term178 m f g) = term29) = True.
Proof. exact (TRANS (@lem7227382 f g m h1) (@lem7227386)). Qed.
Lemma lem7227388 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term226 m) : True = ((term178 m f g) = term29).
Proof. exact (SYM (@lem7227387 f g m h1)). Qed.
Lemma lem7227448 (m : nat) : term247 m.
Proof. exact (@lem7227149 m). Qed.
Lemma lem7227449 (m : nat) : (term247 m) = (term169 m).
Proof. exact (eq_refl (term247 m)). Qed.
Lemma lem7227450 (m : nat) : term169 m.
Proof. exact (EQ_MP (@lem7227449 m) (@lem7227448 m)). Qed.
Lemma lem7227451 (m : nat) (n : nat) : term248 m n.
Proof. exact (@lem7227450 m n). Qed.
Lemma lem7227452 (m : nat) (n : nat) : (term248 m n) = ((Peano.lt n m) = (term165 m n)).
Proof. exact (eq_refl (term248 m n)). Qed.
Lemma lem7227454 (f : nat -> real) : term249 f.
Proof. exact (@lem7216202 f). Qed.
Lemma lem7227455 (f : nat -> real) : (term249 f) = (term250 f).
Proof. exact (eq_refl (term249 f)). Qed.
Lemma lem7227456 (f : nat -> real) : term250 f.
Proof. exact (EQ_MP (@lem7227455 f) (@lem7227454 f)). Qed.
Lemma lem7227457 (f : nat -> real) (m : nat) : term251 f m.
Proof. exact (@lem7227456 f m). Qed.
Lemma lem7227458 (m : nat) (f : nat -> real) : (term251 f m) = (term252 m f).
Proof. exact (eq_refl (term251 f m)). Qed.
Lemma lem7227459 (m : nat) (f : nat -> real) : term252 m f.
Proof. exact (EQ_MP (@lem7227458 m f) (@lem7227457 f m)). Qed.
Lemma lem7227460 (m : nat) (f : nat -> real) (n : nat) : term253 m f n.
Proof. exact (@lem7227459 m f n). Qed.
Lemma lem7227461 (m : nat) (n : nat) (f : nat -> real) : (term253 m f n) = (term254 m n f).
Proof. exact (eq_refl (term253 m f n)). Qed.
Lemma lem7227462 (m : nat) (n : nat) (f : nat -> real) : term254 m n f.
Proof. exact (EQ_MP (@lem7227461 m n f) (@lem7227460 m f n)). Qed.
Lemma lem7227463 (n : nat) (m : nat) (h1 : Peano.lt n m) : Peano.lt n m.
Proof. exact (h1). Qed.
Lemma lem7227464 (f : nat -> real) (n : nat) (m : nat) (h1 : Peano.lt n m) : (term255 m n f) = term29.
Proof. exact (@lem7227462 m n f (@lem7227463 n m h1)). Qed.
Lemma lem7227470 (m : nat) (n : nat) : term262 m n.
Proof. exact (@lem82 (term163 m n)). Qed.
Lemma lem7227475 (m : nat) (n : nat) (f : nat -> real) : term254 m n f.
Proof. exact (fun h0 : Peano.lt n m => @lem7227464 f n m h0). Qed.
Lemma lem7227476 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : term263 m n f g.
Proof. exact (@lem7227475 m (S n) (term258 f g)). Qed.
Lemma lem7227478 (m : nat) (n : nat) : (Peano.lt n m) = (term165 m n).
Proof. exact (EQ_MP (@lem7227452 m n) (@lem7227451 m n)). Qed.
Lemma lem7227479 (m : nat) (n : nat) : (term264 n m) = (term246 m n).
Proof. exact (@lem7227478 m (S n)). Qed.
Lemma lem7227481 (m : nat) (n : nat) (h1 : term246 m n) : (term163 m n) = False.
Proof. exact (@lem7227470 m n (@lem7227261 m n h1)). Qed.
Lemma lem7227482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7227483 (m : nat) (n : nat) (h1 : term246 m n) : (term246 m n) = (~ False).
Proof. exact (MK_COMB (@lem7227482) (@lem7227481 m n h1)). Qed.
Lemma lem7227485 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7227486 (m : nat) (n : nat) (h1 : term246 m n) : (term246 m n) = True.
Proof. exact (TRANS (@lem7227483 m n h1) (@lem7227485)). Qed.
Lemma lem7227487 (m : nat) (n : nat) (h1 : term246 m n) : (term264 n m) = True.
Proof. exact (TRANS (@lem7227479 m n) (@lem7227486 m n h1)). Qed.
Lemma lem7227488 (m : nat) (n : nat) (h1 : term246 m n) : True = (term264 n m).
Proof. exact (SYM (@lem7227487 m n h1)). Qed.
Lemma lem7227489 (m : nat) (n : nat) (h1 : term246 m n) : term264 n m.
Proof. exact (EQ_MP (@lem7227488 m n h1) (@lem0)). Qed.
Lemma lem7227490 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term246 m n) : (term188 m n f g) = term29.
Proof. exact (@lem7227476 m n f g (@lem7227489 m n h1)). Qed.
Lemma lem7227491 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7227492 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term246 m n) : (term265 m n f g) = term261.
Proof. exact (MK_COMB (@lem7227491) (@lem7227490 f g m n h1)). Qed.
Lemma lem7227493 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7227494 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term246 m n) : ((term188 m n f g) = term29) = (term29 = term29).
Proof. exact (MK_COMB (@lem7227492 f g m n h1) (@lem7227493)). Qed.
Lemma lem7227496 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7227497 (x : real) : (x = x) = True.
Proof. exact (@lem7227496 real x). Qed.
Lemma lem7227498 : (term29 = term29) = True.
Proof. exact (@lem7227497 term29). Qed.
Lemma lem7227499 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term246 m n) : ((term188 m n f g) = term29) = True.
Proof. exact (TRANS (@lem7227494 f g m n h1) (@lem7227498)). Qed.
Lemma lem7227500 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term246 m n) : True = ((term188 m n f g) = term29).
Proof. exact (SYM (@lem7227499 f g m n h1)). Qed.
Lemma lem7227509 (f : nat -> real) : term266 f.
Proof. exact (proj1 (@lem7221724 f)). Qed.
Lemma lem7227510 (f : nat -> real) (m : nat) : term267 f m.
Proof. exact (@lem7227509 f m). Qed.
Lemma lem7227511 (m : nat) (f : nat -> real) : (term267 f m) = ((term268 m f) = (term269 m f)).
Proof. exact (eq_refl (term267 f m)). Qed.
Lemma lem7227518 (m : nat) (f : nat -> real) : (term268 m f) = (term269 m f).
Proof. exact (EQ_MP (@lem7227511 m f) (@lem7227510 f m)). Qed.
Lemma lem7227519 (m : nat) (f : nat -> real) (g : nat -> real) : (term178 m f g) = (term270 m f g).
Proof. exact (@lem7227518 m (term258 f g)). Qed.
Lemma lem7227525 {A B : Type'} (f : A -> B) (y : A) : (term271 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7227526 (f : nat -> real) (y : nat) : (term272 f y) = (f y).
Proof. exact (@lem7227525 nat real f y). Qed.
Lemma lem7227527 (f : nat -> real) (g : nat -> real) : (term273 f g) = (term274 f g).
Proof. exact (@lem7227526 (term258 f g) (NUMERAL 0)). Qed.
Lemma lem7227528 (f : nat -> real) (g : nat -> real) (k : nat) : (term275 f g k) = (term276 f g k).
Proof. exact (eq_refl (term275 f g k)). Qed.
Lemma lem7227529 (f : nat -> real) (g : nat -> real) : (term277 f g) = (term258 f g).
Proof. exact (fun_ext (fun k : nat => @lem7227528 f g k)). Qed.
Lemma lem7227530 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7227531 (f : nat -> real) (g : nat -> real) : (term273 f g) = (term274 f g).
Proof. exact (MK_COMB (@lem7227529 f g) (@lem7227530)). Qed.
Lemma lem7227532 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7227533 (f : nat -> real) (g : nat -> real) : (term278 f g) = (term279 f g).
Proof. exact (MK_COMB (@lem7227532) (@lem7227531 f g)). Qed.
Lemma lem7227534 (f : nat -> real) (g : nat -> real) : (term274 f g) = (term280 f g).
Proof. exact (eq_refl (term274 f g)). Qed.
Lemma lem7227535 (f : nat -> real) (g : nat -> real) : ((term273 f g) = (term274 f g)) = ((term274 f g) = (term280 f g)).
Proof. exact (MK_COMB (@lem7227533 f g) (@lem7227534 f g)). Qed.
Lemma lem7227536 (f : nat -> real) (g : nat -> real) : (term274 f g) = (term280 f g).
Proof. exact (EQ_MP (@lem7227535 f g) (@lem7227527 f g)). Qed.
Lemma lem7227537 (m : nat) : (term281 m) = (term281 m).
Proof. exact (eq_refl (term281 m)). Qed.
Lemma lem7227538 (m : nat) (f : nat -> real) (g : nat -> real) : (term282 m f g) = (term283 m f g).
Proof. exact (MK_COMB (@lem7227537 m) (@lem7227536 f g)). Qed.
Lemma lem7227539 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7227540 (m : nat) (f : nat -> real) (g : nat -> real) : (term270 m f g) = (term284 m f g).
Proof. exact (MK_COMB (@lem7227538 m f g) (@lem7227539)). Qed.
Lemma lem7227543 (m : nat) (f : nat -> real) (g : nat -> real) : (term178 m f g) = (term284 m f g).
Proof. exact (TRANS (@lem7227519 m f g) (@lem7227540 m f g)). Qed.
Lemma lem7227544 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7227545 (m : nat) (f : nat -> real) (g : nat -> real) : (term260 m f g) = (term285 m f g).
Proof. exact (MK_COMB (@lem7227544) (@lem7227543 m f g)). Qed.
Lemma lem7227547 (m : nat) (f : nat -> real) : (term268 m f) = (term269 m f).
Proof. exact (EQ_MP (@lem7227511 m f) (@lem7227510 f m)). Qed.
Lemma lem7227548 (m : nat) (g : nat -> real) (f : nat -> real) : (term286 m g f) = (term287 m g f).
Proof. exact (@lem7227547 m (term288 g f)). Qed.
Lemma lem7227554 {A B : Type'} (f : A -> B) (y : A) : (term271 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7227555 (f : nat -> real) (y : nat) : (term272 f y) = (f y).
Proof. exact (@lem7227554 nat real f y). Qed.
Lemma lem7227556 (g : nat -> real) (f : nat -> real) : (term289 g f) = (term290 g f).
Proof. exact (@lem7227555 (term288 g f) (NUMERAL 0)). Qed.
Lemma lem7227557 (g : nat -> real) (f : nat -> real) (k : nat) : (term291 g f k) = (term292 g f k).
Proof. exact (eq_refl (term291 g f k)). Qed.
Lemma lem7227558 (g : nat -> real) (f : nat -> real) : (term293 g f) = (term288 g f).
Proof. exact (fun_ext (fun k : nat => @lem7227557 g f k)). Qed.
Lemma lem7227559 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7227560 (g : nat -> real) (f : nat -> real) : (term289 g f) = (term290 g f).
Proof. exact (MK_COMB (@lem7227558 g f) (@lem7227559)). Qed.
Lemma lem7227561 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7227562 (g : nat -> real) (f : nat -> real) : (term294 g f) = (term295 g f).
Proof. exact (MK_COMB (@lem7227561) (@lem7227560 g f)). Qed.
Lemma lem7227563 (g : nat -> real) (f : nat -> real) : (term290 g f) = (term296 g f).
Proof. exact (eq_refl (term290 g f)). Qed.
Lemma lem7227564 (g : nat -> real) (f : nat -> real) : ((term289 g f) = (term290 g f)) = ((term290 g f) = (term296 g f)).
Proof. exact (MK_COMB (@lem7227562 g f) (@lem7227563 g f)). Qed.
Lemma lem7227565 (g : nat -> real) (f : nat -> real) : (term290 g f) = (term296 g f).
Proof. exact (EQ_MP (@lem7227564 g f) (@lem7227556 g f)). Qed.
Lemma lem7227566 (m : nat) : (term281 m) = (term281 m).
Proof. exact (eq_refl (term281 m)). Qed.
Lemma lem7227567 (m : nat) (g : nat -> real) (f : nat -> real) : (term297 m g f) = (term298 m g f).
Proof. exact (MK_COMB (@lem7227566 m) (@lem7227565 g f)). Qed.
Lemma lem7227568 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7227569 (m : nat) (g : nat -> real) (f : nat -> real) : (term287 m g f) = (term299 m g f).
Proof. exact (MK_COMB (@lem7227567 m g f) (@lem7227568)). Qed.
Lemma lem7227572 (m : nat) (g : nat -> real) (f : nat -> real) : (term286 m g f) = (term299 m g f).
Proof. exact (TRANS (@lem7227548 m g f) (@lem7227569 m g f)). Qed.
Lemma lem7227573 (f : nat -> real) (g : nat -> real) (m : nat) : (term300 f g m) = (term300 f g m).
Proof. exact (eq_refl (term300 f g m)). Qed.
Lemma lem7227574 (m : nat) (g : nat -> real) (f : nat -> real) : (term211 m g f) = (term301 m g f).
Proof. exact (MK_COMB (@lem7227573 f g m) (@lem7227572 m g f)). Qed.
Lemma lem7227575 (m : nat) (g : nat -> real) (f : nat -> real) : ((term178 m f g) = (term211 m g f)) = ((term284 m f g) = (term301 m g f)).
Proof. exact (MK_COMB (@lem7227545 m f g) (@lem7227574 m g f)). Qed.
Lemma lem7227578 (m : nat) (g : nat -> real) (f : nat -> real) : ((term284 m f g) = (term301 m g f)) = ((term178 m f g) = (term211 m g f)).
Proof. exact (SYM (@lem7227575 m g f)). Qed.
Lemma lem7227579 (f : nat -> real) : term302 f.
Proof. exact (proj2 (@lem7221724 f)). Qed.
Lemma lem7227580 (f : nat -> real) (m : nat) : term303 f m.
Proof. exact (@lem7227579 f m). Qed.
Lemma lem7227581 (m : nat) (f : nat -> real) : (term303 f m) = (term304 m f).
Proof. exact (eq_refl (term303 f m)). Qed.
Lemma lem7227582 (m : nat) (f : nat -> real) : term304 m f.
Proof. exact (EQ_MP (@lem7227581 m f) (@lem7227580 f m)). Qed.
Lemma lem7227583 (m : nat) (f : nat -> real) (n : nat) : term305 m f n.
Proof. exact (@lem7227582 m f n). Qed.
Lemma lem7227584 (m : nat) (n : nat) (f : nat -> real) : (term305 m f n) = ((term306 m n f) = (term307 m n f)).
Proof. exact (eq_refl (term305 m f n)). Qed.
Lemma lem7227590 (m : nat) (n : nat) : (term163 m n) = ((term163 m n) = True).
Proof. exact (@lem7 (term163 m n)). Qed.
Lemma lem7227595 (m : nat) (n : nat) (f : nat -> real) : (term306 m n f) = (term307 m n f).
Proof. exact (EQ_MP (@lem7227584 m n f) (@lem7227583 m f n)). Qed.
Lemma lem7227596 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term188 m n f g) = (term308 m n f g).
Proof. exact (@lem7227595 m n (term258 f g)). Qed.
Lemma lem7227598 (m : nat) (n : nat) (h1 : term163 m n) : (term163 m n) = True.
Proof. exact (EQ_MP (@lem7227590 m n) (@lem7227244 m n h1)). Qed.
Lemma lem7227599 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7227600 (m : nat) (n : nat) (h1 : term163 m n) : (term309 m n) = (@COND real True).
Proof. exact (MK_COMB (@lem7227599) (@lem7227598 m n h1)). Qed.
Lemma lem7227602 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : (term183 m n f g) = (term184 m n g f)) : (term183 m n f g) = (term184 m n g f).
Proof. exact (h1). Qed.
Lemma lem7227603 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7227604 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : (term183 m n f g) = (term184 m n g f)) : (term310 m n f g) = (term311 m n g f).
Proof. exact (MK_COMB (@lem7227603) (@lem7227602 m n g f h1)). Qed.
Lemma lem7227606 {A B : Type'} (f : A -> B) (y : A) : (term271 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7227607 (f : nat -> real) (y : nat) : (term272 f y) = (f y).
Proof. exact (@lem7227606 nat real f y). Qed.
Lemma lem7227608 (f : nat -> real) (g : nat -> real) (n : nat) : (term312 f g n) = (term313 f g n).
Proof. exact (@lem7227607 (term258 f g) (S n)). Qed.
Lemma lem7227609 (f : nat -> real) (g : nat -> real) (k : nat) : (term275 f g k) = (term276 f g k).
Proof. exact (eq_refl (term275 f g k)). Qed.
Lemma lem7227610 (f : nat -> real) (g : nat -> real) : (term277 f g) = (term258 f g).
Proof. exact (fun_ext (fun k : nat => @lem7227609 f g k)). Qed.
Lemma lem7227611 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem7227612 (f : nat -> real) (g : nat -> real) (n : nat) : (term312 f g n) = (term313 f g n).
Proof. exact (MK_COMB (@lem7227610 f g) (@lem7227611 n)). Qed.
Lemma lem7227613 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7227614 (f : nat -> real) (g : nat -> real) (n : nat) : (term314 f g n) = (term315 f g n).
Proof. exact (MK_COMB (@lem7227613) (@lem7227612 f g n)). Qed.
Lemma lem7227615 (f : nat -> real) (g : nat -> real) (n : nat) : (term313 f g n) = (term316 f g n).
Proof. exact (eq_refl (term313 f g n)). Qed.
Lemma lem7227616 (f : nat -> real) (g : nat -> real) (n : nat) : ((term312 f g n) = (term313 f g n)) = ((term313 f g n) = (term316 f g n)).
Proof. exact (MK_COMB (@lem7227614 f g n) (@lem7227615 f g n)). Qed.
Lemma lem7227617 (f : nat -> real) (g : nat -> real) (n : nat) : (term313 f g n) = (term316 f g n).
Proof. exact (EQ_MP (@lem7227616 f g n) (@lem7227608 f g n)). Qed.
Lemma lem7227618 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : (term183 m n f g) = (term184 m n g f)) : (term317 m f g n) = (term318 m f g n).
Proof. exact (MK_COMB (@lem7227604 m n g f h1) (@lem7227617 f g n)). Qed.
Lemma lem7227619 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : (term319 m f g n) = (term320 m f g n).
Proof. exact (MK_COMB (@lem7227600 m n h1) (@lem7227618 m n g f h2)). Qed.
Lemma lem7227621 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : (term183 m n f g) = (term184 m n g f)) : (term183 m n f g) = (term184 m n g f).
Proof. exact (h1). Qed.
Lemma lem7227622 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : (term308 m n f g) = (term321 m n g f).
Proof. exact (MK_COMB (@lem7227619 m n g f h1 h2) (@lem7227621 m n g f h2)). Qed.
Lemma lem7227624 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7227625 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7227624 real t2 t1). Qed.
Lemma lem7227626 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term321 m n g f) = (term318 m f g n).
Proof. exact (@lem7227625 (term184 m n g f) (term318 m f g n)). Qed.
Lemma lem7227627 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : (term308 m n f g) = (term318 m f g n).
Proof. exact (TRANS (@lem7227622 m n g f h1 h2) (@lem7227626 m f g n)). Qed.
Lemma lem7227628 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : (term188 m n f g) = (term318 m f g n).
Proof. exact (TRANS (@lem7227596 m n f g) (@lem7227627 m n g f h1 h2)). Qed.
Lemma lem7227629 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7227630 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : (term265 m n f g) = (term322 m f g n).
Proof. exact (MK_COMB (@lem7227629) (@lem7227628 m n g f h1 h2)). Qed.
Lemma lem7227632 (m : nat) (n : nat) (f : nat -> real) : (term306 m n f) = (term307 m n f).
Proof. exact (EQ_MP (@lem7227584 m n f) (@lem7227583 m f n)). Qed.
Lemma lem7227633 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term323 m n g f) = (term324 m n g f).
Proof. exact (@lem7227632 m n (term288 g f)). Qed.
Lemma lem7227635 (m : nat) (n : nat) (h1 : term163 m n) : (term163 m n) = True.
Proof. exact (EQ_MP (@lem7227590 m n) (@lem7227244 m n h1)). Qed.
Lemma lem7227636 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7227637 (m : nat) (n : nat) (h1 : term163 m n) : (term309 m n) = (@COND real True).
Proof. exact (MK_COMB (@lem7227636) (@lem7227635 m n h1)). Qed.
Lemma lem7227639 {A B : Type'} (f : A -> B) (y : A) : (term271 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7227640 (f : nat -> real) (y : nat) : (term272 f y) = (f y).
Proof. exact (@lem7227639 nat real f y). Qed.
Lemma lem7227641 (g : nat -> real) (f : nat -> real) (n : nat) : (term325 g f n) = (term326 g f n).
Proof. exact (@lem7227640 (term288 g f) (S n)). Qed.
Lemma lem7227642 (g : nat -> real) (f : nat -> real) (k : nat) : (term291 g f k) = (term292 g f k).
Proof. exact (eq_refl (term291 g f k)). Qed.
Lemma lem7227643 (g : nat -> real) (f : nat -> real) : (term293 g f) = (term288 g f).
Proof. exact (fun_ext (fun k : nat => @lem7227642 g f k)). Qed.
Lemma lem7227644 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem7227645 (g : nat -> real) (f : nat -> real) (n : nat) : (term325 g f n) = (term326 g f n).
Proof. exact (MK_COMB (@lem7227643 g f) (@lem7227644 n)). Qed.
Lemma lem7227646 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7227647 (g : nat -> real) (f : nat -> real) (n : nat) : (term327 g f n) = (term328 g f n).
Proof. exact (MK_COMB (@lem7227646) (@lem7227645 g f n)). Qed.
Lemma lem7227648 (g : nat -> real) (f : nat -> real) (n : nat) : (term326 g f n) = (term329 g f n).
Proof. exact (eq_refl (term326 g f n)). Qed.
Lemma lem7227649 (g : nat -> real) (f : nat -> real) (n : nat) : ((term325 g f n) = (term326 g f n)) = ((term326 g f n) = (term329 g f n)).
Proof. exact (MK_COMB (@lem7227647 g f n) (@lem7227648 g f n)). Qed.
Lemma lem7227650 (g : nat -> real) (f : nat -> real) (n : nat) : (term326 g f n) = (term329 g f n).
Proof. exact (EQ_MP (@lem7227649 g f n) (@lem7227641 g f n)). Qed.
Lemma lem7227651 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term330 m n g f) = (term330 m n g f).
Proof. exact (eq_refl (term330 m n g f)). Qed.
Lemma lem7227652 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term331 m g f n) = (term332 m g f n).
Proof. exact (MK_COMB (@lem7227651 m n g f) (@lem7227650 g f n)). Qed.
Lemma lem7227653 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : term163 m n) : (term333 m g f n) = (term334 m g f n).
Proof. exact (MK_COMB (@lem7227637 m n h1) (@lem7227652 m g f n)). Qed.
Lemma lem7227654 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term335 m n g f) = (term335 m n g f).
Proof. exact (eq_refl (term335 m n g f)). Qed.
Lemma lem7227655 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : term163 m n) : (term324 m n g f) = (term336 m n g f).
Proof. exact (MK_COMB (@lem7227653 g f m n h1) (@lem7227654 m n g f)). Qed.
Lemma lem7227657 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7227658 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7227657 real t2 t1). Qed.
Lemma lem7227659 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term336 m n g f) = (term332 m g f n).
Proof. exact (@lem7227658 (term335 m n g f) (term332 m g f n)). Qed.
Lemma lem7227660 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : term163 m n) : (term324 m n g f) = (term332 m g f n).
Proof. exact (TRANS (@lem7227655 g f m n h1) (@lem7227659 m g f n)). Qed.
Lemma lem7227661 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : term163 m n) : (term323 m n g f) = (term332 m g f n).
Proof. exact (TRANS (@lem7227633 m n g f) (@lem7227660 g f m n h1)). Qed.
Lemma lem7227662 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term337 n f g m) = (term337 n f g m).
Proof. exact (eq_refl (term337 n f g m)). Qed.
Lemma lem7227663 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : term163 m n) : (term232 m n g f) = (term338 m g f n).
Proof. exact (MK_COMB (@lem7227662 n f g m) (@lem7227661 g f m n h1)). Qed.
Lemma lem7227664 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : ((term188 m n f g) = (term232 m n g f)) = ((term318 m f g n) = (term338 m g f n)).
Proof. exact (MK_COMB (@lem7227630 m n g f h1 h2) (@lem7227663 g f m n h1)). Qed.
Lemma lem7227667 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : ((term318 m f g n) = (term338 m g f n)) = ((term188 m n f g) = (term232 m n g f)).
Proof. exact (SYM (@lem7227664 m n g f h1 h2)). Qed.
Lemma lem7227668 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term204 _476 _475 _474 _477) = (term205 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem7227669 (_474 : real) (_475 : Prop) (m : nat) (g : nat -> real) (f : nat -> real) (_477 : real) : (term339 m g f _475 _474 _477) = (term340 _474 _475 m g f _477).
Proof. exact (@lem7227668 _474 _475 (term341 m g f) _477). Qed.
Lemma lem7227670 (m : nat) (g : nat -> real) (f : nat -> real) : (term342 m f g) = (term343 m g f).
Proof. exact (@lem7227669 (term280 f g) (m = (NUMERAL 0)) m g f term29). Qed.
Lemma lem7227671 (m : nat) (g : nat -> real) (f : nat -> real) : (term344 m g f) = (term29 = (term301 m g f)).
Proof. exact (eq_refl (term344 m g f)). Qed.
Lemma lem7227672 (m : nat) : (term345 m) = (term345 m).
Proof. exact (eq_refl (term345 m)). Qed.
Lemma lem7227673 (m : nat) (g : nat -> real) (f : nat -> real) : (term346 m g f) = (term347 m g f).
Proof. exact (MK_COMB (@lem7227672 m) (@lem7227671 m g f)). Qed.
Lemma lem7227674 (m : nat) (g : nat -> real) (f : nat -> real) : (term348 m f g) = ((term280 f g) = (term301 m g f)).
Proof. exact (eq_refl (term348 m f g)). Qed.
Lemma lem7227675 (m : nat) : (term349 m) = (term349 m).
Proof. exact (eq_refl (term349 m)). Qed.
Lemma lem7227676 (m : nat) (g : nat -> real) (f : nat -> real) : (term350 m f g) = (term351 m g f).
Proof. exact (MK_COMB (@lem7227675 m) (@lem7227674 m g f)). Qed.
Lemma lem7227677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7227678 (m : nat) (g : nat -> real) (f : nat -> real) : (term352 m f g) = (term353 m g f).
Proof. exact (MK_COMB (@lem7227677) (@lem7227676 m g f)). Qed.
Lemma lem7227679 (m : nat) (g : nat -> real) (f : nat -> real) : (term343 m g f) = (term354 m g f).
Proof. exact (MK_COMB (@lem7227678 m g f) (@lem7227673 m g f)). Qed.
Lemma lem7227680 (m : nat) (g : nat -> real) (f : nat -> real) : (term342 m f g) = ((term284 m f g) = (term301 m g f)).
Proof. exact (eq_refl (term342 m f g)). Qed.
Lemma lem7227681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7227682 (m : nat) (g : nat -> real) (f : nat -> real) : (term355 m f g) = (term356 m g f).
Proof. exact (MK_COMB (@lem7227681) (@lem7227680 m g f)). Qed.
Lemma lem7227683 (m : nat) (g : nat -> real) (f : nat -> real) : ((term342 m f g) = (term343 m g f)) = (((term284 m f g) = (term301 m g f)) = (term354 m g f)).
Proof. exact (MK_COMB (@lem7227682 m g f) (@lem7227679 m g f)). Qed.
Lemma lem7227684 (m : nat) (g : nat -> real) (f : nat -> real) : ((term284 m f g) = (term301 m g f)) = (term354 m g f).
Proof. exact (EQ_MP (@lem7227683 m g f) (@lem7227670 m g f)). Qed.
Lemma lem7227685 (m : nat) (g : nat -> real) (f : nat -> real) : (term354 m g f) = ((term284 m f g) = (term301 m g f)).
Proof. exact (SYM (@lem7227684 m g f)). Qed.
Lemma lem7227686 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7227687 (m : nat) : (m = (NUMERAL 0)) = ((m = (NUMERAL 0)) = True).
Proof. exact (@lem7 (m = (NUMERAL 0))). Qed.
Lemma lem7227688 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (EQ_MP (@lem7227687 m) (@lem7227686 m h1)). Qed.
Lemma lem7227689 (m : nat) (g : nat -> real) (f : nat -> real) : (term357 m g f) = (term357 m g f).
Proof. exact (eq_refl (term357 m g f)). Qed.
Lemma lem7227690 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term358 g f m) = (term359 m g f).
Proof. exact (MK_COMB (@lem7227689 m g f) (@lem7227688 m h1)). Qed.
Lemma lem7227691 (m : nat) (g : nat -> real) (f : nat -> real) : (term359 m g f) = ((term280 f g) = (term360 m g f)).
Proof. exact (eq_refl (term359 m g f)). Qed.
Lemma lem7227692 (g : nat -> real) (f : nat -> real) (m : nat) : (term361 g f m) = (term361 g f m).
Proof. exact (eq_refl (term361 g f m)). Qed.
Lemma lem7227693 (m : nat) (g : nat -> real) (f : nat -> real) : ((term358 g f m) = (term359 m g f)) = ((term358 g f m) = ((term280 f g) = (term360 m g f))).
Proof. exact (MK_COMB (@lem7227692 g f m) (@lem7227691 m g f)). Qed.
Lemma lem7227694 (m : nat) (g : nat -> real) (f : nat -> real) : (term358 g f m) = ((term280 f g) = (term301 m g f)).
Proof. exact (eq_refl (term358 g f m)). Qed.
Lemma lem7227695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7227696 (m : nat) (g : nat -> real) (f : nat -> real) : (term361 g f m) = (term362 m g f).
Proof. exact (MK_COMB (@lem7227695) (@lem7227694 m g f)). Qed.
Lemma lem7227697 (m : nat) (g : nat -> real) (f : nat -> real) : ((term280 f g) = (term360 m g f)) = ((term280 f g) = (term360 m g f)).
Proof. exact (eq_refl ((term280 f g) = (term360 m g f))). Qed.
Lemma lem7227698 (m : nat) (g : nat -> real) (f : nat -> real) : ((term358 g f m) = ((term280 f g) = (term360 m g f))) = (((term280 f g) = (term301 m g f)) = ((term280 f g) = (term360 m g f))).
Proof. exact (MK_COMB (@lem7227696 m g f) (@lem7227697 m g f)). Qed.
Lemma lem7227699 (m : nat) (g : nat -> real) (f : nat -> real) : ((term358 g f m) = (term359 m g f)) = (((term280 f g) = (term301 m g f)) = ((term280 f g) = (term360 m g f))).
Proof. exact (TRANS (@lem7227693 m g f) (@lem7227698 m g f)). Qed.
Lemma lem7227700 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : ((term280 f g) = (term301 m g f)) = ((term280 f g) = (term360 m g f)).
Proof. exact (EQ_MP (@lem7227699 m g f) (@lem7227690 g f m h1)). Qed.
Lemma lem7227701 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : ((term280 f g) = (term360 m g f)) = ((term280 f g) = (term301 m g f)).
Proof. exact (SYM (@lem7227700 g f m h1)). Qed.
Lemma lem7227702 (m : nat) (h1 : term363 m) : term363 m.
Proof. exact (h1). Qed.
Lemma lem7227703 (m : nat) : term364 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem7227704 (m : nat) (h1 : term363 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem7227703 m (@lem7227702 m h1)). Qed.
Lemma lem7227705 (m : nat) (g : nat -> real) (f : nat -> real) : (term365 m g f) = (term365 m g f).
Proof. exact (eq_refl (term365 m g f)). Qed.
Lemma lem7227706 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term363 m) : (term366 g f m) = (term367 m g f).
Proof. exact (MK_COMB (@lem7227705 m g f) (@lem7227704 m h1)). Qed.
Lemma lem7227707 (m : nat) (g : nat -> real) (f : nat -> real) : (term367 m g f) = (term29 = (term368 m g f)).
Proof. exact (eq_refl (term367 m g f)). Qed.
Lemma lem7227708 (g : nat -> real) (f : nat -> real) (m : nat) : (term369 g f m) = (term369 g f m).
Proof. exact (eq_refl (term369 g f m)). Qed.
Lemma lem7227709 (m : nat) (g : nat -> real) (f : nat -> real) : ((term366 g f m) = (term367 m g f)) = ((term366 g f m) = (term29 = (term368 m g f))).
Proof. exact (MK_COMB (@lem7227708 g f m) (@lem7227707 m g f)). Qed.
Lemma lem7227710 (m : nat) (g : nat -> real) (f : nat -> real) : (term366 g f m) = (term29 = (term301 m g f)).
Proof. exact (eq_refl (term366 g f m)). Qed.
Lemma lem7227711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7227712 (m : nat) (g : nat -> real) (f : nat -> real) : (term369 g f m) = (term370 m g f).
Proof. exact (MK_COMB (@lem7227711) (@lem7227710 m g f)). Qed.
Lemma lem7227713 (m : nat) (g : nat -> real) (f : nat -> real) : (term29 = (term368 m g f)) = (term29 = (term368 m g f)).
Proof. exact (eq_refl (term29 = (term368 m g f))). Qed.
Lemma lem7227714 (m : nat) (g : nat -> real) (f : nat -> real) : ((term366 g f m) = (term29 = (term368 m g f))) = ((term29 = (term301 m g f)) = (term29 = (term368 m g f))).
Proof. exact (MK_COMB (@lem7227712 m g f) (@lem7227713 m g f)). Qed.
Lemma lem7227715 (m : nat) (g : nat -> real) (f : nat -> real) : ((term366 g f m) = (term367 m g f)) = ((term29 = (term301 m g f)) = (term29 = (term368 m g f))).
Proof. exact (TRANS (@lem7227709 m g f) (@lem7227714 m g f)). Qed.
Lemma lem7227716 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term363 m) : (term29 = (term301 m g f)) = (term29 = (term368 m g f)).
Proof. exact (EQ_MP (@lem7227715 m g f) (@lem7227706 g f m h1)). Qed.
Lemma lem7227717 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term363 m) : (term29 = (term368 m g f)) = (term29 = (term301 m g f)).
Proof. exact (SYM (@lem7227716 g f m h1)). Qed.
Lemma lem7227723 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7227724 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7227725 (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (f m) = (term371 f).
Proof. exact (MK_COMB (@lem7227724 f) (@lem7227723 m h1)). Qed.
Lemma lem7227726 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7227727 (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term372 f m) = (term373 f).
Proof. exact (MK_COMB (@lem7227726) (@lem7227725 f m h1)). Qed.
Lemma lem7227729 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7227730 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7227731 (g : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (g m) = (term371 g).
Proof. exact (MK_COMB (@lem7227730 g) (@lem7227729 m h1)). Qed.
Lemma lem7227732 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term374 f g m) = (term375 f g).
Proof. exact (MK_COMB (@lem7227727 f m h1) (@lem7227731 g m h1)). Qed.
Lemma lem7227733 (f : nat -> real) (g : nat -> real) : (term376 f g) = (term376 f g).
Proof. exact (eq_refl (term376 f g)). Qed.
Lemma lem7227734 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term377 f g m) = (term378 f g).
Proof. exact (MK_COMB (@lem7227733 f g) (@lem7227732 f g m h1)). Qed.
Lemma lem7227735 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7227736 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term300 f g m) = (term379 f g).
Proof. exact (MK_COMB (@lem7227735) (@lem7227734 f g m h1)). Qed.
Lemma lem7227738 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7227739 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7227738 real t2 t1). Qed.
Lemma lem7227740 (g : nat -> real) (f : nat -> real) : (term380 g f) = (term296 g f).
Proof. exact (@lem7227739 term29 (term296 g f)). Qed.
Lemma lem7227741 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term360 m g f) = (term381 g f).
Proof. exact (MK_COMB (@lem7227736 f g m h1) (@lem7227740 g f)). Qed.
Lemma lem7227742 (f : nat -> real) (g : nat -> real) : (term382 f g) = (term382 f g).
Proof. exact (eq_refl (term382 f g)). Qed.
Lemma lem7227743 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : ((term280 f g) = (term360 m g f)) = ((term280 f g) = (term381 g f)).
Proof. exact (MK_COMB (@lem7227742 f g) (@lem7227741 g f m h1)). Qed.
Lemma lem7227746 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : ((term280 f g) = (term381 g f)) = ((term280 f g) = (term360 m g f)).
Proof. exact (SYM (@lem7227743 g f m h1)). Qed.
Lemma lem7227765 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7227766 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7227765 real t1 t2). Qed.
Lemma lem7227767 (g : nat -> real) (f : nat -> real) : (term383 g f) = term29.
Proof. exact (@lem7227766 (term296 g f) term29). Qed.
Lemma lem7227768 (f : nat -> real) (g : nat -> real) (m : nat) : (term300 f g m) = (term300 f g m).
Proof. exact (eq_refl (term300 f g m)). Qed.
Lemma lem7227769 (f : nat -> real) (g : nat -> real) (m : nat) : (term368 m g f) = (term384 f g m).
Proof. exact (MK_COMB (@lem7227768 f g m) (@lem7227767 g f)). Qed.
Lemma lem7227770 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem7227771 (f : nat -> real) (g : nat -> real) (m : nat) : (term29 = (term368 m g f)) = (term29 = (term384 f g m)).
Proof. exact (MK_COMB (@lem7227770) (@lem7227769 f g m)). Qed.
Lemma lem7227774 (m : nat) (g : nat -> real) (f : nat -> real) : (term29 = (term384 f g m)) = (term29 = (term368 m g f)).
Proof. exact (SYM (@lem7227771 f g m)). Qed.
Lemma lem7227785 (g : nat -> real) (f : nat -> real) : (term385 g f) = (term386 g f).
Proof. exact (@lem1988318 (term280 f g) (term381 g f)). Qed.
Lemma lem7227791 (f : nat -> real) : (term387 f) = (term388 f).
Proof. exact (@lem1982792 (term389 f) (term371 f)). Qed.
Lemma lem7227796 (f : nat -> real) : (term388 f) = (term390 f).
Proof. exact (@lem1982761 (term391 f) (term389 f)). Qed.
Lemma lem7227798 (f : nat -> real) : (term387 f) = (term390 f).
Proof. exact (TRANS (@lem7227791 f) (@lem7227796 f)). Qed.
Lemma lem7227801 (g : nat -> real) : (term392 g) = (term392 g).
Proof. exact (eq_refl (term392 g)). Qed.
Lemma lem7227802 (g : nat -> real) (f : nat -> real) : (term296 g f) = (term393 g f).
Proof. exact (MK_COMB (@lem7227801 g) (@lem7227798 f)). Qed.
Lemma lem7227803 (g : nat -> real) (f : nat -> real) : (term393 g f) = (term394 g f).
Proof. exact (@lem1982781 (term391 f) (term389 g) (term389 f)). Qed.
Lemma lem7227804 (f : nat -> real) (g : nat -> real) : (term395 g f) = (term395 f g).
Proof. exact (@lem1982747 (term389 f) (term389 g)). Qed.
Lemma lem7227805 (g : nat -> real) (f : nat -> real) : (term396 g f) = (term397 g f).
Proof. exact (@lem1982751 term62 (term389 g) (term371 f)). Qed.
Lemma lem7227806 (f : nat -> real) (g : nat -> real) : (term398 g f) = (term399 f g).
Proof. exact (@lem1982747 (term371 f) (term389 g)). Qed.
Lemma lem7227807 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7227808 (f : nat -> real) (g : nat -> real) : (term397 g f) = (term400 f g).
Proof. exact (MK_COMB (@lem7227807) (@lem7227806 f g)). Qed.
Lemma lem7227809 (f : nat -> real) (g : nat -> real) : (term396 g f) = (term400 f g).
Proof. exact (TRANS (@lem7227805 g f) (@lem7227808 f g)). Qed.
Lemma lem7227810 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7227811 (f : nat -> real) (g : nat -> real) : (term401 g f) = (term402 f g).
Proof. exact (MK_COMB (@lem7227810) (@lem7227809 f g)). Qed.
Lemma lem7227812 (f : nat -> real) (g : nat -> real) : (term394 g f) = (term403 f g).
Proof. exact (MK_COMB (@lem7227811 f g) (@lem7227804 f g)). Qed.
Lemma lem7227813 (f : nat -> real) (g : nat -> real) : (term393 g f) = (term403 f g).
Proof. exact (TRANS (@lem7227803 g f) (@lem7227812 f g)). Qed.
Lemma lem7227814 (f : nat -> real) (g : nat -> real) : (term296 g f) = (term403 f g).
Proof. exact (TRANS (@lem7227802 g f) (@lem7227813 f g)). Qed.
Lemma lem7227832 (f : nat -> real) (g : nat -> real) : (term378 f g) = (term404 f g).
Proof. exact (@lem1982792 (term395 f g) (term375 f g)). Qed.
Lemma lem7227837 (f : nat -> real) (g : nat -> real) : (term404 f g) = (term405 f g).
Proof. exact (@lem1982761 (term406 f g) (term395 f g)). Qed.
Lemma lem7227839 (f : nat -> real) (g : nat -> real) : (term378 f g) = (term405 f g).
Proof. exact (TRANS (@lem7227832 f g) (@lem7227837 f g)). Qed.
Lemma lem7227840 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7227841 (f : nat -> real) (g : nat -> real) : (term379 f g) = (term407 f g).
Proof. exact (MK_COMB (@lem7227840) (@lem7227839 f g)). Qed.
Lemma lem7227842 (f : nat -> real) (g : nat -> real) : (term381 g f) = (term408 f g).
Proof. exact (MK_COMB (@lem7227841 f g) (@lem7227814 f g)). Qed.
Lemma lem7227843 (f : nat -> real) (g : nat -> real) : (term408 f g) = (term409 f g).
Proof. exact (@lem1982792 (term405 f g) (term403 f g)). Qed.
Lemma lem7227844 (f : nat -> real) (g : nat -> real) : (term410 f g) = (term411 f g).
Proof. exact (@lem1982781 (term400 f g) term62 (term395 f g)). Qed.
Lemma lem7227845 (f : nat -> real) (g : nat -> real) : (term412 f g) = (term412 f g).
Proof. exact (eq_refl (term412 f g)). Qed.
Lemma lem7227846 (f : nat -> real) (g : nat -> real) : (term413 f g) = (term414 f g).
Proof. exact (@lem1982749 term62 term62 (term399 f g)). Qed.
Lemma lem7227848 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7227849 : term62 = term63.
Proof. exact (@lem7227848 term13). Qed.
Lemma lem7227851 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7227852 : term62 = term63.
Proof. exact (@lem7227851 term13). Qed.
Lemma lem7227853 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7227854 : term64 = term65.
Proof. exact (MK_COMB (@lem7227853) (@lem7227852)). Qed.
Lemma lem7227855 : term415 = term416.
Proof. exact (MK_COMB (@lem7227854) (@lem7227849)). Qed.
Lemma lem7227856 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7227858 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7227859 : term71 = term72.
Proof. exact (@lem7227858 term13 term13). Qed.
Lemma lem7227860 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7227861 : term74 = term13.
Proof. exact (EQ_MP (@lem7227860) (@lem940073)). Qed.
Lemma lem7227862 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7227863 : term72 = term44.
Proof. exact (MK_COMB (@lem7227862) (@lem7227861)). Qed.
Lemma lem7227864 : term71 = term44.
Proof. exact (TRANS (@lem7227859) (@lem7227863)). Qed.
Lemma lem7227866 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7227867 : term415 = term72.
Proof. exact (@lem7227866 term13 term13). Qed.
Lemma lem7227868 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7227869 : term74 = term13.
Proof. exact (EQ_MP (@lem7227868) (@lem940073)). Qed.
Lemma lem7227870 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7227871 : term72 = term44.
Proof. exact (MK_COMB (@lem7227870) (@lem7227869)). Qed.
Lemma lem7227872 : term415 = term44.
Proof. exact (TRANS (@lem7227867) (@lem7227871)). Qed.
Lemma lem7227873 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7227874 : term419 = term420.
Proof. exact (MK_COMB (@lem7227873) (@lem7227872)). Qed.
Lemma lem7227875 : term417 = term88.
Proof. exact (MK_COMB (@lem7227874) (@lem7227864)). Qed.
Lemma lem7227876 : term416 = term88.
Proof. exact (TRANS (@lem7227856) (@lem7227875)). Qed.
Lemma lem7227877 : term415 = term88.
Proof. exact (TRANS (@lem7227855) (@lem7227876)). Qed.
Lemma lem7227879 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7227880 : term88 = term44.
Proof. exact (@lem7227879 term44). Qed.
Lemma lem7227881 : term415 = term44.
Proof. exact (TRANS (@lem7227877) (@lem7227880)). Qed.
Lemma lem7227882 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7227883 : term421 = term422.
Proof. exact (MK_COMB (@lem7227882) (@lem7227881)). Qed.
Lemma lem7227884 (f : nat -> real) (g : nat -> real) : (term399 f g) = (term399 f g).
Proof. exact (eq_refl (term399 f g)). Qed.
Lemma lem7227885 (f : nat -> real) (g : nat -> real) : (term414 f g) = (term423 f g).
Proof. exact (MK_COMB (@lem7227883) (@lem7227884 f g)). Qed.
Lemma lem7227886 (f : nat -> real) (g : nat -> real) : (term413 f g) = (term423 f g).
Proof. exact (TRANS (@lem7227846 f g) (@lem7227885 f g)). Qed.
Lemma lem7227887 (f : nat -> real) (g : nat -> real) : (term423 f g) = (term399 f g).
Proof. exact (@lem1982709 (term399 f g)). Qed.
Lemma lem7227888 (f : nat -> real) (g : nat -> real) : (term413 f g) = (term399 f g).
Proof. exact (TRANS (@lem7227886 f g) (@lem7227887 f g)). Qed.
Lemma lem7227889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7227890 (f : nat -> real) (g : nat -> real) : (term424 f g) = (term425 f g).
Proof. exact (MK_COMB (@lem7227889) (@lem7227888 f g)). Qed.
Lemma lem7227891 (f : nat -> real) (g : nat -> real) : (term411 f g) = (term426 f g).
Proof. exact (MK_COMB (@lem7227890 f g) (@lem7227845 f g)). Qed.
Lemma lem7227892 (f : nat -> real) (g : nat -> real) : (term410 f g) = (term426 f g).
Proof. exact (TRANS (@lem7227844 f g) (@lem7227891 f g)). Qed.
Lemma lem7227893 (f : nat -> real) (g : nat -> real) : (term427 f g) = (term427 f g).
Proof. exact (eq_refl (term427 f g)). Qed.
Lemma lem7227894 (f : nat -> real) (g : nat -> real) : (term409 f g) = (term428 f g).
Proof. exact (MK_COMB (@lem7227893 f g) (@lem7227892 f g)). Qed.
Lemma lem7227895 (f : nat -> real) (g : nat -> real) : (term428 f g) = (term429 f g).
Proof. exact (@lem1982755 (term406 f g) (term395 f g) (term426 f g)). Qed.
Lemma lem7227896 (f : nat -> real) (g : nat -> real) : (term430 f g) = (term431 f g).
Proof. exact (@lem1982757 (term399 f g) (term395 f g) (term412 f g)). Qed.
Lemma lem7227897 (f : nat -> real) (g : nat -> real) : (term432 f g) = (term433 f g).
Proof. exact (@lem1982715 term62 (term395 f g)). Qed.
Lemma lem7227899 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7227900 : term44 = term88.
Proof. exact (@lem7227899 term13). Qed.
Lemma lem7227902 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7227903 : term62 = term63.
Proof. exact (@lem7227902 term13). Qed.
Lemma lem7227904 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7227905 : term104 = term105.
Proof. exact (MK_COMB (@lem7227904) (@lem7227903)). Qed.
Lemma lem7227906 : term106 = term107.
Proof. exact (MK_COMB (@lem7227905) (@lem7227900)). Qed.
Lemma lem7227907 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7227909 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7227910 : term110 = term111.
Proof. exact (@lem7227909 (NUMERAL 0) term13). Qed.
Lemma lem7227911 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7227912 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7227913 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7227912 h1) (fun h1 : term111 = True => @lem7227911)). Qed.
Lemma lem7227914 : term111 = True.
Proof. exact (EQ_MP (@lem7227913) (@lem7227911)). Qed.
Lemma lem7227915 : term110 = True.
Proof. exact (TRANS (@lem7227910) (@lem7227914)). Qed.
Lemma lem7227916 : True = term110.
Proof. exact (SYM (@lem7227915)). Qed.
Lemma lem7227917 : term110.
Proof. exact (EQ_MP (@lem7227916) (@lem0)). Qed.
Lemma lem7227918 : term113.
Proof. exact (@lem7227907 (@lem7227917)). Qed.
Lemma lem7227920 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7227921 : term110 = term111.
Proof. exact (@lem7227920 (NUMERAL 0) term13). Qed.
Lemma lem7227922 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7227923 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7227924 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7227923 h1) (fun h1 : term111 = True => @lem7227922)). Qed.
Lemma lem7227925 : term111 = True.
Proof. exact (EQ_MP (@lem7227924) (@lem7227922)). Qed.
Lemma lem7227926 : term110 = True.
Proof. exact (TRANS (@lem7227921) (@lem7227925)). Qed.
Lemma lem7227927 : True = term110.
Proof. exact (SYM (@lem7227926)). Qed.
Lemma lem7227928 : term110.
Proof. exact (EQ_MP (@lem7227927) (@lem0)). Qed.
Lemma lem7227929 : term114.
Proof. exact (@lem7227918 (@lem7227928)). Qed.
Lemma lem7227931 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7227932 : term110 = term111.
Proof. exact (@lem7227931 (NUMERAL 0) term13). Qed.
Lemma lem7227933 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7227934 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7227935 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7227934 h1) (fun h1 : term111 = True => @lem7227933)). Qed.
Lemma lem7227936 : term111 = True.
Proof. exact (EQ_MP (@lem7227935) (@lem7227933)). Qed.
Lemma lem7227937 : term110 = True.
Proof. exact (TRANS (@lem7227932) (@lem7227936)). Qed.
Lemma lem7227938 : True = term110.
Proof. exact (SYM (@lem7227937)). Qed.
Lemma lem7227939 : term110.
Proof. exact (EQ_MP (@lem7227938) (@lem0)). Qed.
Lemma lem7227940 : term115.
Proof. exact (@lem7227929 (@lem7227939)). Qed.
Lemma lem7227942 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7227943 : term71 = term72.
Proof. exact (@lem7227942 term13 term13). Qed.
Lemma lem7227944 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7227945 : term74 = term13.
Proof. exact (EQ_MP (@lem7227944) (@lem940073)). Qed.
Lemma lem7227946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7227947 : term72 = term44.
Proof. exact (MK_COMB (@lem7227946) (@lem7227945)). Qed.
Lemma lem7227948 : term71 = term44.
Proof. exact (TRANS (@lem7227943) (@lem7227947)). Qed.
Lemma lem7227950 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7227951 : term89 = term94.
Proof. exact (@lem7227950 term13 term13). Qed.
Lemma lem7227952 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7227953 : term74 = term13.
Proof. exact (EQ_MP (@lem7227952) (@lem940073)). Qed.
Lemma lem7227954 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7227955 : term72 = term44.
Proof. exact (MK_COMB (@lem7227954) (@lem7227953)). Qed.
Lemma lem7227956 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7227957 : term94 = term62.
Proof. exact (MK_COMB (@lem7227956) (@lem7227955)). Qed.
Lemma lem7227958 : term89 = term62.
Proof. exact (TRANS (@lem7227951) (@lem7227957)). Qed.
Lemma lem7227959 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7227960 : term116 = term104.
Proof. exact (MK_COMB (@lem7227959) (@lem7227958)). Qed.
Lemma lem7227961 : term117 = term106.
Proof. exact (MK_COMB (@lem7227960) (@lem7227948)). Qed.
Lemma lem7227963 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7227964 : term106 = term29.
Proof. exact (@lem7227963 term13). Qed.
Lemma lem7227965 : term117 = term29.
Proof. exact (TRANS (@lem7227961) (@lem7227964)). Qed.
Lemma lem7227966 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7227967 : term119 = term120.
Proof. exact (MK_COMB (@lem7227966) (@lem7227965)). Qed.
Lemma lem7227968 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7227969 : term121 = term122.
Proof. exact (MK_COMB (@lem7227967) (@lem7227968)). Qed.
Lemma lem7227971 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7227972 : term122 = term29.
Proof. exact (@lem7227971 term13). Qed.
Lemma lem7227973 : term121 = term29.
Proof. exact (TRANS (@lem7227969) (@lem7227972)). Qed.
Lemma lem7227975 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7227976 : term71 = term72.
Proof. exact (@lem7227975 term13 term13). Qed.
Lemma lem7227977 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7227978 : term74 = term13.
Proof. exact (EQ_MP (@lem7227977) (@lem940073)). Qed.
Lemma lem7227979 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7227980 : term72 = term44.
Proof. exact (MK_COMB (@lem7227979) (@lem7227978)). Qed.
Lemma lem7227981 : term71 = term44.
Proof. exact (TRANS (@lem7227976) (@lem7227980)). Qed.
Lemma lem7227982 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7227983 : term124 = term122.
Proof. exact (MK_COMB (@lem7227982) (@lem7227981)). Qed.
Lemma lem7227985 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7227986 : term122 = term29.
Proof. exact (@lem7227985 term13). Qed.
Lemma lem7227987 : term124 = term29.
Proof. exact (TRANS (@lem7227983) (@lem7227986)). Qed.
Lemma lem7227988 : term29 = term124.
Proof. exact (SYM (@lem7227987)). Qed.
Lemma lem7227989 : term121 = term124.
Proof. exact (TRANS (@lem7227973) (@lem7227988)). Qed.
Lemma lem7227990 : term107 = term59.
Proof. exact (@lem7227940 (@lem7227989)). Qed.
Lemma lem7227991 : term106 = term59.
Proof. exact (TRANS (@lem7227906) (@lem7227990)). Qed.
Lemma lem7227993 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7227994 : term59 = term29.
Proof. exact (@lem7227993 term29). Qed.
Lemma lem7227995 : term106 = term29.
Proof. exact (TRANS (@lem7227991) (@lem7227994)). Qed.
Lemma lem7227996 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7227997 : term125 = term120.
Proof. exact (MK_COMB (@lem7227996) (@lem7227995)). Qed.
Lemma lem7227998 (f : nat -> real) (g : nat -> real) : (term395 f g) = (term395 f g).
Proof. exact (eq_refl (term395 f g)). Qed.
Lemma lem7227999 (f : nat -> real) (g : nat -> real) : (term433 f g) = (term434 f g).
Proof. exact (MK_COMB (@lem7227997) (@lem7227998 f g)). Qed.
Lemma lem7228000 (f : nat -> real) (g : nat -> real) : (term432 f g) = (term434 f g).
Proof. exact (TRANS (@lem7227897 f g) (@lem7227999 f g)). Qed.
Lemma lem7228001 (f : nat -> real) (g : nat -> real) : (term434 f g) = term29.
Proof. exact (@lem1982719 (term395 f g)). Qed.
Lemma lem7228002 (f : nat -> real) (g : nat -> real) : (term432 f g) = term29.
Proof. exact (TRANS (@lem7228000 f g) (@lem7228001 f g)). Qed.
Lemma lem7228003 (f : nat -> real) (g : nat -> real) : (term425 f g) = (term425 f g).
Proof. exact (eq_refl (term425 f g)). Qed.
Lemma lem7228004 (f : nat -> real) (g : nat -> real) : (term431 f g) = (term435 f g).
Proof. exact (MK_COMB (@lem7228003 f g) (@lem7228002 f g)). Qed.
Lemma lem7228005 (f : nat -> real) (g : nat -> real) : (term430 f g) = (term435 f g).
Proof. exact (TRANS (@lem7227896 f g) (@lem7228004 f g)). Qed.
Lemma lem7228006 (f : nat -> real) (g : nat -> real) : (term435 f g) = (term399 f g).
Proof. exact (@lem1982723 (term399 f g)). Qed.
Lemma lem7228007 (f : nat -> real) (g : nat -> real) : (term430 f g) = (term399 f g).
Proof. exact (TRANS (@lem7228005 f g) (@lem7228006 f g)). Qed.
Lemma lem7228008 (f : nat -> real) (g : nat -> real) : (term436 f g) = (term436 f g).
Proof. exact (eq_refl (term436 f g)). Qed.
Lemma lem7228009 (f : nat -> real) (g : nat -> real) : (term429 f g) = (term437 f g).
Proof. exact (MK_COMB (@lem7228008 f g) (@lem7228007 f g)). Qed.
Lemma lem7228010 (f : nat -> real) (g : nat -> real) : (term428 f g) = (term437 f g).
Proof. exact (TRANS (@lem7227895 f g) (@lem7228009 f g)). Qed.
Lemma lem7228011 (f : nat -> real) (g : nat -> real) : (term409 f g) = (term437 f g).
Proof. exact (TRANS (@lem7227894 f g) (@lem7228010 f g)). Qed.
Lemma lem7228012 (f : nat -> real) (g : nat -> real) : (term408 f g) = (term437 f g).
Proof. exact (TRANS (@lem7227843 f g) (@lem7228011 f g)). Qed.
Lemma lem7228013 (f : nat -> real) (g : nat -> real) : (term381 g f) = (term437 f g).
Proof. exact (TRANS (@lem7227842 f g) (@lem7228012 f g)). Qed.
Lemma lem7228019 (g : nat -> real) : (term387 g) = (term388 g).
Proof. exact (@lem1982792 (term389 g) (term371 g)). Qed.
Lemma lem7228024 (g : nat -> real) : (term388 g) = (term390 g).
Proof. exact (@lem1982761 (term391 g) (term389 g)). Qed.
Lemma lem7228026 (g : nat -> real) : (term387 g) = (term390 g).
Proof. exact (TRANS (@lem7228019 g) (@lem7228024 g)). Qed.
Lemma lem7228029 (f : nat -> real) : (term373 f) = (term373 f).
Proof. exact (eq_refl (term373 f)). Qed.
Lemma lem7228030 (f : nat -> real) (g : nat -> real) : (term280 f g) = (term438 f g).
Proof. exact (MK_COMB (@lem7228029 f) (@lem7228026 g)). Qed.
Lemma lem7228031 (f : nat -> real) (g : nat -> real) : (term438 f g) = (term439 f g).
Proof. exact (@lem1982781 (term391 g) (term371 f) (term389 g)). Qed.
Lemma lem7228032 (f : nat -> real) (g : nat -> real) : (term399 f g) = (term399 f g).
Proof. exact (eq_refl (term399 f g)). Qed.
Lemma lem7228037 (f : nat -> real) (g : nat -> real) : (term440 f g) = (term406 f g).
Proof. exact (@lem1982751 term62 (term371 f) (term371 g)). Qed.
Lemma lem7228038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7228039 (f : nat -> real) (g : nat -> real) : (term441 f g) = (term436 f g).
Proof. exact (MK_COMB (@lem7228038) (@lem7228037 f g)). Qed.
Lemma lem7228040 (f : nat -> real) (g : nat -> real) : (term439 f g) = (term437 f g).
Proof. exact (MK_COMB (@lem7228039 f g) (@lem7228032 f g)). Qed.
Lemma lem7228041 (f : nat -> real) (g : nat -> real) : (term438 f g) = (term437 f g).
Proof. exact (TRANS (@lem7228031 f g) (@lem7228040 f g)). Qed.
Lemma lem7228042 (f : nat -> real) (g : nat -> real) : (term280 f g) = (term437 f g).
Proof. exact (TRANS (@lem7228030 f g) (@lem7228041 f g)). Qed.
Lemma lem7228043 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7228044 (f : nat -> real) (g : nat -> real) : (term442 f g) = (term443 f g).
Proof. exact (MK_COMB (@lem7228043) (@lem7228042 f g)). Qed.
Lemma lem7228045 (f : nat -> real) (g : nat -> real) : (term444 g f) = (term445 f g).
Proof. exact (MK_COMB (@lem7228044 f g) (@lem7228013 f g)). Qed.
Lemma lem7228046 (f : nat -> real) (g : nat -> real) : (term445 f g) = (term446 f g).
Proof. exact (@lem1982792 (term437 f g) (term437 f g)). Qed.
Lemma lem7228047 (f : nat -> real) (g : nat -> real) : (term447 f g) = (term448 f g).
Proof. exact (@lem1982781 (term406 f g) term62 (term399 f g)). Qed.
Lemma lem7228048 (f : nat -> real) (g : nat -> real) : (term400 f g) = (term400 f g).
Proof. exact (eq_refl (term400 f g)). Qed.
Lemma lem7228049 (f : nat -> real) (g : nat -> real) : (term449 f g) = (term450 f g).
Proof. exact (@lem1982749 term62 term62 (term375 f g)). Qed.
Lemma lem7228051 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7228052 : term62 = term63.
Proof. exact (@lem7228051 term13). Qed.
Lemma lem7228054 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7228055 : term62 = term63.
Proof. exact (@lem7228054 term13). Qed.
Lemma lem7228056 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228057 : term64 = term65.
Proof. exact (MK_COMB (@lem7228056) (@lem7228055)). Qed.
Lemma lem7228058 : term415 = term416.
Proof. exact (MK_COMB (@lem7228057) (@lem7228052)). Qed.
Lemma lem7228059 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7228061 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228062 : term71 = term72.
Proof. exact (@lem7228061 term13 term13). Qed.
Lemma lem7228063 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228064 : term74 = term13.
Proof. exact (EQ_MP (@lem7228063) (@lem940073)). Qed.
Lemma lem7228065 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228066 : term72 = term44.
Proof. exact (MK_COMB (@lem7228065) (@lem7228064)). Qed.
Lemma lem7228067 : term71 = term44.
Proof. exact (TRANS (@lem7228062) (@lem7228066)). Qed.
Lemma lem7228069 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7228070 : term415 = term72.
Proof. exact (@lem7228069 term13 term13). Qed.
Lemma lem7228071 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228072 : term74 = term13.
Proof. exact (EQ_MP (@lem7228071) (@lem940073)). Qed.
Lemma lem7228073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228074 : term72 = term44.
Proof. exact (MK_COMB (@lem7228073) (@lem7228072)). Qed.
Lemma lem7228075 : term415 = term44.
Proof. exact (TRANS (@lem7228070) (@lem7228074)). Qed.
Lemma lem7228076 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7228077 : term419 = term420.
Proof. exact (MK_COMB (@lem7228076) (@lem7228075)). Qed.
Lemma lem7228078 : term417 = term88.
Proof. exact (MK_COMB (@lem7228077) (@lem7228067)). Qed.
Lemma lem7228079 : term416 = term88.
Proof. exact (TRANS (@lem7228059) (@lem7228078)). Qed.
Lemma lem7228080 : term415 = term88.
Proof. exact (TRANS (@lem7228058) (@lem7228079)). Qed.
Lemma lem7228082 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7228083 : term88 = term44.
Proof. exact (@lem7228082 term44). Qed.
Lemma lem7228084 : term415 = term44.
Proof. exact (TRANS (@lem7228080) (@lem7228083)). Qed.
Lemma lem7228085 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228086 : term421 = term422.
Proof. exact (MK_COMB (@lem7228085) (@lem7228084)). Qed.
Lemma lem7228087 (f : nat -> real) (g : nat -> real) : (term375 f g) = (term375 f g).
Proof. exact (eq_refl (term375 f g)). Qed.
Lemma lem7228088 (f : nat -> real) (g : nat -> real) : (term450 f g) = (term451 f g).
Proof. exact (MK_COMB (@lem7228086) (@lem7228087 f g)). Qed.
Lemma lem7228089 (f : nat -> real) (g : nat -> real) : (term449 f g) = (term451 f g).
Proof. exact (TRANS (@lem7228049 f g) (@lem7228088 f g)). Qed.
Lemma lem7228090 (f : nat -> real) (g : nat -> real) : (term451 f g) = (term375 f g).
Proof. exact (@lem1982709 (term375 f g)). Qed.
Lemma lem7228091 (f : nat -> real) (g : nat -> real) : (term449 f g) = (term375 f g).
Proof. exact (TRANS (@lem7228089 f g) (@lem7228090 f g)). Qed.
Lemma lem7228092 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7228093 (f : nat -> real) (g : nat -> real) : (term452 f g) = (term453 f g).
Proof. exact (MK_COMB (@lem7228092) (@lem7228091 f g)). Qed.
Lemma lem7228094 (f : nat -> real) (g : nat -> real) : (term448 f g) = (term454 f g).
Proof. exact (MK_COMB (@lem7228093 f g) (@lem7228048 f g)). Qed.
Lemma lem7228095 (f : nat -> real) (g : nat -> real) : (term447 f g) = (term454 f g).
Proof. exact (TRANS (@lem7228047 f g) (@lem7228094 f g)). Qed.
Lemma lem7228096 (f : nat -> real) (g : nat -> real) : (term455 f g) = (term455 f g).
Proof. exact (eq_refl (term455 f g)). Qed.
Lemma lem7228097 (f : nat -> real) (g : nat -> real) : (term446 f g) = (term456 f g).
Proof. exact (MK_COMB (@lem7228096 f g) (@lem7228095 f g)). Qed.
Lemma lem7228098 (f : nat -> real) (g : nat -> real) : (term456 f g) = (term457 f g).
Proof. exact (@lem1982753 (term406 f g) (term375 f g) (term399 f g) (term400 f g)). Qed.
Lemma lem7228099 (f : nat -> real) (g : nat -> real) : (term458 f g) = (term459 f g).
Proof. exact (@lem1982713 term62 (term375 f g)). Qed.
Lemma lem7228101 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228102 : term44 = term88.
Proof. exact (@lem7228101 term13). Qed.
Lemma lem7228104 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7228105 : term62 = term63.
Proof. exact (@lem7228104 term13). Qed.
Lemma lem7228106 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7228107 : term104 = term105.
Proof. exact (MK_COMB (@lem7228106) (@lem7228105)). Qed.
Lemma lem7228108 : term106 = term107.
Proof. exact (MK_COMB (@lem7228107) (@lem7228102)). Qed.
Lemma lem7228109 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7228111 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228112 : term110 = term111.
Proof. exact (@lem7228111 (NUMERAL 0) term13). Qed.
Lemma lem7228113 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228114 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228115 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228114 h1) (fun h1 : term111 = True => @lem7228113)). Qed.
Lemma lem7228116 : term111 = True.
Proof. exact (EQ_MP (@lem7228115) (@lem7228113)). Qed.
Lemma lem7228117 : term110 = True.
Proof. exact (TRANS (@lem7228112) (@lem7228116)). Qed.
Lemma lem7228118 : True = term110.
Proof. exact (SYM (@lem7228117)). Qed.
Lemma lem7228119 : term110.
Proof. exact (EQ_MP (@lem7228118) (@lem0)). Qed.
Lemma lem7228120 : term113.
Proof. exact (@lem7228109 (@lem7228119)). Qed.
Lemma lem7228122 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228123 : term110 = term111.
Proof. exact (@lem7228122 (NUMERAL 0) term13). Qed.
Lemma lem7228124 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228125 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228126 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228125 h1) (fun h1 : term111 = True => @lem7228124)). Qed.
Lemma lem7228127 : term111 = True.
Proof. exact (EQ_MP (@lem7228126) (@lem7228124)). Qed.
Lemma lem7228128 : term110 = True.
Proof. exact (TRANS (@lem7228123) (@lem7228127)). Qed.
Lemma lem7228129 : True = term110.
Proof. exact (SYM (@lem7228128)). Qed.
Lemma lem7228130 : term110.
Proof. exact (EQ_MP (@lem7228129) (@lem0)). Qed.
Lemma lem7228131 : term114.
Proof. exact (@lem7228120 (@lem7228130)). Qed.
Lemma lem7228133 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228134 : term110 = term111.
Proof. exact (@lem7228133 (NUMERAL 0) term13). Qed.
Lemma lem7228135 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228136 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228137 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228136 h1) (fun h1 : term111 = True => @lem7228135)). Qed.
Lemma lem7228138 : term111 = True.
Proof. exact (EQ_MP (@lem7228137) (@lem7228135)). Qed.
Lemma lem7228139 : term110 = True.
Proof. exact (TRANS (@lem7228134) (@lem7228138)). Qed.
Lemma lem7228140 : True = term110.
Proof. exact (SYM (@lem7228139)). Qed.
Lemma lem7228141 : term110.
Proof. exact (EQ_MP (@lem7228140) (@lem0)). Qed.
Lemma lem7228142 : term115.
Proof. exact (@lem7228131 (@lem7228141)). Qed.
Lemma lem7228144 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228145 : term71 = term72.
Proof. exact (@lem7228144 term13 term13). Qed.
Lemma lem7228146 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228147 : term74 = term13.
Proof. exact (EQ_MP (@lem7228146) (@lem940073)). Qed.
Lemma lem7228148 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228149 : term72 = term44.
Proof. exact (MK_COMB (@lem7228148) (@lem7228147)). Qed.
Lemma lem7228150 : term71 = term44.
Proof. exact (TRANS (@lem7228145) (@lem7228149)). Qed.
Lemma lem7228152 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7228153 : term89 = term94.
Proof. exact (@lem7228152 term13 term13). Qed.
Lemma lem7228154 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228155 : term74 = term13.
Proof. exact (EQ_MP (@lem7228154) (@lem940073)). Qed.
Lemma lem7228156 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228157 : term72 = term44.
Proof. exact (MK_COMB (@lem7228156) (@lem7228155)). Qed.
Lemma lem7228158 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7228159 : term94 = term62.
Proof. exact (MK_COMB (@lem7228158) (@lem7228157)). Qed.
Lemma lem7228160 : term89 = term62.
Proof. exact (TRANS (@lem7228153) (@lem7228159)). Qed.
Lemma lem7228161 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7228162 : term116 = term104.
Proof. exact (MK_COMB (@lem7228161) (@lem7228160)). Qed.
Lemma lem7228163 : term117 = term106.
Proof. exact (MK_COMB (@lem7228162) (@lem7228150)). Qed.
Lemma lem7228165 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7228166 : term106 = term29.
Proof. exact (@lem7228165 term13). Qed.
Lemma lem7228167 : term117 = term29.
Proof. exact (TRANS (@lem7228163) (@lem7228166)). Qed.
Lemma lem7228168 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228169 : term119 = term120.
Proof. exact (MK_COMB (@lem7228168) (@lem7228167)). Qed.
Lemma lem7228170 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7228171 : term121 = term122.
Proof. exact (MK_COMB (@lem7228169) (@lem7228170)). Qed.
Lemma lem7228173 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7228174 : term122 = term29.
Proof. exact (@lem7228173 term13). Qed.
Lemma lem7228175 : term121 = term29.
Proof. exact (TRANS (@lem7228171) (@lem7228174)). Qed.
Lemma lem7228177 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228178 : term71 = term72.
Proof. exact (@lem7228177 term13 term13). Qed.
Lemma lem7228179 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228180 : term74 = term13.
Proof. exact (EQ_MP (@lem7228179) (@lem940073)). Qed.
Lemma lem7228181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228182 : term72 = term44.
Proof. exact (MK_COMB (@lem7228181) (@lem7228180)). Qed.
Lemma lem7228183 : term71 = term44.
Proof. exact (TRANS (@lem7228178) (@lem7228182)). Qed.
Lemma lem7228184 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7228185 : term124 = term122.
Proof. exact (MK_COMB (@lem7228184) (@lem7228183)). Qed.
Lemma lem7228187 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7228188 : term122 = term29.
Proof. exact (@lem7228187 term13). Qed.
Lemma lem7228189 : term124 = term29.
Proof. exact (TRANS (@lem7228185) (@lem7228188)). Qed.
Lemma lem7228190 : term29 = term124.
Proof. exact (SYM (@lem7228189)). Qed.
Lemma lem7228191 : term121 = term124.
Proof. exact (TRANS (@lem7228175) (@lem7228190)). Qed.
Lemma lem7228192 : term107 = term59.
Proof. exact (@lem7228142 (@lem7228191)). Qed.
Lemma lem7228193 : term106 = term59.
Proof. exact (TRANS (@lem7228108) (@lem7228192)). Qed.
Lemma lem7228195 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7228196 : term59 = term29.
Proof. exact (@lem7228195 term29). Qed.
Lemma lem7228197 : term106 = term29.
Proof. exact (TRANS (@lem7228193) (@lem7228196)). Qed.
Lemma lem7228198 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228199 : term125 = term120.
Proof. exact (MK_COMB (@lem7228198) (@lem7228197)). Qed.
Lemma lem7228200 (f : nat -> real) (g : nat -> real) : (term375 f g) = (term375 f g).
Proof. exact (eq_refl (term375 f g)). Qed.
Lemma lem7228201 (f : nat -> real) (g : nat -> real) : (term459 f g) = (term460 f g).
Proof. exact (MK_COMB (@lem7228199) (@lem7228200 f g)). Qed.
Lemma lem7228202 (f : nat -> real) (g : nat -> real) : (term458 f g) = (term460 f g).
Proof. exact (TRANS (@lem7228099 f g) (@lem7228201 f g)). Qed.
Lemma lem7228203 (f : nat -> real) (g : nat -> real) : (term460 f g) = term29.
Proof. exact (@lem1982719 (term375 f g)). Qed.
Lemma lem7228204 (f : nat -> real) (g : nat -> real) : (term458 f g) = term29.
Proof. exact (TRANS (@lem7228202 f g) (@lem7228203 f g)). Qed.
Lemma lem7228205 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7228206 (f : nat -> real) (g : nat -> real) : (term461 f g) = term128.
Proof. exact (MK_COMB (@lem7228205) (@lem7228204 f g)). Qed.
Lemma lem7228207 (f : nat -> real) (g : nat -> real) : (term462 f g) = (term463 f g).
Proof. exact (@lem1982715 term62 (term399 f g)). Qed.
Lemma lem7228209 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228210 : term44 = term88.
Proof. exact (@lem7228209 term13). Qed.
Lemma lem7228212 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7228213 : term62 = term63.
Proof. exact (@lem7228212 term13). Qed.
Lemma lem7228214 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7228215 : term104 = term105.
Proof. exact (MK_COMB (@lem7228214) (@lem7228213)). Qed.
Lemma lem7228216 : term106 = term107.
Proof. exact (MK_COMB (@lem7228215) (@lem7228210)). Qed.
Lemma lem7228217 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7228219 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228220 : term110 = term111.
Proof. exact (@lem7228219 (NUMERAL 0) term13). Qed.
Lemma lem7228221 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228222 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228223 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228222 h1) (fun h1 : term111 = True => @lem7228221)). Qed.
Lemma lem7228224 : term111 = True.
Proof. exact (EQ_MP (@lem7228223) (@lem7228221)). Qed.
Lemma lem7228225 : term110 = True.
Proof. exact (TRANS (@lem7228220) (@lem7228224)). Qed.
Lemma lem7228226 : True = term110.
Proof. exact (SYM (@lem7228225)). Qed.
Lemma lem7228227 : term110.
Proof. exact (EQ_MP (@lem7228226) (@lem0)). Qed.
Lemma lem7228228 : term113.
Proof. exact (@lem7228217 (@lem7228227)). Qed.
Lemma lem7228230 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228231 : term110 = term111.
Proof. exact (@lem7228230 (NUMERAL 0) term13). Qed.
Lemma lem7228232 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228233 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228234 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228233 h1) (fun h1 : term111 = True => @lem7228232)). Qed.
Lemma lem7228235 : term111 = True.
Proof. exact (EQ_MP (@lem7228234) (@lem7228232)). Qed.
Lemma lem7228236 : term110 = True.
Proof. exact (TRANS (@lem7228231) (@lem7228235)). Qed.
Lemma lem7228237 : True = term110.
Proof. exact (SYM (@lem7228236)). Qed.
Lemma lem7228238 : term110.
Proof. exact (EQ_MP (@lem7228237) (@lem0)). Qed.
Lemma lem7228239 : term114.
Proof. exact (@lem7228228 (@lem7228238)). Qed.
Lemma lem7228241 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228242 : term110 = term111.
Proof. exact (@lem7228241 (NUMERAL 0) term13). Qed.
Lemma lem7228243 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228244 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228245 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228244 h1) (fun h1 : term111 = True => @lem7228243)). Qed.
Lemma lem7228246 : term111 = True.
Proof. exact (EQ_MP (@lem7228245) (@lem7228243)). Qed.
Lemma lem7228247 : term110 = True.
Proof. exact (TRANS (@lem7228242) (@lem7228246)). Qed.
Lemma lem7228248 : True = term110.
Proof. exact (SYM (@lem7228247)). Qed.
Lemma lem7228249 : term110.
Proof. exact (EQ_MP (@lem7228248) (@lem0)). Qed.
Lemma lem7228250 : term115.
Proof. exact (@lem7228239 (@lem7228249)). Qed.
Lemma lem7228252 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228253 : term71 = term72.
Proof. exact (@lem7228252 term13 term13). Qed.
Lemma lem7228254 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228255 : term74 = term13.
Proof. exact (EQ_MP (@lem7228254) (@lem940073)). Qed.
Lemma lem7228256 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228257 : term72 = term44.
Proof. exact (MK_COMB (@lem7228256) (@lem7228255)). Qed.
Lemma lem7228258 : term71 = term44.
Proof. exact (TRANS (@lem7228253) (@lem7228257)). Qed.
Lemma lem7228260 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7228261 : term89 = term94.
Proof. exact (@lem7228260 term13 term13). Qed.
Lemma lem7228262 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228263 : term74 = term13.
Proof. exact (EQ_MP (@lem7228262) (@lem940073)). Qed.
Lemma lem7228264 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228265 : term72 = term44.
Proof. exact (MK_COMB (@lem7228264) (@lem7228263)). Qed.
Lemma lem7228266 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7228267 : term94 = term62.
Proof. exact (MK_COMB (@lem7228266) (@lem7228265)). Qed.
Lemma lem7228268 : term89 = term62.
Proof. exact (TRANS (@lem7228261) (@lem7228267)). Qed.
Lemma lem7228269 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7228270 : term116 = term104.
Proof. exact (MK_COMB (@lem7228269) (@lem7228268)). Qed.
Lemma lem7228271 : term117 = term106.
Proof. exact (MK_COMB (@lem7228270) (@lem7228258)). Qed.
Lemma lem7228273 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7228274 : term106 = term29.
Proof. exact (@lem7228273 term13). Qed.
Lemma lem7228275 : term117 = term29.
Proof. exact (TRANS (@lem7228271) (@lem7228274)). Qed.
Lemma lem7228276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228277 : term119 = term120.
Proof. exact (MK_COMB (@lem7228276) (@lem7228275)). Qed.
Lemma lem7228278 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7228279 : term121 = term122.
Proof. exact (MK_COMB (@lem7228277) (@lem7228278)). Qed.
Lemma lem7228281 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7228282 : term122 = term29.
Proof. exact (@lem7228281 term13). Qed.
Lemma lem7228283 : term121 = term29.
Proof. exact (TRANS (@lem7228279) (@lem7228282)). Qed.
Lemma lem7228285 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228286 : term71 = term72.
Proof. exact (@lem7228285 term13 term13). Qed.
Lemma lem7228287 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228288 : term74 = term13.
Proof. exact (EQ_MP (@lem7228287) (@lem940073)). Qed.
Lemma lem7228289 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228290 : term72 = term44.
Proof. exact (MK_COMB (@lem7228289) (@lem7228288)). Qed.
Lemma lem7228291 : term71 = term44.
Proof. exact (TRANS (@lem7228286) (@lem7228290)). Qed.
Lemma lem7228292 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7228293 : term124 = term122.
Proof. exact (MK_COMB (@lem7228292) (@lem7228291)). Qed.
Lemma lem7228295 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7228296 : term122 = term29.
Proof. exact (@lem7228295 term13). Qed.
Lemma lem7228297 : term124 = term29.
Proof. exact (TRANS (@lem7228293) (@lem7228296)). Qed.
Lemma lem7228298 : term29 = term124.
Proof. exact (SYM (@lem7228297)). Qed.
Lemma lem7228299 : term121 = term124.
Proof. exact (TRANS (@lem7228283) (@lem7228298)). Qed.
Lemma lem7228300 : term107 = term59.
Proof. exact (@lem7228250 (@lem7228299)). Qed.
Lemma lem7228301 : term106 = term59.
Proof. exact (TRANS (@lem7228216) (@lem7228300)). Qed.
Lemma lem7228303 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7228304 : term59 = term29.
Proof. exact (@lem7228303 term29). Qed.
Lemma lem7228305 : term106 = term29.
Proof. exact (TRANS (@lem7228301) (@lem7228304)). Qed.
Lemma lem7228306 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228307 : term125 = term120.
Proof. exact (MK_COMB (@lem7228306) (@lem7228305)). Qed.
Lemma lem7228308 (f : nat -> real) (g : nat -> real) : (term399 f g) = (term399 f g).
Proof. exact (eq_refl (term399 f g)). Qed.
Lemma lem7228309 (f : nat -> real) (g : nat -> real) : (term463 f g) = (term464 f g).
Proof. exact (MK_COMB (@lem7228307) (@lem7228308 f g)). Qed.
Lemma lem7228310 (f : nat -> real) (g : nat -> real) : (term462 f g) = (term464 f g).
Proof. exact (TRANS (@lem7228207 f g) (@lem7228309 f g)). Qed.
Lemma lem7228311 (f : nat -> real) (g : nat -> real) : (term464 f g) = term29.
Proof. exact (@lem1982719 (term399 f g)). Qed.
Lemma lem7228312 (f : nat -> real) (g : nat -> real) : (term462 f g) = term29.
Proof. exact (TRANS (@lem7228310 f g) (@lem7228311 f g)). Qed.
Lemma lem7228313 (f : nat -> real) (g : nat -> real) : (term457 f g) = term465.
Proof. exact (MK_COMB (@lem7228206 f g) (@lem7228312 f g)). Qed.
Lemma lem7228314 (f : nat -> real) (g : nat -> real) : (term456 f g) = term465.
Proof. exact (TRANS (@lem7228098 f g) (@lem7228313 f g)). Qed.
Lemma lem7228315 : term465 = term29.
Proof. exact (@lem1982721 term29). Qed.
Lemma lem7228316 (f : nat -> real) (g : nat -> real) : (term456 f g) = term29.
Proof. exact (TRANS (@lem7228314 f g) (@lem7228315)). Qed.
Lemma lem7228317 (f : nat -> real) (g : nat -> real) : (term446 f g) = term29.
Proof. exact (TRANS (@lem7228097 f g) (@lem7228316 f g)). Qed.
Lemma lem7228318 (f : nat -> real) (g : nat -> real) : (term445 f g) = term29.
Proof. exact (TRANS (@lem7228046 f g) (@lem7228317 f g)). Qed.
Lemma lem7228319 (g : nat -> real) (f : nat -> real) : (term444 g f) = term29.
Proof. exact (TRANS (@lem7228045 f g) (@lem7228318 f g)). Qed.
Lemma lem7228320 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7228321 (g : nat -> real) (f : nat -> real) : (term466 g f) = term467.
Proof. exact (MK_COMB (@lem7228320) (@lem7228319 g f)). Qed.
Lemma lem7228322 : term467 = term66.
Proof. exact (@lem1982785 term29). Qed.
Lemma lem7228324 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228325 : term29 = term59.
Proof. exact (@lem7228324 (NUMERAL 0)). Qed.
Lemma lem7228327 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7228328 : term62 = term63.
Proof. exact (@lem7228327 term13). Qed.
Lemma lem7228329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228330 : term64 = term65.
Proof. exact (MK_COMB (@lem7228329) (@lem7228328)). Qed.
Lemma lem7228331 : term66 = term67.
Proof. exact (MK_COMB (@lem7228330) (@lem7228325)). Qed.
Lemma lem7228332 : term67 = term68.
Proof. exact (@lem1981613 term62 term29 term44 term44). Qed.
Lemma lem7228334 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228335 : term71 = term72.
Proof. exact (@lem7228334 term13 term13). Qed.
Lemma lem7228336 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228337 : term74 = term13.
Proof. exact (EQ_MP (@lem7228336) (@lem940073)). Qed.
Lemma lem7228338 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228339 : term72 = term44.
Proof. exact (MK_COMB (@lem7228338) (@lem7228337)). Qed.
Lemma lem7228340 : term71 = term44.
Proof. exact (TRANS (@lem7228335) (@lem7228339)). Qed.
Lemma lem7228342 (x : nat) : (term75 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7228343 : term66 = term29.
Proof. exact (@lem7228342 term13). Qed.
Lemma lem7228344 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7228345 : term76 = term77.
Proof. exact (MK_COMB (@lem7228344) (@lem7228343)). Qed.
Lemma lem7228346 : term68 = term59.
Proof. exact (MK_COMB (@lem7228345) (@lem7228340)). Qed.
Lemma lem7228347 : term67 = term59.
Proof. exact (TRANS (@lem7228332) (@lem7228346)). Qed.
Lemma lem7228348 : term66 = term59.
Proof. exact (TRANS (@lem7228331) (@lem7228347)). Qed.
Lemma lem7228350 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7228351 : term59 = term29.
Proof. exact (@lem7228350 term29). Qed.
Lemma lem7228352 : term66 = term29.
Proof. exact (TRANS (@lem7228348) (@lem7228351)). Qed.
Lemma lem7228353 : term467 = term29.
Proof. exact (TRANS (@lem7228322) (@lem7228352)). Qed.
Lemma lem7228354 (g : nat -> real) (f : nat -> real) : (term468 g f) = (term468 g f).
Proof. exact (eq_refl (term468 g f)). Qed.
Lemma lem7228355 (g : nat -> real) (f : nat -> real) : ((term466 g f) = term467) = ((term466 g f) = term29).
Proof. exact (MK_COMB (@lem7228354 g f) (@lem7228353)). Qed.
Lemma lem7228356 (g : nat -> real) (f : nat -> real) : (term466 g f) = term29.
Proof. exact (EQ_MP (@lem7228355 g f) (@lem7228321 g f)). Qed.
Lemma lem7228357 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7228358 (g : nat -> real) (f : nat -> real) : (term469 g f) = term470.
Proof. exact (MK_COMB (@lem7228357) (@lem7228356 g f)). Qed.
Lemma lem7228359 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7228360 (g : nat -> real) (f : nat -> real) : (term471 g f) = term472.
Proof. exact (MK_COMB (@lem7228358 g f) (@lem7228359)). Qed.
Lemma lem7228361 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7228362 (g : nat -> real) (f : nat -> real) : (term473 g f) = term470.
Proof. exact (MK_COMB (@lem7228361) (@lem7228319 g f)). Qed.
Lemma lem7228363 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7228364 (g : nat -> real) (f : nat -> real) : (term474 g f) = term472.
Proof. exact (MK_COMB (@lem7228362 g f) (@lem7228363)). Qed.
Lemma lem7228365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7228366 (g : nat -> real) (f : nat -> real) : (term475 g f) = term476.
Proof. exact (MK_COMB (@lem7228365) (@lem7228364 g f)). Qed.
Lemma lem7228367 (g : nat -> real) (f : nat -> real) : (term386 g f) = term477.
Proof. exact (MK_COMB (@lem7228366 g f) (@lem7228360 g f)). Qed.
Lemma lem7228381 (g : nat -> real) (f : nat -> real) : (term385 g f) = term477.
Proof. exact (TRANS (@lem7227785 g f) (@lem7228367 g f)). Qed.
Lemma lem7228391 (h1 : term477) : term477.
Proof. exact (h1). Qed.
Lemma lem7228392 (h1 : term472) : term472.
Proof. exact (h1). Qed.
Lemma lem7228394 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7228395 : term472 = term478.
Proof. exact (@lem7228394 term29 term29). Qed.
Lemma lem7228397 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228398 : term29 = term59.
Proof. exact (@lem7228397 (NUMERAL 0)). Qed.
Lemma lem7228400 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228401 : term29 = term59.
Proof. exact (@lem7228400 (NUMERAL 0)). Qed.
Lemma lem7228402 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7228403 : term479 = term480.
Proof. exact (MK_COMB (@lem7228402) (@lem7228401)). Qed.
Lemma lem7228404 : term478 = term481.
Proof. exact (MK_COMB (@lem7228403) (@lem7228398)). Qed.
Lemma lem7228405 : term482.
Proof. exact (@lem1980255 term29 term44 term29 term44). Qed.
Lemma lem7228407 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228408 : term110 = term111.
Proof. exact (@lem7228407 (NUMERAL 0) term13). Qed.
Lemma lem7228409 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228410 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228411 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228410 h1) (fun h1 : term111 = True => @lem7228409)). Qed.
Lemma lem7228412 : term111 = True.
Proof. exact (EQ_MP (@lem7228411) (@lem7228409)). Qed.
Lemma lem7228413 : term110 = True.
Proof. exact (TRANS (@lem7228408) (@lem7228412)). Qed.
Lemma lem7228414 : True = term110.
Proof. exact (SYM (@lem7228413)). Qed.
Lemma lem7228415 : term110.
Proof. exact (EQ_MP (@lem7228414) (@lem0)). Qed.
Lemma lem7228416 : term483.
Proof. exact (@lem7228405 (@lem7228415)). Qed.
Lemma lem7228418 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228419 : term110 = term111.
Proof. exact (@lem7228418 (NUMERAL 0) term13). Qed.
Lemma lem7228420 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228421 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228422 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228421 h1) (fun h1 : term111 = True => @lem7228420)). Qed.
Lemma lem7228423 : term111 = True.
Proof. exact (EQ_MP (@lem7228422) (@lem7228420)). Qed.
Lemma lem7228424 : term110 = True.
Proof. exact (TRANS (@lem7228419) (@lem7228423)). Qed.
Lemma lem7228425 : True = term110.
Proof. exact (SYM (@lem7228424)). Qed.
Lemma lem7228426 : term110.
Proof. exact (EQ_MP (@lem7228425) (@lem0)). Qed.
Lemma lem7228427 : term481 = term484.
Proof. exact (@lem7228416 (@lem7228426)). Qed.
Lemma lem7228429 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7228430 : term122 = term29.
Proof. exact (@lem7228429 term13). Qed.
Lemma lem7228432 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7228433 : term122 = term29.
Proof. exact (@lem7228432 term13). Qed.
Lemma lem7228434 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7228435 : term485 = term479.
Proof. exact (MK_COMB (@lem7228434) (@lem7228433)). Qed.
Lemma lem7228436 : term484 = term478.
Proof. exact (MK_COMB (@lem7228435) (@lem7228430)). Qed.
Lemma lem7228438 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228439 : term478 = term486.
Proof. exact (@lem7228438 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7228440 : term486 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7228441 : term478 = False.
Proof. exact (TRANS (@lem7228439) (@lem7228440)). Qed.
Lemma lem7228442 : term484 = False.
Proof. exact (TRANS (@lem7228436) (@lem7228441)). Qed.
Lemma lem7228443 : term481 = False.
Proof. exact (TRANS (@lem7228427) (@lem7228442)). Qed.
Lemma lem7228444 : term478 = False.
Proof. exact (TRANS (@lem7228404) (@lem7228443)). Qed.
Lemma lem7228445 : term472 = False.
Proof. exact (TRANS (@lem7228395) (@lem7228444)). Qed.
Lemma lem7228446 (h1 : term472) : False.
Proof. exact (EQ_MP (@lem7228445) (@lem7228392 h1)). Qed.
Lemma lem7228447 (h1 : term472) : term472.
Proof. exact (h1). Qed.
Lemma lem7228449 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7228450 : term472 = term478.
Proof. exact (@lem7228449 term29 term29). Qed.
Lemma lem7228452 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228453 : term29 = term59.
Proof. exact (@lem7228452 (NUMERAL 0)). Qed.
Lemma lem7228455 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228456 : term29 = term59.
Proof. exact (@lem7228455 (NUMERAL 0)). Qed.
Lemma lem7228457 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7228458 : term479 = term480.
Proof. exact (MK_COMB (@lem7228457) (@lem7228456)). Qed.
Lemma lem7228459 : term478 = term481.
Proof. exact (MK_COMB (@lem7228458) (@lem7228453)). Qed.
Lemma lem7228460 : term482.
Proof. exact (@lem1980255 term29 term44 term29 term44). Qed.
Lemma lem7228462 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228463 : term110 = term111.
Proof. exact (@lem7228462 (NUMERAL 0) term13). Qed.
Lemma lem7228464 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228465 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228466 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228465 h1) (fun h1 : term111 = True => @lem7228464)). Qed.
Lemma lem7228467 : term111 = True.
Proof. exact (EQ_MP (@lem7228466) (@lem7228464)). Qed.
Lemma lem7228468 : term110 = True.
Proof. exact (TRANS (@lem7228463) (@lem7228467)). Qed.
Lemma lem7228469 : True = term110.
Proof. exact (SYM (@lem7228468)). Qed.
Lemma lem7228470 : term110.
Proof. exact (EQ_MP (@lem7228469) (@lem0)). Qed.
Lemma lem7228471 : term483.
Proof. exact (@lem7228460 (@lem7228470)). Qed.
Lemma lem7228473 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228474 : term110 = term111.
Proof. exact (@lem7228473 (NUMERAL 0) term13). Qed.
Lemma lem7228475 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7228476 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7228477 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7228476 h1) (fun h1 : term111 = True => @lem7228475)). Qed.
Lemma lem7228478 : term111 = True.
Proof. exact (EQ_MP (@lem7228477) (@lem7228475)). Qed.
Lemma lem7228479 : term110 = True.
Proof. exact (TRANS (@lem7228474) (@lem7228478)). Qed.
Lemma lem7228480 : True = term110.
Proof. exact (SYM (@lem7228479)). Qed.
Lemma lem7228481 : term110.
Proof. exact (EQ_MP (@lem7228480) (@lem0)). Qed.
Lemma lem7228482 : term481 = term484.
Proof. exact (@lem7228471 (@lem7228481)). Qed.
Lemma lem7228484 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7228485 : term122 = term29.
Proof. exact (@lem7228484 term13). Qed.
Lemma lem7228487 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7228488 : term122 = term29.
Proof. exact (@lem7228487 term13). Qed.
Lemma lem7228489 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7228490 : term485 = term479.
Proof. exact (MK_COMB (@lem7228489) (@lem7228488)). Qed.
Lemma lem7228491 : term484 = term478.
Proof. exact (MK_COMB (@lem7228490) (@lem7228485)). Qed.
Lemma lem7228493 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7228494 : term478 = term486.
Proof. exact (@lem7228493 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7228495 : term486 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7228496 : term478 = False.
Proof. exact (TRANS (@lem7228494) (@lem7228495)). Qed.
Lemma lem7228497 : term484 = False.
Proof. exact (TRANS (@lem7228491) (@lem7228496)). Qed.
Lemma lem7228498 : term481 = False.
Proof. exact (TRANS (@lem7228482) (@lem7228497)). Qed.
Lemma lem7228499 : term478 = False.
Proof. exact (TRANS (@lem7228459) (@lem7228498)). Qed.
Lemma lem7228500 : term472 = False.
Proof. exact (TRANS (@lem7228450) (@lem7228499)). Qed.
Lemma lem7228501 (h1 : term472) : False.
Proof. exact (EQ_MP (@lem7228500) (@lem7228447 h1)). Qed.
Lemma lem7228502 (h1 : term477) : False.
Proof. exact (or_elim (@lem7228391 h1) (fun h0 : term472 => @lem7228446 h0) (fun h0 : term472 => @lem7228501 h0)). Qed.
Lemma lem7228504 (h1 : term477) : term477.
Proof. exact (h1). Qed.
Lemma lem7228505 (h1 : term477) : term477 = False.
Proof. exact (prop_ext (fun h2 : term477 => @lem7228502 h1) (fun h2 : False => @lem7228504 h1)). Qed.
Lemma lem7228506 (h1 : term477) : False.
Proof. exact (EQ_MP (@lem7228505 h1) (@lem7228504 h1)). Qed.
Lemma lem7228507 (g : nat -> real) (f : nat -> real) (h1 : term385 g f) : term385 g f.
Proof. exact (h1). Qed.
Lemma lem7228508 (g : nat -> real) (f : nat -> real) (h1 : term385 g f) : term477.
Proof. exact (EQ_MP (@lem7228381 g f) (@lem7228507 g f h1)). Qed.
Lemma lem7228509 (g : nat -> real) (f : nat -> real) (h1 : term385 g f) : term477 = False.
Proof. exact (prop_ext (fun h2 : term477 => @lem7228506 h2) (fun h2 : False => @lem7228508 g f h1)). Qed.
Lemma lem7228510 (g : nat -> real) (f : nat -> real) (h1 : term385 g f) : False.
Proof. exact (EQ_MP (@lem7228509 g f h1) (@lem7228508 g f h1)). Qed.
Lemma lem7228511 (g : nat -> real) (f : nat -> real) : term487 g f.
Proof. exact (fun h0 : term385 g f => @lem7228510 g f h0). Qed.
Lemma lem7228512 (g : nat -> real) (f : nat -> real) : term488 g f.
Proof. exact (@lem1386578 ((term280 f g) = (term381 g f))). Qed.
Lemma lem7228515 (g : nat -> real) (f : nat -> real) : (term280 f g) = (term381 g f).
Proof. exact (@lem7228512 g f (@lem7228511 g f)). Qed.
Lemma lem7228518 : term489 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem7228519 : (term489 = (BIT1 0)) = (term490 = term13).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228520 : term490 = term13.
Proof. exact (EQ_MP (@lem7228519) (@lem7228518)). Qed.
Lemma lem7228521 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7228522 (f : nat -> real) : (term389 f) = (term491 f).
Proof. exact (MK_COMB (@lem7228521 f) (@lem7228520)). Qed.
Lemma lem7228523 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228524 (f : nat -> real) : (term392 f) = (term492 f).
Proof. exact (MK_COMB (@lem7228523) (@lem7228522 f)). Qed.
Lemma lem7228525 : term489 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem7228526 : (term489 = (BIT1 0)) = (term490 = term13).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228527 : term490 = term13.
Proof. exact (EQ_MP (@lem7228526) (@lem7228525)). Qed.
Lemma lem7228528 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7228529 (g : nat -> real) : (term389 g) = (term491 g).
Proof. exact (MK_COMB (@lem7228528 g) (@lem7228527)). Qed.
Lemma lem7228530 (f : nat -> real) (g : nat -> real) : (term395 f g) = (term493 f g).
Proof. exact (MK_COMB (@lem7228524 f) (@lem7228529 g)). Qed.
Lemma lem7228531 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7228532 (f : nat -> real) (g : nat -> real) : (term376 f g) = (term494 f g).
Proof. exact (MK_COMB (@lem7228531) (@lem7228530 f g)). Qed.
Lemma lem7228533 (f : nat -> real) (g : nat -> real) (m : nat) : (term374 f g m) = (term374 f g m).
Proof. exact (eq_refl (term374 f g m)). Qed.
Lemma lem7228534 (f : nat -> real) (g : nat -> real) (m : nat) : (term377 f g m) = (term495 f g m).
Proof. exact (MK_COMB (@lem7228532 f g) (@lem7228533 f g m)). Qed.
Lemma lem7228535 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7228536 (f : nat -> real) (g : nat -> real) (m : nat) : (term300 f g m) = (term496 f g m).
Proof. exact (MK_COMB (@lem7228535) (@lem7228534 f g m)). Qed.
Lemma lem7228537 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7228538 (f : nat -> real) (g : nat -> real) (m : nat) : (term384 f g m) = (term497 f g m).
Proof. exact (MK_COMB (@lem7228536 f g m) (@lem7228537)). Qed.
Lemma lem7228539 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem7228540 (f : nat -> real) (g : nat -> real) (m : nat) : (term29 = (term384 f g m)) = (term29 = (term497 f g m)).
Proof. exact (MK_COMB (@lem7228539) (@lem7228538 f g m)). Qed.
Lemma lem7228543 (m : nat) : (term345 m) = (term345 m).
Proof. exact (eq_refl (term345 m)). Qed.
Lemma lem7228544 (f : nat -> real) (g : nat -> real) (m : nat) : (term498 f g m) = (term499 f g m).
Proof. exact (MK_COMB (@lem7228543 m) (@lem7228540 f g m)). Qed.
Lemma lem7228547 (m : nat) : (term218 m) = (term218 m).
Proof. exact (eq_refl (term218 m)). Qed.
Lemma lem7228562 (f : nat -> real) (g : nat -> real) (m : nat) : (term500 f g m) = (term501 f g m).
Proof. exact (MK_COMB (@lem7228547 m) (@lem7228544 f g m)). Qed.
Lemma lem7228566 (m : nat) : (term502 m) = (m = (NUMERAL 0)).
Proof. exact (@lem16933 (m = (NUMERAL 0))). Qed.
Lemma lem7228567 (f : nat -> real) (g : nat -> real) (m : nat) : (term29 = (term497 f g m)) = (term29 = (term497 f g m)).
Proof. exact (eq_refl (term29 = (term497 f g m))). Qed.
Lemma lem7228568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7228569 (m : nat) : (term503 m) = (term504 m).
Proof. exact (MK_COMB (@lem7228568) (@lem7228566 m)). Qed.
Lemma lem7228570 (f : nat -> real) (g : nat -> real) (m : nat) : (term505 f g m) = (term506 f g m).
Proof. exact (MK_COMB (@lem7228569 m) (@lem7228567 f g m)). Qed.
Lemma lem7228571 (f : nat -> real) (g : nat -> real) (m : nat) : (term499 f g m) = (term505 f g m).
Proof. exact (@lem17265 (term363 m) (term29 = (term497 f g m))). Qed.
Lemma lem7228572 (f : nat -> real) (g : nat -> real) (m : nat) : (term499 f g m) = (term506 f g m).
Proof. exact (TRANS (@lem7228571 f g m) (@lem7228570 f g m)). Qed.
Lemma lem7228574 (m : nat) : (term507 m) = (term507 m).
Proof. exact (eq_refl (term507 m)). Qed.
Lemma lem7228575 (f : nat -> real) (g : nat -> real) (m : nat) : (term508 f g m) = (term509 f g m).
Proof. exact (MK_COMB (@lem7228574 m) (@lem7228572 f g m)). Qed.
Lemma lem7228576 (f : nat -> real) (g : nat -> real) (m : nat) : (term501 f g m) = (term508 f g m).
Proof. exact (@lem17265 (term212 m) (term499 f g m)). Qed.
Lemma lem7228577 (f : nat -> real) (g : nat -> real) (m : nat) : (term501 f g m) = (term509 f g m).
Proof. exact (TRANS (@lem7228576 f g m) (@lem7228575 f g m)). Qed.
Lemma lem7228620 (f : nat -> real) (g : nat -> real) (m : nat) : (term500 f g m) = (term509 f g m).
Proof. exact (TRANS (@lem7228562 f g m) (@lem7228577 f g m)). Qed.
Lemma lem7228622 (m : nat) (n : nat) : (Peano.le m n) = (term510 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7228623 (m : nat) : (term212 m) = (term511 m).
Proof. exact (@lem7228622 m (NUMERAL 0)). Qed.
Lemma lem7228624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7228625 (m : nat) : (term226 m) = (term512 m).
Proof. exact (MK_COMB (@lem7228624) (@lem7228623 m)). Qed.
Lemma lem7228626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7228627 (m : nat) : (term507 m) = (term513 m).
Proof. exact (MK_COMB (@lem7228626) (@lem7228625 m)). Qed.
Lemma lem7228629 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7228630 (m : nat) : (m = (NUMERAL 0)) = ((int_of_num m) = term26).
Proof. exact (@lem7228629 m (NUMERAL 0)). Qed.
Lemma lem7228633 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7228634 (m : nat) : (term504 m) = (term514 m).
Proof. exact (MK_COMB (@lem7228633) (@lem7228630 m)). Qed.
Lemma lem7228637 (f : nat -> real) (g : nat -> real) (m : nat) : (term29 = (term497 f g m)) = (term29 = (term497 f g m)).
Proof. exact (eq_refl (term29 = (term497 f g m))). Qed.
Lemma lem7228638 (f : nat -> real) (g : nat -> real) (m : nat) : (term506 f g m) = (term515 f g m).
Proof. exact (MK_COMB (@lem7228634 m) (@lem7228637 f g m)). Qed.
Lemma lem7228639 (f : nat -> real) (g : nat -> real) (m : nat) : (term509 f g m) = (term516 f g m).
Proof. exact (MK_COMB (@lem7228627 m) (@lem7228638 f g m)). Qed.
Lemma lem7228640 (f : nat -> real) (g : nat -> real) (m : nat) : (term500 f g m) = (term516 f g m).
Proof. exact (TRANS (@lem7228620 f g m) (@lem7228639 f g m)). Qed.
Lemma lem7228641 (m : nat) : term16 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem7228642 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem7228643 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem7228642 m) (@lem7228641 m)). Qed.
Lemma lem7228644 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term517 _96871 f g m) = (term518 _96871 f g m).
Proof. exact (@lem2318604 (term518 _96871 f g m)). Qed.
Lemma lem7228659 (_96871 : int) : (term519 _96871) = (term520 _96871).
Proof. exact (@lem16933 (term520 _96871)). Qed.
Lemma lem7228666 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term521 _96871 f g m) = (term522 _96871 f g m).
Proof. exact (@lem17160 (_96871 = term26) (term29 = (term497 f g m))). Qed.
Lemma lem7228667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7228668 (_96871 : int) : (term523 _96871) = (term524 _96871).
Proof. exact (MK_COMB (@lem7228667) (@lem7228659 _96871)). Qed.
Lemma lem7228669 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term525 _96871 f g m) = (term526 _96871 f g m).
Proof. exact (MK_COMB (@lem7228668 _96871) (@lem7228666 _96871 f g m)). Qed.
Lemma lem7228670 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term527 _96871 f g m) = (term525 _96871 f g m).
Proof. exact (@lem17160 (term528 _96871) (term529 _96871 f g m)). Qed.
Lemma lem7228671 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term527 _96871 f g m) = (term526 _96871 f g m).
Proof. exact (TRANS (@lem7228670 _96871 f g m) (@lem7228669 _96871 f g m)). Qed.
Lemma lem7228673 (_96871 : int) : (term50 _96871) = (term50 _96871).
Proof. exact (eq_refl (term50 _96871)). Qed.
Lemma lem7228674 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term530 _96871 f g m) = (term531 _96871 f g m).
Proof. exact (MK_COMB (@lem7228673 _96871) (@lem7228671 _96871 f g m)). Qed.
Lemma lem7228675 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term532 _96871 f g m) = (term530 _96871 f g m).
Proof. exact (@lem17362 (term22 _96871) (term533 _96871 f g m)). Qed.
Lemma lem7228695 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term532 _96871 f g m) = (term531 _96871 f g m).
Proof. exact (TRANS (@lem7228675 _96871 f g m) (@lem7228674 _96871 f g m)). Qed.
Lemma lem7228698 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7228699 (_96871 : int) : (term22 _96871) = (term25 _96871).
Proof. exact (@lem7228698 term26 _96871). Qed.
Lemma lem7228701 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7228702 : term28 = term29.
Proof. exact (@lem7228701 (NUMERAL 0)). Qed.
Lemma lem7228703 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7228704 : term30 = term31.
Proof. exact (MK_COMB (@lem7228703) (@lem7228702)). Qed.
Lemma lem7228705 (_96871 : int) : (real_of_int _96871) = (real_of_int _96871).
Proof. exact (eq_refl (real_of_int _96871)). Qed.
Lemma lem7228706 (_96871 : int) : (term25 _96871) = (term32 _96871).
Proof. exact (MK_COMB (@lem7228704) (@lem7228705 _96871)). Qed.
Lemma lem7228708 (_96871 : int) : (term22 _96871) = (term32 _96871).
Proof. exact (TRANS (@lem7228699 _96871) (@lem7228706 _96871)). Qed.
Lemma lem7228711 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7228712 (_96871 : int) : (term520 _96871) = (term534 _96871).
Proof. exact (@lem7228711 _96871 term26). Qed.
Lemma lem7228714 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7228715 : term28 = term29.
Proof. exact (@lem7228714 (NUMERAL 0)). Qed.
Lemma lem7228716 (_96871 : int) : (term535 _96871) = (term535 _96871).
Proof. exact (eq_refl (term535 _96871)). Qed.
Lemma lem7228717 (_96871 : int) : (term534 _96871) = (term536 _96871).
Proof. exact (MK_COMB (@lem7228716 _96871) (@lem7228715)). Qed.
Lemma lem7228719 (_96871 : int) : (term520 _96871) = (term536 _96871).
Proof. exact (TRANS (@lem7228712 _96871) (@lem7228717 _96871)). Qed.
Lemma lem7228721 (y : int) (x : int) : (term537 x y) = (term538 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem7228722 (_96871 : int) : (term539 _96871) = (term540 _96871).
Proof. exact (@lem7228721 term26 _96871). Qed.
Lemma lem7228724 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7228725 (_96871 : int) : (term541 _96871) = (term542 _96871).
Proof. exact (@lem7228724 (term36 _96871) term26). Qed.
Lemma lem7228727 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7228728 (_96871 : int) : (term40 _96871) = (term41 _96871).
Proof. exact (@lem7228727 _96871 term42). Qed.
Lemma lem7228730 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7228731 : term43 = term44.
Proof. exact (@lem7228730 term13). Qed.
Lemma lem7228732 (_96871 : int) : (term45 _96871) = (term45 _96871).
Proof. exact (eq_refl (term45 _96871)). Qed.
Lemma lem7228733 (_96871 : int) : (term41 _96871) = (term46 _96871).
Proof. exact (MK_COMB (@lem7228732 _96871) (@lem7228731)). Qed.
Lemma lem7228734 (_96871 : int) : (term40 _96871) = (term46 _96871).
Proof. exact (TRANS (@lem7228728 _96871) (@lem7228733 _96871)). Qed.
Lemma lem7228735 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7228736 (_96871 : int) : (term47 _96871) = (term48 _96871).
Proof. exact (MK_COMB (@lem7228735) (@lem7228734 _96871)). Qed.
Lemma lem7228738 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7228739 : term28 = term29.
Proof. exact (@lem7228738 (NUMERAL 0)). Qed.
Lemma lem7228740 (_96871 : int) : (term542 _96871) = (term543 _96871).
Proof. exact (MK_COMB (@lem7228736 _96871) (@lem7228739)). Qed.
Lemma lem7228741 (_96871 : int) : (term541 _96871) = (term543 _96871).
Proof. exact (TRANS (@lem7228725 _96871) (@lem7228740 _96871)). Qed.
Lemma lem7228742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7228743 (_96871 : int) : (term544 _96871) = (term545 _96871).
Proof. exact (MK_COMB (@lem7228742) (@lem7228741 _96871)). Qed.
Lemma lem7228745 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7228746 (_96871 : int) : (term546 _96871) = (term547 _96871).
Proof. exact (@lem7228745 term548 _96871). Qed.
Lemma lem7228748 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7228749 : term549 = term550.
Proof. exact (@lem7228748 term26 term42). Qed.
Lemma lem7228751 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7228752 : term28 = term29.
Proof. exact (@lem7228751 (NUMERAL 0)). Qed.
Lemma lem7228753 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7228754 : term551 = term128.
Proof. exact (MK_COMB (@lem7228753) (@lem7228752)). Qed.
Lemma lem7228756 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7228757 : term43 = term44.
Proof. exact (@lem7228756 term13). Qed.
Lemma lem7228758 : term550 = term552.
Proof. exact (MK_COMB (@lem7228754) (@lem7228757)). Qed.
Lemma lem7228759 : term549 = term552.
Proof. exact (TRANS (@lem7228749) (@lem7228758)). Qed.
Lemma lem7228760 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7228761 : term553 = term554.
Proof. exact (MK_COMB (@lem7228760) (@lem7228759)). Qed.
Lemma lem7228762 (_96871 : int) : (real_of_int _96871) = (real_of_int _96871).
Proof. exact (eq_refl (real_of_int _96871)). Qed.
Lemma lem7228763 (_96871 : int) : (term547 _96871) = (term555 _96871).
Proof. exact (MK_COMB (@lem7228761) (@lem7228762 _96871)). Qed.
Lemma lem7228764 (_96871 : int) : (term546 _96871) = (term555 _96871).
Proof. exact (TRANS (@lem7228746 _96871) (@lem7228763 _96871)). Qed.
Lemma lem7228765 (_96871 : int) : (term540 _96871) = (term556 _96871).
Proof. exact (MK_COMB (@lem7228743 _96871) (@lem7228764 _96871)). Qed.
Lemma lem7228766 (_96871 : int) : (term539 _96871) = (term556 _96871).
Proof. exact (TRANS (@lem7228722 _96871) (@lem7228765 _96871)). Qed.
Lemma lem7228773 (f : nat -> real) (g : nat -> real) (m : nat) : (term557 f g m) = (term557 f g m).
Proof. exact (eq_refl (term557 f g m)). Qed.
Lemma lem7228774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7228775 (_96871 : int) : (term558 _96871) = (term559 _96871).
Proof. exact (MK_COMB (@lem7228774) (@lem7228766 _96871)). Qed.
Lemma lem7228776 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term522 _96871 f g m) = (term560 _96871 f g m).
Proof. exact (MK_COMB (@lem7228775 _96871) (@lem7228773 f g m)). Qed.
Lemma lem7228777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7228778 (_96871 : int) : (term524 _96871) = (term561 _96871).
Proof. exact (MK_COMB (@lem7228777) (@lem7228719 _96871)). Qed.
Lemma lem7228779 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term526 _96871 f g m) = (term562 _96871 f g m).
Proof. exact (MK_COMB (@lem7228778 _96871) (@lem7228776 _96871 f g m)). Qed.
Lemma lem7228780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7228781 (_96871 : int) : (term50 _96871) = (term51 _96871).
Proof. exact (MK_COMB (@lem7228780) (@lem7228708 _96871)). Qed.
Lemma lem7228782 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term531 _96871 f g m) = (term563 _96871 f g m).
Proof. exact (MK_COMB (@lem7228781 _96871) (@lem7228779 _96871 f g m)). Qed.
Lemma lem7228783 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term532 _96871 f g m) = (term563 _96871 f g m).
Proof. exact (TRANS (@lem7228695 _96871 f g m) (@lem7228782 _96871 f g m)). Qed.
Lemma lem7228787 (t : Prop) : (term53 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7228835 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term564 _96871 f g m) = (term563 _96871 f g m).
Proof. exact (@lem7228787 (term563 _96871 f g m)). Qed.
Lemma lem7228836 (_96871 : int) : (term32 _96871) = (term55 _96871).
Proof. exact (@lem1988287 (real_of_int _96871) term29). Qed.
Lemma lem7228842 (_96871 : int) : (term56 _96871) = (term57 _96871).
Proof. exact (@lem1982792 (real_of_int _96871) term29). Qed.
Lemma lem7228844 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228845 : term29 = term59.
Proof. exact (@lem7228844 (NUMERAL 0)). Qed.
Lemma lem7228847 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7228848 : term62 = term63.
Proof. exact (@lem7228847 term13). Qed.
Lemma lem7228849 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228850 : term64 = term65.
Proof. exact (MK_COMB (@lem7228849) (@lem7228848)). Qed.
Lemma lem7228851 : term66 = term67.
Proof. exact (MK_COMB (@lem7228850) (@lem7228845)). Qed.
Lemma lem7228852 : term67 = term68.
Proof. exact (@lem1981613 term62 term29 term44 term44). Qed.
Lemma lem7228854 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228855 : term71 = term72.
Proof. exact (@lem7228854 term13 term13). Qed.
Lemma lem7228856 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228857 : term74 = term13.
Proof. exact (EQ_MP (@lem7228856) (@lem940073)). Qed.
Lemma lem7228858 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228859 : term72 = term44.
Proof. exact (MK_COMB (@lem7228858) (@lem7228857)). Qed.
Lemma lem7228860 : term71 = term44.
Proof. exact (TRANS (@lem7228855) (@lem7228859)). Qed.
Lemma lem7228862 (x : nat) : (term75 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7228863 : term66 = term29.
Proof. exact (@lem7228862 term13). Qed.
Lemma lem7228864 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7228865 : term76 = term77.
Proof. exact (MK_COMB (@lem7228864) (@lem7228863)). Qed.
Lemma lem7228866 : term68 = term59.
Proof. exact (MK_COMB (@lem7228865) (@lem7228860)). Qed.
Lemma lem7228867 : term67 = term59.
Proof. exact (TRANS (@lem7228852) (@lem7228866)). Qed.
Lemma lem7228868 : term66 = term59.
Proof. exact (TRANS (@lem7228851) (@lem7228867)). Qed.
Lemma lem7228870 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7228871 : term59 = term29.
Proof. exact (@lem7228870 term29). Qed.
Lemma lem7228872 : term66 = term29.
Proof. exact (TRANS (@lem7228868) (@lem7228871)). Qed.
Lemma lem7228873 (_96871 : int) : (term45 _96871) = (term45 _96871).
Proof. exact (eq_refl (term45 _96871)). Qed.
Lemma lem7228874 (_96871 : int) : (term57 _96871) = (term79 _96871).
Proof. exact (MK_COMB (@lem7228873 _96871) (@lem7228872)). Qed.
Lemma lem7228875 (_96871 : int) : (term79 _96871) = (real_of_int _96871).
Proof. exact (@lem1982723 (real_of_int _96871)). Qed.
Lemma lem7228876 (_96871 : int) : (term57 _96871) = (real_of_int _96871).
Proof. exact (TRANS (@lem7228874 _96871) (@lem7228875 _96871)). Qed.
Lemma lem7228878 (_96871 : int) : (term56 _96871) = (real_of_int _96871).
Proof. exact (TRANS (@lem7228842 _96871) (@lem7228876 _96871)). Qed.
Lemma lem7228879 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7228880 (_96871 : int) : (term80 _96871) = (term81 _96871).
Proof. exact (MK_COMB (@lem7228879) (@lem7228878 _96871)). Qed.
Lemma lem7228881 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7228882 (_96871 : int) : (term55 _96871) = (term82 _96871).
Proof. exact (MK_COMB (@lem7228880 _96871) (@lem7228881)). Qed.
Lemma lem7228883 (_96871 : int) : (term32 _96871) = (term82 _96871).
Proof. exact (TRANS (@lem7228836 _96871) (@lem7228882 _96871)). Qed.
Lemma lem7228884 (_96871 : int) : (term536 _96871) = (term565 _96871).
Proof. exact (@lem1988287 term29 (real_of_int _96871)). Qed.
Lemma lem7228890 (_96871 : int) : (term566 _96871) = (term567 _96871).
Proof. exact (@lem1982792 term29 (real_of_int _96871)). Qed.
Lemma lem7228895 (_96871 : int) : (term567 _96871) = (term101 _96871).
Proof. exact (@lem1982721 (term101 _96871)). Qed.
Lemma lem7228897 (_96871 : int) : (term566 _96871) = (term101 _96871).
Proof. exact (TRANS (@lem7228890 _96871) (@lem7228895 _96871)). Qed.
Lemma lem7228898 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7228899 (_96871 : int) : (term568 _96871) = (term569 _96871).
Proof. exact (MK_COMB (@lem7228898) (@lem7228897 _96871)). Qed.
Lemma lem7228900 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7228901 (_96871 : int) : (term565 _96871) = (term570 _96871).
Proof. exact (MK_COMB (@lem7228899 _96871) (@lem7228900)). Qed.
Lemma lem7228902 (_96871 : int) : (term536 _96871) = (term570 _96871).
Proof. exact (TRANS (@lem7228884 _96871) (@lem7228901 _96871)). Qed.
Lemma lem7228903 (_96871 : int) : (term543 _96871) = (term571 _96871).
Proof. exact (@lem1988287 term29 (term46 _96871)). Qed.
Lemma lem7228915 (_96871 : int) : (term572 _96871) = (term573 _96871).
Proof. exact (@lem1982792 term29 (term46 _96871)). Qed.
Lemma lem7228916 (_96871 : int) : (term86 _96871) = (term87 _96871).
Proof. exact (@lem1982781 (real_of_int _96871) term62 term44). Qed.
Lemma lem7228918 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228919 : term44 = term88.
Proof. exact (@lem7228918 term13). Qed.
Lemma lem7228921 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7228922 : term62 = term63.
Proof. exact (@lem7228921 term13). Qed.
Lemma lem7228923 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228924 : term64 = term65.
Proof. exact (MK_COMB (@lem7228923) (@lem7228922)). Qed.
Lemma lem7228925 : term89 = term90.
Proof. exact (MK_COMB (@lem7228924) (@lem7228919)). Qed.
Lemma lem7228926 : term90 = term91.
Proof. exact (@lem1981613 term62 term44 term44 term44). Qed.
Lemma lem7228928 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228929 : term71 = term72.
Proof. exact (@lem7228928 term13 term13). Qed.
Lemma lem7228930 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228931 : term74 = term13.
Proof. exact (EQ_MP (@lem7228930) (@lem940073)). Qed.
Lemma lem7228932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228933 : term72 = term44.
Proof. exact (MK_COMB (@lem7228932) (@lem7228931)). Qed.
Lemma lem7228934 : term71 = term44.
Proof. exact (TRANS (@lem7228929) (@lem7228933)). Qed.
Lemma lem7228936 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7228937 : term89 = term94.
Proof. exact (@lem7228936 term13 term13). Qed.
Lemma lem7228938 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228939 : term74 = term13.
Proof. exact (EQ_MP (@lem7228938) (@lem940073)). Qed.
Lemma lem7228940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228941 : term72 = term44.
Proof. exact (MK_COMB (@lem7228940) (@lem7228939)). Qed.
Lemma lem7228942 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7228943 : term94 = term62.
Proof. exact (MK_COMB (@lem7228942) (@lem7228941)). Qed.
Lemma lem7228944 : term89 = term62.
Proof. exact (TRANS (@lem7228937) (@lem7228943)). Qed.
Lemma lem7228945 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7228946 : term95 = term96.
Proof. exact (MK_COMB (@lem7228945) (@lem7228944)). Qed.
Lemma lem7228947 : term91 = term63.
Proof. exact (MK_COMB (@lem7228946) (@lem7228934)). Qed.
Lemma lem7228948 : term90 = term63.
Proof. exact (TRANS (@lem7228926) (@lem7228947)). Qed.
Lemma lem7228949 : term89 = term63.
Proof. exact (TRANS (@lem7228925) (@lem7228948)). Qed.
Lemma lem7228951 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7228952 : term63 = term62.
Proof. exact (@lem7228951 term62). Qed.
Lemma lem7228953 : term89 = term62.
Proof. exact (TRANS (@lem7228949) (@lem7228952)). Qed.
Lemma lem7228956 (_96871 : int) : (term97 _96871) = (term97 _96871).
Proof. exact (eq_refl (term97 _96871)). Qed.
Lemma lem7228957 (_96871 : int) : (term87 _96871) = (term98 _96871).
Proof. exact (MK_COMB (@lem7228956 _96871) (@lem7228953)). Qed.
Lemma lem7228958 (_96871 : int) : (term86 _96871) = (term98 _96871).
Proof. exact (TRANS (@lem7228916 _96871) (@lem7228957 _96871)). Qed.
Lemma lem7228959 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem7228960 (_96871 : int) : (term573 _96871) = (term574 _96871).
Proof. exact (MK_COMB (@lem7228959) (@lem7228958 _96871)). Qed.
Lemma lem7228961 (_96871 : int) : (term574 _96871) = (term98 _96871).
Proof. exact (@lem1982721 (term98 _96871)). Qed.
Lemma lem7228962 (_96871 : int) : (term573 _96871) = (term98 _96871).
Proof. exact (TRANS (@lem7228960 _96871) (@lem7228961 _96871)). Qed.
Lemma lem7228964 (_96871 : int) : (term572 _96871) = (term98 _96871).
Proof. exact (TRANS (@lem7228915 _96871) (@lem7228962 _96871)). Qed.
Lemma lem7228965 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7228966 (_96871 : int) : (term575 _96871) = (term576 _96871).
Proof. exact (MK_COMB (@lem7228965) (@lem7228964 _96871)). Qed.
Lemma lem7228967 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7228968 (_96871 : int) : (term571 _96871) = (term577 _96871).
Proof. exact (MK_COMB (@lem7228966 _96871) (@lem7228967)). Qed.
Lemma lem7228969 (_96871 : int) : (term543 _96871) = (term577 _96871).
Proof. exact (TRANS (@lem7228903 _96871) (@lem7228968 _96871)). Qed.
Lemma lem7228970 (_96871 : int) : (term555 _96871) = (term578 _96871).
Proof. exact (@lem1988287 (real_of_int _96871) term552). Qed.
Lemma lem7228977 : term552 = term44.
Proof. exact (@lem1982721 term44). Qed.
Lemma lem7228980 (_96871 : int) : (term579 _96871) = (term579 _96871).
Proof. exact (eq_refl (term579 _96871)). Qed.
Lemma lem7228981 (_96871 : int) : (term580 _96871) = (term581 _96871).
Proof. exact (MK_COMB (@lem7228980 _96871) (@lem7228977)). Qed.
Lemma lem7228982 (_96871 : int) : (term581 _96871) = (term582 _96871).
Proof. exact (@lem1982792 (real_of_int _96871) term44). Qed.
Lemma lem7228984 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7228985 : term44 = term88.
Proof. exact (@lem7228984 term13). Qed.
Lemma lem7228987 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7228988 : term62 = term63.
Proof. exact (@lem7228987 term13). Qed.
Lemma lem7228989 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7228990 : term64 = term65.
Proof. exact (MK_COMB (@lem7228989) (@lem7228988)). Qed.
Lemma lem7228991 : term89 = term90.
Proof. exact (MK_COMB (@lem7228990) (@lem7228985)). Qed.
Lemma lem7228992 : term90 = term91.
Proof. exact (@lem1981613 term62 term44 term44 term44). Qed.
Lemma lem7228994 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7228995 : term71 = term72.
Proof. exact (@lem7228994 term13 term13). Qed.
Lemma lem7228996 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7228997 : term74 = term13.
Proof. exact (EQ_MP (@lem7228996) (@lem940073)). Qed.
Lemma lem7228998 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7228999 : term72 = term44.
Proof. exact (MK_COMB (@lem7228998) (@lem7228997)). Qed.
Lemma lem7229000 : term71 = term44.
Proof. exact (TRANS (@lem7228995) (@lem7228999)). Qed.
Lemma lem7229002 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7229003 : term89 = term94.
Proof. exact (@lem7229002 term13 term13). Qed.
Lemma lem7229004 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229005 : term74 = term13.
Proof. exact (EQ_MP (@lem7229004) (@lem940073)). Qed.
Lemma lem7229006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229007 : term72 = term44.
Proof. exact (MK_COMB (@lem7229006) (@lem7229005)). Qed.
Lemma lem7229008 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7229009 : term94 = term62.
Proof. exact (MK_COMB (@lem7229008) (@lem7229007)). Qed.
Lemma lem7229010 : term89 = term62.
Proof. exact (TRANS (@lem7229003) (@lem7229009)). Qed.
Lemma lem7229011 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7229012 : term95 = term96.
Proof. exact (MK_COMB (@lem7229011) (@lem7229010)). Qed.
Lemma lem7229013 : term91 = term63.
Proof. exact (MK_COMB (@lem7229012) (@lem7229000)). Qed.
Lemma lem7229014 : term90 = term63.
Proof. exact (TRANS (@lem7228992) (@lem7229013)). Qed.
Lemma lem7229015 : term89 = term63.
Proof. exact (TRANS (@lem7228991) (@lem7229014)). Qed.
Lemma lem7229017 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7229018 : term63 = term62.
Proof. exact (@lem7229017 term62). Qed.
Lemma lem7229019 : term89 = term62.
Proof. exact (TRANS (@lem7229015) (@lem7229018)). Qed.
Lemma lem7229020 (_96871 : int) : (term45 _96871) = (term45 _96871).
Proof. exact (eq_refl (term45 _96871)). Qed.
Lemma lem7229023 (_96871 : int) : (term582 _96871) = (term583 _96871).
Proof. exact (MK_COMB (@lem7229020 _96871) (@lem7229019)). Qed.
Lemma lem7229024 (_96871 : int) : (term581 _96871) = (term583 _96871).
Proof. exact (TRANS (@lem7228982 _96871) (@lem7229023 _96871)). Qed.
Lemma lem7229025 (_96871 : int) : (term580 _96871) = (term583 _96871).
Proof. exact (TRANS (@lem7228981 _96871) (@lem7229024 _96871)). Qed.
Lemma lem7229026 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7229027 (_96871 : int) : (term584 _96871) = (term585 _96871).
Proof. exact (MK_COMB (@lem7229026) (@lem7229025 _96871)). Qed.
Lemma lem7229028 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229029 (_96871 : int) : (term578 _96871) = (term586 _96871).
Proof. exact (MK_COMB (@lem7229027 _96871) (@lem7229028)). Qed.
Lemma lem7229030 (_96871 : int) : (term555 _96871) = (term586 _96871).
Proof. exact (TRANS (@lem7228970 _96871) (@lem7229029 _96871)). Qed.
Lemma lem7229031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7229032 (_96871 : int) : (term545 _96871) = (term587 _96871).
Proof. exact (MK_COMB (@lem7229031) (@lem7228969 _96871)). Qed.
Lemma lem7229033 (_96871 : int) : (term556 _96871) = (term588 _96871).
Proof. exact (MK_COMB (@lem7229032 _96871) (@lem7229030 _96871)). Qed.
Lemma lem7229034 (f : nat -> real) (g : nat -> real) (m : nat) : (term557 f g m) = (term589 f g m).
Proof. exact (@lem1988318 term29 (term497 f g m)). Qed.
Lemma lem7229035 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229053 (f : nat -> real) (g : nat -> real) (m : nat) : (term495 f g m) = (term590 f g m).
Proof. exact (@lem1982792 (term493 f g) (term374 f g m)). Qed.
Lemma lem7229058 (m : nat) (f : nat -> real) (g : nat -> real) : (term590 f g m) = (term591 m f g).
Proof. exact (@lem1982761 (term592 f g m) (term493 f g)). Qed.
Lemma lem7229060 (m : nat) (f : nat -> real) (g : nat -> real) : (term495 f g m) = (term591 m f g).
Proof. exact (TRANS (@lem7229053 f g m) (@lem7229058 m f g)). Qed.
Lemma lem7229061 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7229062 (m : nat) (f : nat -> real) (g : nat -> real) : (term496 f g m) = (term593 m f g).
Proof. exact (MK_COMB (@lem7229061) (@lem7229060 m f g)). Qed.
Lemma lem7229063 (m : nat) (f : nat -> real) (g : nat -> real) : (term497 f g m) = (term594 m f g).
Proof. exact (MK_COMB (@lem7229062 m f g) (@lem7229035)). Qed.
Lemma lem7229064 (m : nat) (f : nat -> real) (g : nat -> real) : (term594 m f g) = (term595 m f g).
Proof. exact (@lem1982792 (term591 m f g) term29). Qed.
Lemma lem7229066 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229067 : term29 = term59.
Proof. exact (@lem7229066 (NUMERAL 0)). Qed.
Lemma lem7229069 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229070 : term62 = term63.
Proof. exact (@lem7229069 term13). Qed.
Lemma lem7229071 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229072 : term64 = term65.
Proof. exact (MK_COMB (@lem7229071) (@lem7229070)). Qed.
Lemma lem7229073 : term66 = term67.
Proof. exact (MK_COMB (@lem7229072) (@lem7229067)). Qed.
Lemma lem7229074 : term67 = term68.
Proof. exact (@lem1981613 term62 term29 term44 term44). Qed.
Lemma lem7229076 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229077 : term71 = term72.
Proof. exact (@lem7229076 term13 term13). Qed.
Lemma lem7229078 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229079 : term74 = term13.
Proof. exact (EQ_MP (@lem7229078) (@lem940073)). Qed.
Lemma lem7229080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229081 : term72 = term44.
Proof. exact (MK_COMB (@lem7229080) (@lem7229079)). Qed.
Lemma lem7229082 : term71 = term44.
Proof. exact (TRANS (@lem7229077) (@lem7229081)). Qed.
Lemma lem7229084 (x : nat) : (term75 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7229085 : term66 = term29.
Proof. exact (@lem7229084 term13). Qed.
Lemma lem7229086 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7229087 : term76 = term77.
Proof. exact (MK_COMB (@lem7229086) (@lem7229085)). Qed.
Lemma lem7229088 : term68 = term59.
Proof. exact (MK_COMB (@lem7229087) (@lem7229082)). Qed.
Lemma lem7229089 : term67 = term59.
Proof. exact (TRANS (@lem7229074) (@lem7229088)). Qed.
Lemma lem7229090 : term66 = term59.
Proof. exact (TRANS (@lem7229073) (@lem7229089)). Qed.
Lemma lem7229092 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7229093 : term59 = term29.
Proof. exact (@lem7229092 term29). Qed.
Lemma lem7229094 : term66 = term29.
Proof. exact (TRANS (@lem7229090) (@lem7229093)). Qed.
Lemma lem7229095 (m : nat) (f : nat -> real) (g : nat -> real) : (term596 m f g) = (term596 m f g).
Proof. exact (eq_refl (term596 m f g)). Qed.
Lemma lem7229096 (m : nat) (f : nat -> real) (g : nat -> real) : (term595 m f g) = (term597 m f g).
Proof. exact (MK_COMB (@lem7229095 m f g) (@lem7229094)). Qed.
Lemma lem7229097 (m : nat) (f : nat -> real) (g : nat -> real) : (term597 m f g) = (term591 m f g).
Proof. exact (@lem1982723 (term591 m f g)). Qed.
Lemma lem7229098 (m : nat) (f : nat -> real) (g : nat -> real) : (term595 m f g) = (term591 m f g).
Proof. exact (TRANS (@lem7229096 m f g) (@lem7229097 m f g)). Qed.
Lemma lem7229099 (m : nat) (f : nat -> real) (g : nat -> real) : (term594 m f g) = (term591 m f g).
Proof. exact (TRANS (@lem7229064 m f g) (@lem7229098 m f g)). Qed.
Lemma lem7229100 (m : nat) (f : nat -> real) (g : nat -> real) : (term497 f g m) = (term591 m f g).
Proof. exact (TRANS (@lem7229063 m f g) (@lem7229099 m f g)). Qed.
Lemma lem7229103 : term598 = term598.
Proof. exact (eq_refl term598). Qed.
Lemma lem7229104 (m : nat) (f : nat -> real) (g : nat -> real) : (term599 f g m) = (term600 m f g).
Proof. exact (MK_COMB (@lem7229103) (@lem7229100 m f g)). Qed.
Lemma lem7229105 (m : nat) (f : nat -> real) (g : nat -> real) : (term600 m f g) = (term601 m f g).
Proof. exact (@lem1982792 term29 (term591 m f g)). Qed.
Lemma lem7229106 (m : nat) (f : nat -> real) (g : nat -> real) : (term602 m f g) = (term603 m f g).
Proof. exact (@lem1982781 (term592 f g m) term62 (term493 f g)). Qed.
Lemma lem7229107 (f : nat -> real) (g : nat -> real) : (term604 f g) = (term604 f g).
Proof. exact (eq_refl (term604 f g)). Qed.
Lemma lem7229108 (f : nat -> real) (g : nat -> real) (m : nat) : (term605 f g m) = (term606 f g m).
Proof. exact (@lem1982749 term62 term62 (term374 f g m)). Qed.
Lemma lem7229110 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229111 : term62 = term63.
Proof. exact (@lem7229110 term13). Qed.
Lemma lem7229113 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229114 : term62 = term63.
Proof. exact (@lem7229113 term13). Qed.
Lemma lem7229115 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229116 : term64 = term65.
Proof. exact (MK_COMB (@lem7229115) (@lem7229114)). Qed.
Lemma lem7229117 : term415 = term416.
Proof. exact (MK_COMB (@lem7229116) (@lem7229111)). Qed.
Lemma lem7229118 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7229120 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229121 : term71 = term72.
Proof. exact (@lem7229120 term13 term13). Qed.
Lemma lem7229122 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229123 : term74 = term13.
Proof. exact (EQ_MP (@lem7229122) (@lem940073)). Qed.
Lemma lem7229124 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229125 : term72 = term44.
Proof. exact (MK_COMB (@lem7229124) (@lem7229123)). Qed.
Lemma lem7229126 : term71 = term44.
Proof. exact (TRANS (@lem7229121) (@lem7229125)). Qed.
Lemma lem7229128 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7229129 : term415 = term72.
Proof. exact (@lem7229128 term13 term13). Qed.
Lemma lem7229130 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229131 : term74 = term13.
Proof. exact (EQ_MP (@lem7229130) (@lem940073)). Qed.
Lemma lem7229132 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229133 : term72 = term44.
Proof. exact (MK_COMB (@lem7229132) (@lem7229131)). Qed.
Lemma lem7229134 : term415 = term44.
Proof. exact (TRANS (@lem7229129) (@lem7229133)). Qed.
Lemma lem7229135 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7229136 : term419 = term420.
Proof. exact (MK_COMB (@lem7229135) (@lem7229134)). Qed.
Lemma lem7229137 : term417 = term88.
Proof. exact (MK_COMB (@lem7229136) (@lem7229126)). Qed.
Lemma lem7229138 : term416 = term88.
Proof. exact (TRANS (@lem7229118) (@lem7229137)). Qed.
Lemma lem7229139 : term415 = term88.
Proof. exact (TRANS (@lem7229117) (@lem7229138)). Qed.
Lemma lem7229141 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7229142 : term88 = term44.
Proof. exact (@lem7229141 term44). Qed.
Lemma lem7229143 : term415 = term44.
Proof. exact (TRANS (@lem7229139) (@lem7229142)). Qed.
Lemma lem7229144 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229145 : term421 = term422.
Proof. exact (MK_COMB (@lem7229144) (@lem7229143)). Qed.
Lemma lem7229146 (f : nat -> real) (g : nat -> real) (m : nat) : (term374 f g m) = (term374 f g m).
Proof. exact (eq_refl (term374 f g m)). Qed.
Lemma lem7229147 (f : nat -> real) (g : nat -> real) (m : nat) : (term606 f g m) = (term607 f g m).
Proof. exact (MK_COMB (@lem7229145) (@lem7229146 f g m)). Qed.
Lemma lem7229148 (f : nat -> real) (g : nat -> real) (m : nat) : (term605 f g m) = (term607 f g m).
Proof. exact (TRANS (@lem7229108 f g m) (@lem7229147 f g m)). Qed.
Lemma lem7229149 (f : nat -> real) (g : nat -> real) (m : nat) : (term607 f g m) = (term374 f g m).
Proof. exact (@lem1982709 (term374 f g m)). Qed.
Lemma lem7229150 (f : nat -> real) (g : nat -> real) (m : nat) : (term605 f g m) = (term374 f g m).
Proof. exact (TRANS (@lem7229148 f g m) (@lem7229149 f g m)). Qed.
Lemma lem7229151 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7229152 (f : nat -> real) (g : nat -> real) (m : nat) : (term608 f g m) = (term609 f g m).
Proof. exact (MK_COMB (@lem7229151) (@lem7229150 f g m)). Qed.
Lemma lem7229153 (m : nat) (f : nat -> real) (g : nat -> real) : (term603 m f g) = (term610 m f g).
Proof. exact (MK_COMB (@lem7229152 f g m) (@lem7229107 f g)). Qed.
Lemma lem7229154 (m : nat) (f : nat -> real) (g : nat -> real) : (term602 m f g) = (term610 m f g).
Proof. exact (TRANS (@lem7229106 m f g) (@lem7229153 m f g)). Qed.
Lemma lem7229155 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem7229156 (m : nat) (f : nat -> real) (g : nat -> real) : (term601 m f g) = (term611 m f g).
Proof. exact (MK_COMB (@lem7229155) (@lem7229154 m f g)). Qed.
Lemma lem7229157 (m : nat) (f : nat -> real) (g : nat -> real) : (term611 m f g) = (term610 m f g).
Proof. exact (@lem1982721 (term610 m f g)). Qed.
Lemma lem7229158 (m : nat) (f : nat -> real) (g : nat -> real) : (term601 m f g) = (term610 m f g).
Proof. exact (TRANS (@lem7229156 m f g) (@lem7229157 m f g)). Qed.
Lemma lem7229159 (m : nat) (f : nat -> real) (g : nat -> real) : (term600 m f g) = (term610 m f g).
Proof. exact (TRANS (@lem7229105 m f g) (@lem7229158 m f g)). Qed.
Lemma lem7229160 (m : nat) (f : nat -> real) (g : nat -> real) : (term599 f g m) = (term610 m f g).
Proof. exact (TRANS (@lem7229104 m f g) (@lem7229159 m f g)). Qed.
Lemma lem7229161 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7229162 (m : nat) (f : nat -> real) (g : nat -> real) : (term612 f g m) = (term613 m f g).
Proof. exact (MK_COMB (@lem7229161) (@lem7229160 m f g)). Qed.
Lemma lem7229163 (m : nat) (f : nat -> real) (g : nat -> real) : (term613 m f g) = (term614 m f g).
Proof. exact (@lem1982785 (term610 m f g)). Qed.
Lemma lem7229164 (m : nat) (f : nat -> real) (g : nat -> real) : (term614 m f g) = (term615 m f g).
Proof. exact (@lem1982781 (term374 f g m) term62 (term604 f g)). Qed.
Lemma lem7229165 (f : nat -> real) (g : nat -> real) : (term616 f g) = (term617 f g).
Proof. exact (@lem1982749 term62 term62 (term493 f g)). Qed.
Lemma lem7229167 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229168 : term62 = term63.
Proof. exact (@lem7229167 term13). Qed.
Lemma lem7229170 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229171 : term62 = term63.
Proof. exact (@lem7229170 term13). Qed.
Lemma lem7229172 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229173 : term64 = term65.
Proof. exact (MK_COMB (@lem7229172) (@lem7229171)). Qed.
Lemma lem7229174 : term415 = term416.
Proof. exact (MK_COMB (@lem7229173) (@lem7229168)). Qed.
Lemma lem7229175 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7229177 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229178 : term71 = term72.
Proof. exact (@lem7229177 term13 term13). Qed.
Lemma lem7229179 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229180 : term74 = term13.
Proof. exact (EQ_MP (@lem7229179) (@lem940073)). Qed.
Lemma lem7229181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229182 : term72 = term44.
Proof. exact (MK_COMB (@lem7229181) (@lem7229180)). Qed.
Lemma lem7229183 : term71 = term44.
Proof. exact (TRANS (@lem7229178) (@lem7229182)). Qed.
Lemma lem7229185 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7229186 : term415 = term72.
Proof. exact (@lem7229185 term13 term13). Qed.
Lemma lem7229187 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229188 : term74 = term13.
Proof. exact (EQ_MP (@lem7229187) (@lem940073)). Qed.
Lemma lem7229189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229190 : term72 = term44.
Proof. exact (MK_COMB (@lem7229189) (@lem7229188)). Qed.
Lemma lem7229191 : term415 = term44.
Proof. exact (TRANS (@lem7229186) (@lem7229190)). Qed.
Lemma lem7229192 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7229193 : term419 = term420.
Proof. exact (MK_COMB (@lem7229192) (@lem7229191)). Qed.
Lemma lem7229194 : term417 = term88.
Proof. exact (MK_COMB (@lem7229193) (@lem7229183)). Qed.
Lemma lem7229195 : term416 = term88.
Proof. exact (TRANS (@lem7229175) (@lem7229194)). Qed.
Lemma lem7229196 : term415 = term88.
Proof. exact (TRANS (@lem7229174) (@lem7229195)). Qed.
Lemma lem7229198 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7229199 : term88 = term44.
Proof. exact (@lem7229198 term44). Qed.
Lemma lem7229200 : term415 = term44.
Proof. exact (TRANS (@lem7229196) (@lem7229199)). Qed.
Lemma lem7229201 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229202 : term421 = term422.
Proof. exact (MK_COMB (@lem7229201) (@lem7229200)). Qed.
Lemma lem7229203 (f : nat -> real) (g : nat -> real) : (term493 f g) = (term493 f g).
Proof. exact (eq_refl (term493 f g)). Qed.
Lemma lem7229204 (f : nat -> real) (g : nat -> real) : (term617 f g) = (term618 f g).
Proof. exact (MK_COMB (@lem7229202) (@lem7229203 f g)). Qed.
Lemma lem7229205 (f : nat -> real) (g : nat -> real) : (term616 f g) = (term618 f g).
Proof. exact (TRANS (@lem7229165 f g) (@lem7229204 f g)). Qed.
Lemma lem7229206 (f : nat -> real) (g : nat -> real) : (term618 f g) = (term493 f g).
Proof. exact (@lem1982709 (term493 f g)). Qed.
Lemma lem7229207 (f : nat -> real) (g : nat -> real) : (term616 f g) = (term493 f g).
Proof. exact (TRANS (@lem7229205 f g) (@lem7229206 f g)). Qed.
Lemma lem7229210 (f : nat -> real) (g : nat -> real) (m : nat) : (term619 f g m) = (term619 f g m).
Proof. exact (eq_refl (term619 f g m)). Qed.
Lemma lem7229211 (m : nat) (f : nat -> real) (g : nat -> real) : (term615 m f g) = (term591 m f g).
Proof. exact (MK_COMB (@lem7229210 f g m) (@lem7229207 f g)). Qed.
Lemma lem7229212 (m : nat) (f : nat -> real) (g : nat -> real) : (term614 m f g) = (term591 m f g).
Proof. exact (TRANS (@lem7229164 m f g) (@lem7229211 m f g)). Qed.
Lemma lem7229213 (m : nat) (f : nat -> real) (g : nat -> real) : (term613 m f g) = (term591 m f g).
Proof. exact (TRANS (@lem7229163 m f g) (@lem7229212 m f g)). Qed.
Lemma lem7229214 (f : nat -> real) (g : nat -> real) (m : nat) : (term620 f g m) = (term620 f g m).
Proof. exact (eq_refl (term620 f g m)). Qed.
Lemma lem7229215 (m : nat) (f : nat -> real) (g : nat -> real) : ((term612 f g m) = (term613 m f g)) = ((term612 f g m) = (term591 m f g)).
Proof. exact (MK_COMB (@lem7229214 f g m) (@lem7229213 m f g)). Qed.
Lemma lem7229216 (m : nat) (f : nat -> real) (g : nat -> real) : (term612 f g m) = (term591 m f g).
Proof. exact (EQ_MP (@lem7229215 m f g) (@lem7229162 m f g)). Qed.
Lemma lem7229217 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7229218 (m : nat) (f : nat -> real) (g : nat -> real) : (term621 f g m) = (term622 m f g).
Proof. exact (MK_COMB (@lem7229217) (@lem7229216 m f g)). Qed.
Lemma lem7229219 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229220 (m : nat) (f : nat -> real) (g : nat -> real) : (term623 f g m) = (term624 m f g).
Proof. exact (MK_COMB (@lem7229218 m f g) (@lem7229219)). Qed.
Lemma lem7229221 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7229222 (m : nat) (f : nat -> real) (g : nat -> real) : (term625 f g m) = (term626 m f g).
Proof. exact (MK_COMB (@lem7229221) (@lem7229160 m f g)). Qed.
Lemma lem7229223 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229224 (m : nat) (f : nat -> real) (g : nat -> real) : (term627 f g m) = (term628 m f g).
Proof. exact (MK_COMB (@lem7229222 m f g) (@lem7229223)). Qed.
Lemma lem7229225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7229226 (m : nat) (f : nat -> real) (g : nat -> real) : (term629 f g m) = (term630 m f g).
Proof. exact (MK_COMB (@lem7229225) (@lem7229224 m f g)). Qed.
Lemma lem7229227 (m : nat) (f : nat -> real) (g : nat -> real) : (term589 f g m) = (term631 m f g).
Proof. exact (MK_COMB (@lem7229226 m f g) (@lem7229220 m f g)). Qed.
Lemma lem7229228 (m : nat) (f : nat -> real) (g : nat -> real) : (term557 f g m) = (term631 m f g).
Proof. exact (TRANS (@lem7229034 f g m) (@lem7229227 m f g)). Qed.
Lemma lem7229229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7229230 (_96871 : int) : (term559 _96871) = (term632 _96871).
Proof. exact (MK_COMB (@lem7229229) (@lem7229033 _96871)). Qed.
Lemma lem7229231 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term560 _96871 f g m) = (term633 _96871 m f g).
Proof. exact (MK_COMB (@lem7229230 _96871) (@lem7229228 m f g)). Qed.
Lemma lem7229232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7229233 (_96871 : int) : (term561 _96871) = (term634 _96871).
Proof. exact (MK_COMB (@lem7229232) (@lem7228902 _96871)). Qed.
Lemma lem7229234 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term562 _96871 f g m) = (term635 _96871 m f g).
Proof. exact (MK_COMB (@lem7229233 _96871) (@lem7229231 _96871 m f g)). Qed.
Lemma lem7229235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7229236 (_96871 : int) : (term51 _96871) = (term133 _96871).
Proof. exact (MK_COMB (@lem7229235) (@lem7228883 _96871)). Qed.
Lemma lem7229237 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term563 _96871 f g m) = (term636 _96871 m f g).
Proof. exact (MK_COMB (@lem7229236 _96871) (@lem7229234 _96871 m f g)). Qed.
Lemma lem7229244 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term564 _96871 f g m) = (term636 _96871 m f g).
Proof. exact (TRANS (@lem7228835 _96871 f g m) (@lem7229237 _96871 m f g)). Qed.
Lemma lem7229258 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term633 _96871 m f g) = (term637 _96871 m f g).
Proof. exact (@lem19158 (term628 m f g) (term588 _96871) (term624 m f g)). Qed.
Lemma lem7229265 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term638 _96871 m f g) = (term639 _96871 m f g).
Proof. exact (@lem19367 (term577 _96871) (term586 _96871) (term624 m f g)). Qed.
Lemma lem7229272 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term640 _96871 m f g) = (term641 _96871 m f g).
Proof. exact (@lem19367 (term577 _96871) (term586 _96871) (term628 m f g)). Qed.
Lemma lem7229273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7229274 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term642 _96871 m f g) = (term643 _96871 m f g).
Proof. exact (MK_COMB (@lem7229273) (@lem7229272 _96871 m f g)). Qed.
Lemma lem7229275 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term637 _96871 m f g) = (term644 _96871 m f g).
Proof. exact (MK_COMB (@lem7229274 _96871 m f g) (@lem7229265 _96871 m f g)). Qed.
Lemma lem7229277 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term633 _96871 m f g) = (term644 _96871 m f g).
Proof. exact (TRANS (@lem7229258 _96871 m f g) (@lem7229275 _96871 m f g)). Qed.
Lemma lem7229280 (_96871 : int) : (term634 _96871) = (term634 _96871).
Proof. exact (eq_refl (term634 _96871)). Qed.
Lemma lem7229281 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term635 _96871 m f g) = (term645 _96871 m f g).
Proof. exact (MK_COMB (@lem7229280 _96871) (@lem7229277 _96871 m f g)). Qed.
Lemma lem7229282 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term645 _96871 m f g) = (term646 _96871 m f g).
Proof. exact (@lem19158 (term641 _96871 m f g) (term570 _96871) (term639 _96871 m f g)). Qed.
Lemma lem7229289 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term647 _96871 m f g) = (term648 _96871 m f g).
Proof. exact (@lem19158 (term649 _96871 m f g) (term570 _96871) (term650 _96871 m f g)). Qed.
Lemma lem7229296 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term651 _96871 m f g) = (term652 _96871 m f g).
Proof. exact (@lem19158 (term653 _96871 m f g) (term570 _96871) (term654 _96871 m f g)). Qed.
Lemma lem7229297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7229298 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term655 _96871 m f g) = (term656 _96871 m f g).
Proof. exact (MK_COMB (@lem7229297) (@lem7229296 _96871 m f g)). Qed.
Lemma lem7229299 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term646 _96871 m f g) = (term657 _96871 m f g).
Proof. exact (MK_COMB (@lem7229298 _96871 m f g) (@lem7229289 _96871 m f g)). Qed.
Lemma lem7229300 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term645 _96871 m f g) = (term657 _96871 m f g).
Proof. exact (TRANS (@lem7229282 _96871 m f g) (@lem7229299 _96871 m f g)). Qed.
Lemma lem7229301 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term635 _96871 m f g) = (term657 _96871 m f g).
Proof. exact (TRANS (@lem7229281 _96871 m f g) (@lem7229300 _96871 m f g)). Qed.
Lemma lem7229304 (_96871 : int) : (term133 _96871) = (term133 _96871).
Proof. exact (eq_refl (term133 _96871)). Qed.
Lemma lem7229305 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term636 _96871 m f g) = (term658 _96871 m f g).
Proof. exact (MK_COMB (@lem7229304 _96871) (@lem7229301 _96871 m f g)). Qed.
Lemma lem7229306 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term658 _96871 m f g) = (term659 _96871 m f g).
Proof. exact (@lem19158 (term652 _96871 m f g) (term82 _96871) (term648 _96871 m f g)). Qed.
Lemma lem7229313 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term660 _96871 m f g) = (term661 _96871 m f g).
Proof. exact (@lem19158 (term662 _96871 m f g) (term82 _96871) (term663 _96871 m f g)). Qed.
Lemma lem7229320 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term664 _96871 m f g) = (term665 _96871 m f g).
Proof. exact (@lem19158 (term666 _96871 m f g) (term82 _96871) (term667 _96871 m f g)). Qed.
Lemma lem7229321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7229322 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term668 _96871 m f g) = (term669 _96871 m f g).
Proof. exact (MK_COMB (@lem7229321) (@lem7229320 _96871 m f g)). Qed.
Lemma lem7229323 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term659 _96871 m f g) = (term670 _96871 m f g).
Proof. exact (MK_COMB (@lem7229322 _96871 m f g) (@lem7229313 _96871 m f g)). Qed.
Lemma lem7229324 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term658 _96871 m f g) = (term670 _96871 m f g).
Proof. exact (TRANS (@lem7229306 _96871 m f g) (@lem7229323 _96871 m f g)). Qed.
Lemma lem7229325 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term636 _96871 m f g) = (term670 _96871 m f g).
Proof. exact (TRANS (@lem7229305 _96871 m f g) (@lem7229324 _96871 m f g)). Qed.
Lemma lem7229326 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) : (term564 _96871 f g m) = (term670 _96871 m f g).
Proof. exact (TRANS (@lem7229244 _96871 m f g) (@lem7229325 _96871 m f g)). Qed.
Lemma lem7229348 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term670 _96871 m f g) : term670 _96871 m f g.
Proof. exact (h1). Qed.
Lemma lem7229349 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term665 _96871 m f g) : term665 _96871 m f g.
Proof. exact (h1). Qed.
Lemma lem7229350 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term671 _96871 m f g.
Proof. exact (h1). Qed.
Lemma lem7229351 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term666 _96871 m f g.
Proof. exact (proj2 (@lem7229350 _96871 m f g h1)). Qed.
Lemma lem7229352 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term82 _96871.
Proof. exact (proj1 (@lem7229350 _96871 m f g h1)). Qed.
Lemma lem7229353 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term653 _96871 m f g.
Proof. exact (proj2 (@lem7229351 _96871 m f g h1)). Qed.
Lemma lem7229356 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term577 _96871.
Proof. exact (proj1 (@lem7229353 _96871 m f g h1)). Qed.
Lemma lem7229358 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7229359 : term672 = term110.
Proof. exact (@lem7229358 term29 term44). Qed.
Lemma lem7229361 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229362 : term44 = term88.
Proof. exact (@lem7229361 term13). Qed.
Lemma lem7229364 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229365 : term29 = term59.
Proof. exact (@lem7229364 (NUMERAL 0)). Qed.
Lemma lem7229366 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7229367 : term479 = term480.
Proof. exact (MK_COMB (@lem7229366) (@lem7229365)). Qed.
Lemma lem7229368 : term110 = term673.
Proof. exact (MK_COMB (@lem7229367) (@lem7229362)). Qed.
Lemma lem7229369 : term674.
Proof. exact (@lem1980255 term29 term44 term44 term44). Qed.
Lemma lem7229371 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229372 : term110 = term111.
Proof. exact (@lem7229371 (NUMERAL 0) term13). Qed.
Lemma lem7229373 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229374 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229375 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229374 h1) (fun h1 : term111 = True => @lem7229373)). Qed.
Lemma lem7229376 : term111 = True.
Proof. exact (EQ_MP (@lem7229375) (@lem7229373)). Qed.
Lemma lem7229377 : term110 = True.
Proof. exact (TRANS (@lem7229372) (@lem7229376)). Qed.
Lemma lem7229378 : True = term110.
Proof. exact (SYM (@lem7229377)). Qed.
Lemma lem7229379 : term110.
Proof. exact (EQ_MP (@lem7229378) (@lem0)). Qed.
Lemma lem7229380 : term675.
Proof. exact (@lem7229369 (@lem7229379)). Qed.
Lemma lem7229382 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229383 : term110 = term111.
Proof. exact (@lem7229382 (NUMERAL 0) term13). Qed.
Lemma lem7229384 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229385 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229386 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229385 h1) (fun h1 : term111 = True => @lem7229384)). Qed.
Lemma lem7229387 : term111 = True.
Proof. exact (EQ_MP (@lem7229386) (@lem7229384)). Qed.
Lemma lem7229388 : term110 = True.
Proof. exact (TRANS (@lem7229383) (@lem7229387)). Qed.
Lemma lem7229389 : True = term110.
Proof. exact (SYM (@lem7229388)). Qed.
Lemma lem7229390 : term110.
Proof. exact (EQ_MP (@lem7229389) (@lem0)). Qed.
Lemma lem7229391 : term673 = term676.
Proof. exact (@lem7229380 (@lem7229390)). Qed.
Lemma lem7229393 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229394 : term71 = term72.
Proof. exact (@lem7229393 term13 term13). Qed.
Lemma lem7229395 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229396 : term74 = term13.
Proof. exact (EQ_MP (@lem7229395) (@lem940073)). Qed.
Lemma lem7229397 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229398 : term72 = term44.
Proof. exact (MK_COMB (@lem7229397) (@lem7229396)). Qed.
Lemma lem7229399 : term71 = term44.
Proof. exact (TRANS (@lem7229394) (@lem7229398)). Qed.
Lemma lem7229401 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229402 : term122 = term29.
Proof. exact (@lem7229401 term13). Qed.
Lemma lem7229403 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7229404 : term485 = term479.
Proof. exact (MK_COMB (@lem7229403) (@lem7229402)). Qed.
Lemma lem7229405 : term676 = term110.
Proof. exact (MK_COMB (@lem7229404) (@lem7229399)). Qed.
Lemma lem7229407 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229408 : term110 = term111.
Proof. exact (@lem7229407 (NUMERAL 0) term13). Qed.
Lemma lem7229409 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229410 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229411 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229410 h1) (fun h1 : term111 = True => @lem7229409)). Qed.
Lemma lem7229412 : term111 = True.
Proof. exact (EQ_MP (@lem7229411) (@lem7229409)). Qed.
Lemma lem7229413 : term110 = True.
Proof. exact (TRANS (@lem7229408) (@lem7229412)). Qed.
Lemma lem7229414 : term676 = True.
Proof. exact (TRANS (@lem7229405) (@lem7229413)). Qed.
Lemma lem7229415 : term673 = True.
Proof. exact (TRANS (@lem7229391) (@lem7229414)). Qed.
Lemma lem7229416 : term110 = True.
Proof. exact (TRANS (@lem7229368) (@lem7229415)). Qed.
Lemma lem7229417 : term672 = True.
Proof. exact (TRANS (@lem7229359) (@lem7229416)). Qed.
Lemma lem7229418 : True = term672.
Proof. exact (SYM (@lem7229417)). Qed.
Lemma lem7229419 : term672.
Proof. exact (EQ_MP (@lem7229418) (@lem0)). Qed.
Lemma lem7229420 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term677 _96871.
Proof. exact (conj (@lem7229419) (@lem7229352 _96871 m f g h1)). Qed.
Lemma lem7229422 (x : real) (y : real) : term678 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7229423 (_96871 : int) : term679 _96871.
Proof. exact (@lem7229422 term44 (real_of_int _96871)). Qed.
Lemma lem7229424 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term680 _96871.
Proof. exact (@lem7229423 _96871 (@lem7229420 _96871 m f g h1)). Qed.
Lemma lem7229425 (_96871 : int) : (term681 _96871) = (real_of_int _96871).
Proof. exact (@lem1982733 (real_of_int _96871)). Qed.
Lemma lem7229426 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7229427 (_96871 : int) : (term682 _96871) = (term81 _96871).
Proof. exact (MK_COMB (@lem7229426) (@lem7229425 _96871)). Qed.
Lemma lem7229428 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229429 (_96871 : int) : (term680 _96871) = (term82 _96871).
Proof. exact (MK_COMB (@lem7229427 _96871) (@lem7229428)). Qed.
Lemma lem7229430 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term82 _96871.
Proof. exact (EQ_MP (@lem7229429 _96871) (@lem7229424 _96871 m f g h1)). Qed.
Lemma lem7229432 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7229433 : term672 = term110.
Proof. exact (@lem7229432 term29 term44). Qed.
Lemma lem7229435 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229436 : term44 = term88.
Proof. exact (@lem7229435 term13). Qed.
Lemma lem7229438 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229439 : term29 = term59.
Proof. exact (@lem7229438 (NUMERAL 0)). Qed.
Lemma lem7229440 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7229441 : term479 = term480.
Proof. exact (MK_COMB (@lem7229440) (@lem7229439)). Qed.
Lemma lem7229442 : term110 = term673.
Proof. exact (MK_COMB (@lem7229441) (@lem7229436)). Qed.
Lemma lem7229443 : term674.
Proof. exact (@lem1980255 term29 term44 term44 term44). Qed.
Lemma lem7229445 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229446 : term110 = term111.
Proof. exact (@lem7229445 (NUMERAL 0) term13). Qed.
Lemma lem7229447 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229448 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229449 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229448 h1) (fun h1 : term111 = True => @lem7229447)). Qed.
Lemma lem7229450 : term111 = True.
Proof. exact (EQ_MP (@lem7229449) (@lem7229447)). Qed.
Lemma lem7229451 : term110 = True.
Proof. exact (TRANS (@lem7229446) (@lem7229450)). Qed.
Lemma lem7229452 : True = term110.
Proof. exact (SYM (@lem7229451)). Qed.
Lemma lem7229453 : term110.
Proof. exact (EQ_MP (@lem7229452) (@lem0)). Qed.
Lemma lem7229454 : term675.
Proof. exact (@lem7229443 (@lem7229453)). Qed.
Lemma lem7229456 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229457 : term110 = term111.
Proof. exact (@lem7229456 (NUMERAL 0) term13). Qed.
Lemma lem7229458 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229459 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229460 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229459 h1) (fun h1 : term111 = True => @lem7229458)). Qed.
Lemma lem7229461 : term111 = True.
Proof. exact (EQ_MP (@lem7229460) (@lem7229458)). Qed.
Lemma lem7229462 : term110 = True.
Proof. exact (TRANS (@lem7229457) (@lem7229461)). Qed.
Lemma lem7229463 : True = term110.
Proof. exact (SYM (@lem7229462)). Qed.
Lemma lem7229464 : term110.
Proof. exact (EQ_MP (@lem7229463) (@lem0)). Qed.
Lemma lem7229465 : term673 = term676.
Proof. exact (@lem7229454 (@lem7229464)). Qed.
Lemma lem7229467 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229468 : term71 = term72.
Proof. exact (@lem7229467 term13 term13). Qed.
Lemma lem7229469 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229470 : term74 = term13.
Proof. exact (EQ_MP (@lem7229469) (@lem940073)). Qed.
Lemma lem7229471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229472 : term72 = term44.
Proof. exact (MK_COMB (@lem7229471) (@lem7229470)). Qed.
Lemma lem7229473 : term71 = term44.
Proof. exact (TRANS (@lem7229468) (@lem7229472)). Qed.
Lemma lem7229475 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229476 : term122 = term29.
Proof. exact (@lem7229475 term13). Qed.
Lemma lem7229477 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7229478 : term485 = term479.
Proof. exact (MK_COMB (@lem7229477) (@lem7229476)). Qed.
Lemma lem7229479 : term676 = term110.
Proof. exact (MK_COMB (@lem7229478) (@lem7229473)). Qed.
Lemma lem7229481 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229482 : term110 = term111.
Proof. exact (@lem7229481 (NUMERAL 0) term13). Qed.
Lemma lem7229483 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229484 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229485 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229484 h1) (fun h1 : term111 = True => @lem7229483)). Qed.
Lemma lem7229486 : term111 = True.
Proof. exact (EQ_MP (@lem7229485) (@lem7229483)). Qed.
Lemma lem7229487 : term110 = True.
Proof. exact (TRANS (@lem7229482) (@lem7229486)). Qed.
Lemma lem7229488 : term676 = True.
Proof. exact (TRANS (@lem7229479) (@lem7229487)). Qed.
Lemma lem7229489 : term673 = True.
Proof. exact (TRANS (@lem7229465) (@lem7229488)). Qed.
Lemma lem7229490 : term110 = True.
Proof. exact (TRANS (@lem7229442) (@lem7229489)). Qed.
Lemma lem7229491 : term672 = True.
Proof. exact (TRANS (@lem7229433) (@lem7229490)). Qed.
Lemma lem7229492 : True = term672.
Proof. exact (SYM (@lem7229491)). Qed.
Lemma lem7229493 : term672.
Proof. exact (EQ_MP (@lem7229492) (@lem0)). Qed.
Lemma lem7229494 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term683 _96871.
Proof. exact (conj (@lem7229493) (@lem7229356 _96871 m f g h1)). Qed.
Lemma lem7229496 (x : real) (y : real) : term678 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7229497 (_96871 : int) : term684 _96871.
Proof. exact (@lem7229496 term44 (term98 _96871)). Qed.
Lemma lem7229498 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term685 _96871.
Proof. exact (@lem7229497 _96871 (@lem7229494 _96871 m f g h1)). Qed.
Lemma lem7229499 (_96871 : int) : (term686 _96871) = (term98 _96871).
Proof. exact (@lem1982733 (term98 _96871)). Qed.
Lemma lem7229500 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7229501 (_96871 : int) : (term687 _96871) = (term576 _96871).
Proof. exact (MK_COMB (@lem7229500) (@lem7229499 _96871)). Qed.
Lemma lem7229502 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229503 (_96871 : int) : (term685 _96871) = (term577 _96871).
Proof. exact (MK_COMB (@lem7229501 _96871) (@lem7229502)). Qed.
Lemma lem7229504 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term577 _96871.
Proof. exact (EQ_MP (@lem7229503 _96871) (@lem7229498 _96871 m f g h1)). Qed.
Lemma lem7229505 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term688 _96871.
Proof. exact (conj (@lem7229504 _96871 m f g h1) (@lem7229430 _96871 m f g h1)). Qed.
Lemma lem7229507 (x : real) (y : real) : term689 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7229508 (_96871 : int) : term690 _96871.
Proof. exact (@lem7229507 (term98 _96871) (real_of_int _96871)). Qed.
Lemma lem7229509 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term691 _96871.
Proof. exact (@lem7229508 _96871 (@lem7229505 _96871 m f g h1)). Qed.
Lemma lem7229510 (_96871 : int) : (term692 _96871) = (term693 _96871).
Proof. exact (@lem1982759 (term101 _96871) (real_of_int _96871) term62). Qed.
Lemma lem7229511 (_96871 : int) : (term694 _96871) = (term103 _96871).
Proof. exact (@lem1982713 term62 (real_of_int _96871)). Qed.
Lemma lem7229513 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229514 : term44 = term88.
Proof. exact (@lem7229513 term13). Qed.
Lemma lem7229516 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229517 : term62 = term63.
Proof. exact (@lem7229516 term13). Qed.
Lemma lem7229518 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7229519 : term104 = term105.
Proof. exact (MK_COMB (@lem7229518) (@lem7229517)). Qed.
Lemma lem7229520 : term106 = term107.
Proof. exact (MK_COMB (@lem7229519) (@lem7229514)). Qed.
Lemma lem7229521 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7229523 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229524 : term110 = term111.
Proof. exact (@lem7229523 (NUMERAL 0) term13). Qed.
Lemma lem7229525 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229526 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229527 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229526 h1) (fun h1 : term111 = True => @lem7229525)). Qed.
Lemma lem7229528 : term111 = True.
Proof. exact (EQ_MP (@lem7229527) (@lem7229525)). Qed.
Lemma lem7229529 : term110 = True.
Proof. exact (TRANS (@lem7229524) (@lem7229528)). Qed.
Lemma lem7229530 : True = term110.
Proof. exact (SYM (@lem7229529)). Qed.
Lemma lem7229531 : term110.
Proof. exact (EQ_MP (@lem7229530) (@lem0)). Qed.
Lemma lem7229532 : term113.
Proof. exact (@lem7229521 (@lem7229531)). Qed.
Lemma lem7229534 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229535 : term110 = term111.
Proof. exact (@lem7229534 (NUMERAL 0) term13). Qed.
Lemma lem7229536 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229537 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229538 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229537 h1) (fun h1 : term111 = True => @lem7229536)). Qed.
Lemma lem7229539 : term111 = True.
Proof. exact (EQ_MP (@lem7229538) (@lem7229536)). Qed.
Lemma lem7229540 : term110 = True.
Proof. exact (TRANS (@lem7229535) (@lem7229539)). Qed.
Lemma lem7229541 : True = term110.
Proof. exact (SYM (@lem7229540)). Qed.
Lemma lem7229542 : term110.
Proof. exact (EQ_MP (@lem7229541) (@lem0)). Qed.
Lemma lem7229543 : term114.
Proof. exact (@lem7229532 (@lem7229542)). Qed.
Lemma lem7229545 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229546 : term110 = term111.
Proof. exact (@lem7229545 (NUMERAL 0) term13). Qed.
Lemma lem7229547 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229548 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229549 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229548 h1) (fun h1 : term111 = True => @lem7229547)). Qed.
Lemma lem7229550 : term111 = True.
Proof. exact (EQ_MP (@lem7229549) (@lem7229547)). Qed.
Lemma lem7229551 : term110 = True.
Proof. exact (TRANS (@lem7229546) (@lem7229550)). Qed.
Lemma lem7229552 : True = term110.
Proof. exact (SYM (@lem7229551)). Qed.
Lemma lem7229553 : term110.
Proof. exact (EQ_MP (@lem7229552) (@lem0)). Qed.
Lemma lem7229554 : term115.
Proof. exact (@lem7229543 (@lem7229553)). Qed.
Lemma lem7229556 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229557 : term71 = term72.
Proof. exact (@lem7229556 term13 term13). Qed.
Lemma lem7229558 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229559 : term74 = term13.
Proof. exact (EQ_MP (@lem7229558) (@lem940073)). Qed.
Lemma lem7229560 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229561 : term72 = term44.
Proof. exact (MK_COMB (@lem7229560) (@lem7229559)). Qed.
Lemma lem7229562 : term71 = term44.
Proof. exact (TRANS (@lem7229557) (@lem7229561)). Qed.
Lemma lem7229564 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7229565 : term89 = term94.
Proof. exact (@lem7229564 term13 term13). Qed.
Lemma lem7229566 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229567 : term74 = term13.
Proof. exact (EQ_MP (@lem7229566) (@lem940073)). Qed.
Lemma lem7229568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229569 : term72 = term44.
Proof. exact (MK_COMB (@lem7229568) (@lem7229567)). Qed.
Lemma lem7229570 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7229571 : term94 = term62.
Proof. exact (MK_COMB (@lem7229570) (@lem7229569)). Qed.
Lemma lem7229572 : term89 = term62.
Proof. exact (TRANS (@lem7229565) (@lem7229571)). Qed.
Lemma lem7229573 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7229574 : term116 = term104.
Proof. exact (MK_COMB (@lem7229573) (@lem7229572)). Qed.
Lemma lem7229575 : term117 = term106.
Proof. exact (MK_COMB (@lem7229574) (@lem7229562)). Qed.
Lemma lem7229577 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7229578 : term106 = term29.
Proof. exact (@lem7229577 term13). Qed.
Lemma lem7229579 : term117 = term29.
Proof. exact (TRANS (@lem7229575) (@lem7229578)). Qed.
Lemma lem7229580 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229581 : term119 = term120.
Proof. exact (MK_COMB (@lem7229580) (@lem7229579)). Qed.
Lemma lem7229582 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7229583 : term121 = term122.
Proof. exact (MK_COMB (@lem7229581) (@lem7229582)). Qed.
Lemma lem7229585 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229586 : term122 = term29.
Proof. exact (@lem7229585 term13). Qed.
Lemma lem7229587 : term121 = term29.
Proof. exact (TRANS (@lem7229583) (@lem7229586)). Qed.
Lemma lem7229589 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229590 : term71 = term72.
Proof. exact (@lem7229589 term13 term13). Qed.
Lemma lem7229591 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229592 : term74 = term13.
Proof. exact (EQ_MP (@lem7229591) (@lem940073)). Qed.
Lemma lem7229593 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229594 : term72 = term44.
Proof. exact (MK_COMB (@lem7229593) (@lem7229592)). Qed.
Lemma lem7229595 : term71 = term44.
Proof. exact (TRANS (@lem7229590) (@lem7229594)). Qed.
Lemma lem7229596 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7229597 : term124 = term122.
Proof. exact (MK_COMB (@lem7229596) (@lem7229595)). Qed.
Lemma lem7229599 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229600 : term122 = term29.
Proof. exact (@lem7229599 term13). Qed.
Lemma lem7229601 : term124 = term29.
Proof. exact (TRANS (@lem7229597) (@lem7229600)). Qed.
Lemma lem7229602 : term29 = term124.
Proof. exact (SYM (@lem7229601)). Qed.
Lemma lem7229603 : term121 = term124.
Proof. exact (TRANS (@lem7229587) (@lem7229602)). Qed.
Lemma lem7229604 : term107 = term59.
Proof. exact (@lem7229554 (@lem7229603)). Qed.
Lemma lem7229605 : term106 = term59.
Proof. exact (TRANS (@lem7229520) (@lem7229604)). Qed.
Lemma lem7229607 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7229608 : term59 = term29.
Proof. exact (@lem7229607 term29). Qed.
Lemma lem7229609 : term106 = term29.
Proof. exact (TRANS (@lem7229605) (@lem7229608)). Qed.
Lemma lem7229610 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229611 : term125 = term120.
Proof. exact (MK_COMB (@lem7229610) (@lem7229609)). Qed.
Lemma lem7229612 (_96871 : int) : (real_of_int _96871) = (real_of_int _96871).
Proof. exact (eq_refl (real_of_int _96871)). Qed.
Lemma lem7229613 (_96871 : int) : (term103 _96871) = (term126 _96871).
Proof. exact (MK_COMB (@lem7229611) (@lem7229612 _96871)). Qed.
Lemma lem7229614 (_96871 : int) : (term694 _96871) = (term126 _96871).
Proof. exact (TRANS (@lem7229511 _96871) (@lem7229613 _96871)). Qed.
Lemma lem7229615 (_96871 : int) : (term126 _96871) = term29.
Proof. exact (@lem1982719 (real_of_int _96871)). Qed.
Lemma lem7229616 (_96871 : int) : (term694 _96871) = term29.
Proof. exact (TRANS (@lem7229614 _96871) (@lem7229615 _96871)). Qed.
Lemma lem7229617 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7229618 (_96871 : int) : (term695 _96871) = term128.
Proof. exact (MK_COMB (@lem7229617) (@lem7229616 _96871)). Qed.
Lemma lem7229619 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem7229620 (_96871 : int) : (term693 _96871) = term129.
Proof. exact (MK_COMB (@lem7229618 _96871) (@lem7229619)). Qed.
Lemma lem7229621 (_96871 : int) : (term692 _96871) = term129.
Proof. exact (TRANS (@lem7229510 _96871) (@lem7229620 _96871)). Qed.
Lemma lem7229622 : term129 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem7229623 (_96871 : int) : (term692 _96871) = term62.
Proof. exact (TRANS (@lem7229621 _96871) (@lem7229622)). Qed.
Lemma lem7229624 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7229625 (_96871 : int) : (term696 _96871) = term131.
Proof. exact (MK_COMB (@lem7229624) (@lem7229623 _96871)). Qed.
Lemma lem7229626 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229627 (_96871 : int) : (term691 _96871) = term132.
Proof. exact (MK_COMB (@lem7229625 _96871) (@lem7229626)). Qed.
Lemma lem7229628 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : term132.
Proof. exact (EQ_MP (@lem7229627 _96871) (@lem7229509 _96871 m f g h1)). Qed.
Lemma lem7229630 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7229631 : term132 = term135.
Proof. exact (@lem7229630 term29 term62). Qed.
Lemma lem7229633 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229634 : term62 = term63.
Proof. exact (@lem7229633 term13). Qed.
Lemma lem7229636 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229637 : term29 = term59.
Proof. exact (@lem7229636 (NUMERAL 0)). Qed.
Lemma lem7229638 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7229639 : term31 = term136.
Proof. exact (MK_COMB (@lem7229638) (@lem7229637)). Qed.
Lemma lem7229640 : term135 = term137.
Proof. exact (MK_COMB (@lem7229639) (@lem7229634)). Qed.
Lemma lem7229641 : term138.
Proof. exact (@lem1980026 term29 term44 term62 term44). Qed.
Lemma lem7229643 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229644 : term110 = term111.
Proof. exact (@lem7229643 (NUMERAL 0) term13). Qed.
Lemma lem7229645 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229646 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229647 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229646 h1) (fun h1 : term111 = True => @lem7229645)). Qed.
Lemma lem7229648 : term111 = True.
Proof. exact (EQ_MP (@lem7229647) (@lem7229645)). Qed.
Lemma lem7229649 : term110 = True.
Proof. exact (TRANS (@lem7229644) (@lem7229648)). Qed.
Lemma lem7229650 : True = term110.
Proof. exact (SYM (@lem7229649)). Qed.
Lemma lem7229651 : term110.
Proof. exact (EQ_MP (@lem7229650) (@lem0)). Qed.
Lemma lem7229652 : term139.
Proof. exact (@lem7229641 (@lem7229651)). Qed.
Lemma lem7229654 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229655 : term110 = term111.
Proof. exact (@lem7229654 (NUMERAL 0) term13). Qed.
Lemma lem7229656 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229657 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229658 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229657 h1) (fun h1 : term111 = True => @lem7229656)). Qed.
Lemma lem7229659 : term111 = True.
Proof. exact (EQ_MP (@lem7229658) (@lem7229656)). Qed.
Lemma lem7229660 : term110 = True.
Proof. exact (TRANS (@lem7229655) (@lem7229659)). Qed.
Lemma lem7229661 : True = term110.
Proof. exact (SYM (@lem7229660)). Qed.
Lemma lem7229662 : term110.
Proof. exact (EQ_MP (@lem7229661) (@lem0)). Qed.
Lemma lem7229663 : term137 = term140.
Proof. exact (@lem7229652 (@lem7229662)). Qed.
Lemma lem7229665 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7229666 : term89 = term94.
Proof. exact (@lem7229665 term13 term13). Qed.
Lemma lem7229667 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229668 : term74 = term13.
Proof. exact (EQ_MP (@lem7229667) (@lem940073)). Qed.
Lemma lem7229669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229670 : term72 = term44.
Proof. exact (MK_COMB (@lem7229669) (@lem7229668)). Qed.
Lemma lem7229671 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7229672 : term94 = term62.
Proof. exact (MK_COMB (@lem7229671) (@lem7229670)). Qed.
Lemma lem7229673 : term89 = term62.
Proof. exact (TRANS (@lem7229666) (@lem7229672)). Qed.
Lemma lem7229675 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229676 : term122 = term29.
Proof. exact (@lem7229675 term13). Qed.
Lemma lem7229677 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7229678 : term141 = term31.
Proof. exact (MK_COMB (@lem7229677) (@lem7229676)). Qed.
Lemma lem7229679 : term140 = term135.
Proof. exact (MK_COMB (@lem7229678) (@lem7229673)). Qed.
Lemma lem7229681 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7229682 : term135 = term144.
Proof. exact (@lem7229681 (NUMERAL 0) term13). Qed.
Lemma lem7229683 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229684 (h1 : term112 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7229685 : (term112 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229684 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem7229683)). Qed.
Lemma lem7229686 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7229685) (@lem7229683)). Qed.
Lemma lem7229687 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7229688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7229689 : term145 = (and True).
Proof. exact (MK_COMB (@lem7229688) (@lem7229687)). Qed.
Lemma lem7229690 : term144 = (True /\ False).
Proof. exact (MK_COMB (@lem7229689) (@lem7229686)). Qed.
Lemma lem7229692 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7229693 : term144 = False.
Proof. exact (TRANS (@lem7229690) (@lem7229692)). Qed.
Lemma lem7229694 : term135 = False.
Proof. exact (TRANS (@lem7229682) (@lem7229693)). Qed.
Lemma lem7229695 : term140 = False.
Proof. exact (TRANS (@lem7229679) (@lem7229694)). Qed.
Lemma lem7229696 : term137 = False.
Proof. exact (TRANS (@lem7229663) (@lem7229695)). Qed.
Lemma lem7229697 : term135 = False.
Proof. exact (TRANS (@lem7229640) (@lem7229696)). Qed.
Lemma lem7229698 : term132 = False.
Proof. exact (TRANS (@lem7229631) (@lem7229697)). Qed.
Lemma lem7229699 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term671 _96871 m f g) : False.
Proof. exact (EQ_MP (@lem7229698) (@lem7229628 _96871 m f g h1)). Qed.
Lemma lem7229700 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term697 _96871 m f g.
Proof. exact (h1). Qed.
Lemma lem7229701 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term667 _96871 m f g.
Proof. exact (proj2 (@lem7229700 _96871 m f g h1)). Qed.
Lemma lem7229703 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term654 _96871 m f g.
Proof. exact (proj2 (@lem7229701 _96871 m f g h1)). Qed.
Lemma lem7229704 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term570 _96871.
Proof. exact (proj1 (@lem7229701 _96871 m f g h1)). Qed.
Lemma lem7229706 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term586 _96871.
Proof. exact (proj1 (@lem7229703 _96871 m f g h1)). Qed.
Lemma lem7229708 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7229709 : term672 = term110.
Proof. exact (@lem7229708 term29 term44). Qed.
Lemma lem7229711 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229712 : term44 = term88.
Proof. exact (@lem7229711 term13). Qed.
Lemma lem7229714 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229715 : term29 = term59.
Proof. exact (@lem7229714 (NUMERAL 0)). Qed.
Lemma lem7229716 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7229717 : term479 = term480.
Proof. exact (MK_COMB (@lem7229716) (@lem7229715)). Qed.
Lemma lem7229718 : term110 = term673.
Proof. exact (MK_COMB (@lem7229717) (@lem7229712)). Qed.
Lemma lem7229719 : term674.
Proof. exact (@lem1980255 term29 term44 term44 term44). Qed.
Lemma lem7229721 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229722 : term110 = term111.
Proof. exact (@lem7229721 (NUMERAL 0) term13). Qed.
Lemma lem7229723 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229724 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229725 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229724 h1) (fun h1 : term111 = True => @lem7229723)). Qed.
Lemma lem7229726 : term111 = True.
Proof. exact (EQ_MP (@lem7229725) (@lem7229723)). Qed.
Lemma lem7229727 : term110 = True.
Proof. exact (TRANS (@lem7229722) (@lem7229726)). Qed.
Lemma lem7229728 : True = term110.
Proof. exact (SYM (@lem7229727)). Qed.
Lemma lem7229729 : term110.
Proof. exact (EQ_MP (@lem7229728) (@lem0)). Qed.
Lemma lem7229730 : term675.
Proof. exact (@lem7229719 (@lem7229729)). Qed.
Lemma lem7229732 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229733 : term110 = term111.
Proof. exact (@lem7229732 (NUMERAL 0) term13). Qed.
Lemma lem7229734 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229735 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229736 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229735 h1) (fun h1 : term111 = True => @lem7229734)). Qed.
Lemma lem7229737 : term111 = True.
Proof. exact (EQ_MP (@lem7229736) (@lem7229734)). Qed.
Lemma lem7229738 : term110 = True.
Proof. exact (TRANS (@lem7229733) (@lem7229737)). Qed.
Lemma lem7229739 : True = term110.
Proof. exact (SYM (@lem7229738)). Qed.
Lemma lem7229740 : term110.
Proof. exact (EQ_MP (@lem7229739) (@lem0)). Qed.
Lemma lem7229741 : term673 = term676.
Proof. exact (@lem7229730 (@lem7229740)). Qed.
Lemma lem7229743 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229744 : term71 = term72.
Proof. exact (@lem7229743 term13 term13). Qed.
Lemma lem7229745 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229746 : term74 = term13.
Proof. exact (EQ_MP (@lem7229745) (@lem940073)). Qed.
Lemma lem7229747 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229748 : term72 = term44.
Proof. exact (MK_COMB (@lem7229747) (@lem7229746)). Qed.
Lemma lem7229749 : term71 = term44.
Proof. exact (TRANS (@lem7229744) (@lem7229748)). Qed.
Lemma lem7229751 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229752 : term122 = term29.
Proof. exact (@lem7229751 term13). Qed.
Lemma lem7229753 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7229754 : term485 = term479.
Proof. exact (MK_COMB (@lem7229753) (@lem7229752)). Qed.
Lemma lem7229755 : term676 = term110.
Proof. exact (MK_COMB (@lem7229754) (@lem7229749)). Qed.
Lemma lem7229757 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229758 : term110 = term111.
Proof. exact (@lem7229757 (NUMERAL 0) term13). Qed.
Lemma lem7229759 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229760 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229761 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229760 h1) (fun h1 : term111 = True => @lem7229759)). Qed.
Lemma lem7229762 : term111 = True.
Proof. exact (EQ_MP (@lem7229761) (@lem7229759)). Qed.
Lemma lem7229763 : term110 = True.
Proof. exact (TRANS (@lem7229758) (@lem7229762)). Qed.
Lemma lem7229764 : term676 = True.
Proof. exact (TRANS (@lem7229755) (@lem7229763)). Qed.
Lemma lem7229765 : term673 = True.
Proof. exact (TRANS (@lem7229741) (@lem7229764)). Qed.
Lemma lem7229766 : term110 = True.
Proof. exact (TRANS (@lem7229718) (@lem7229765)). Qed.
Lemma lem7229767 : term672 = True.
Proof. exact (TRANS (@lem7229709) (@lem7229766)). Qed.
Lemma lem7229768 : True = term672.
Proof. exact (SYM (@lem7229767)). Qed.
Lemma lem7229769 : term672.
Proof. exact (EQ_MP (@lem7229768) (@lem0)). Qed.
Lemma lem7229770 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term698 _96871.
Proof. exact (conj (@lem7229769) (@lem7229706 _96871 m f g h1)). Qed.
Lemma lem7229772 (x : real) (y : real) : term678 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7229773 (_96871 : int) : term699 _96871.
Proof. exact (@lem7229772 term44 (term583 _96871)). Qed.
Lemma lem7229774 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term700 _96871.
Proof. exact (@lem7229773 _96871 (@lem7229770 _96871 m f g h1)). Qed.
Lemma lem7229775 (_96871 : int) : (term701 _96871) = (term583 _96871).
Proof. exact (@lem1982733 (term583 _96871)). Qed.
Lemma lem7229776 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7229777 (_96871 : int) : (term702 _96871) = (term585 _96871).
Proof. exact (MK_COMB (@lem7229776) (@lem7229775 _96871)). Qed.
Lemma lem7229778 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229779 (_96871 : int) : (term700 _96871) = (term586 _96871).
Proof. exact (MK_COMB (@lem7229777 _96871) (@lem7229778)). Qed.
Lemma lem7229780 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term586 _96871.
Proof. exact (EQ_MP (@lem7229779 _96871) (@lem7229774 _96871 m f g h1)). Qed.
Lemma lem7229782 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7229783 : term672 = term110.
Proof. exact (@lem7229782 term29 term44). Qed.
Lemma lem7229785 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229786 : term44 = term88.
Proof. exact (@lem7229785 term13). Qed.
Lemma lem7229788 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229789 : term29 = term59.
Proof. exact (@lem7229788 (NUMERAL 0)). Qed.
Lemma lem7229790 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7229791 : term479 = term480.
Proof. exact (MK_COMB (@lem7229790) (@lem7229789)). Qed.
Lemma lem7229792 : term110 = term673.
Proof. exact (MK_COMB (@lem7229791) (@lem7229786)). Qed.
Lemma lem7229793 : term674.
Proof. exact (@lem1980255 term29 term44 term44 term44). Qed.
Lemma lem7229795 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229796 : term110 = term111.
Proof. exact (@lem7229795 (NUMERAL 0) term13). Qed.
Lemma lem7229797 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229798 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229799 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229798 h1) (fun h1 : term111 = True => @lem7229797)). Qed.
Lemma lem7229800 : term111 = True.
Proof. exact (EQ_MP (@lem7229799) (@lem7229797)). Qed.
Lemma lem7229801 : term110 = True.
Proof. exact (TRANS (@lem7229796) (@lem7229800)). Qed.
Lemma lem7229802 : True = term110.
Proof. exact (SYM (@lem7229801)). Qed.
Lemma lem7229803 : term110.
Proof. exact (EQ_MP (@lem7229802) (@lem0)). Qed.
Lemma lem7229804 : term675.
Proof. exact (@lem7229793 (@lem7229803)). Qed.
Lemma lem7229806 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229807 : term110 = term111.
Proof. exact (@lem7229806 (NUMERAL 0) term13). Qed.
Lemma lem7229808 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229809 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229810 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229809 h1) (fun h1 : term111 = True => @lem7229808)). Qed.
Lemma lem7229811 : term111 = True.
Proof. exact (EQ_MP (@lem7229810) (@lem7229808)). Qed.
Lemma lem7229812 : term110 = True.
Proof. exact (TRANS (@lem7229807) (@lem7229811)). Qed.
Lemma lem7229813 : True = term110.
Proof. exact (SYM (@lem7229812)). Qed.
Lemma lem7229814 : term110.
Proof. exact (EQ_MP (@lem7229813) (@lem0)). Qed.
Lemma lem7229815 : term673 = term676.
Proof. exact (@lem7229804 (@lem7229814)). Qed.
Lemma lem7229817 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229818 : term71 = term72.
Proof. exact (@lem7229817 term13 term13). Qed.
Lemma lem7229819 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229820 : term74 = term13.
Proof. exact (EQ_MP (@lem7229819) (@lem940073)). Qed.
Lemma lem7229821 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229822 : term72 = term44.
Proof. exact (MK_COMB (@lem7229821) (@lem7229820)). Qed.
Lemma lem7229823 : term71 = term44.
Proof. exact (TRANS (@lem7229818) (@lem7229822)). Qed.
Lemma lem7229825 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229826 : term122 = term29.
Proof. exact (@lem7229825 term13). Qed.
Lemma lem7229827 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7229828 : term485 = term479.
Proof. exact (MK_COMB (@lem7229827) (@lem7229826)). Qed.
Lemma lem7229829 : term676 = term110.
Proof. exact (MK_COMB (@lem7229828) (@lem7229823)). Qed.
Lemma lem7229831 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229832 : term110 = term111.
Proof. exact (@lem7229831 (NUMERAL 0) term13). Qed.
Lemma lem7229833 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229834 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229835 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229834 h1) (fun h1 : term111 = True => @lem7229833)). Qed.
Lemma lem7229836 : term111 = True.
Proof. exact (EQ_MP (@lem7229835) (@lem7229833)). Qed.
Lemma lem7229837 : term110 = True.
Proof. exact (TRANS (@lem7229832) (@lem7229836)). Qed.
Lemma lem7229838 : term676 = True.
Proof. exact (TRANS (@lem7229829) (@lem7229837)). Qed.
Lemma lem7229839 : term673 = True.
Proof. exact (TRANS (@lem7229815) (@lem7229838)). Qed.
Lemma lem7229840 : term110 = True.
Proof. exact (TRANS (@lem7229792) (@lem7229839)). Qed.
Lemma lem7229841 : term672 = True.
Proof. exact (TRANS (@lem7229783) (@lem7229840)). Qed.
Lemma lem7229842 : True = term672.
Proof. exact (SYM (@lem7229841)). Qed.
Lemma lem7229843 : term672.
Proof. exact (EQ_MP (@lem7229842) (@lem0)). Qed.
Lemma lem7229844 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term703 _96871.
Proof. exact (conj (@lem7229843) (@lem7229704 _96871 m f g h1)). Qed.
Lemma lem7229846 (x : real) (y : real) : term678 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7229847 (_96871 : int) : term704 _96871.
Proof. exact (@lem7229846 term44 (term101 _96871)). Qed.
Lemma lem7229848 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term705 _96871.
Proof. exact (@lem7229847 _96871 (@lem7229844 _96871 m f g h1)). Qed.
Lemma lem7229849 (_96871 : int) : (term706 _96871) = (term101 _96871).
Proof. exact (@lem1982733 (term101 _96871)). Qed.
Lemma lem7229850 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7229851 (_96871 : int) : (term707 _96871) = (term569 _96871).
Proof. exact (MK_COMB (@lem7229850) (@lem7229849 _96871)). Qed.
Lemma lem7229852 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229853 (_96871 : int) : (term705 _96871) = (term570 _96871).
Proof. exact (MK_COMB (@lem7229851 _96871) (@lem7229852)). Qed.
Lemma lem7229854 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term570 _96871.
Proof. exact (EQ_MP (@lem7229853 _96871) (@lem7229848 _96871 m f g h1)). Qed.
Lemma lem7229855 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term708 _96871.
Proof. exact (conj (@lem7229854 _96871 m f g h1) (@lem7229780 _96871 m f g h1)). Qed.
Lemma lem7229857 (x : real) (y : real) : term689 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7229858 (_96871 : int) : term709 _96871.
Proof. exact (@lem7229857 (term101 _96871) (term583 _96871)). Qed.
Lemma lem7229859 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term710 _96871.
Proof. exact (@lem7229858 _96871 (@lem7229855 _96871 m f g h1)). Qed.
Lemma lem7229860 (_96871 : int) : (term711 _96871) = (term693 _96871).
Proof. exact (@lem1982763 (term101 _96871) (real_of_int _96871) term62). Qed.
Lemma lem7229861 (_96871 : int) : (term694 _96871) = (term103 _96871).
Proof. exact (@lem1982713 term62 (real_of_int _96871)). Qed.
Lemma lem7229863 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229864 : term44 = term88.
Proof. exact (@lem7229863 term13). Qed.
Lemma lem7229866 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229867 : term62 = term63.
Proof. exact (@lem7229866 term13). Qed.
Lemma lem7229868 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7229869 : term104 = term105.
Proof. exact (MK_COMB (@lem7229868) (@lem7229867)). Qed.
Lemma lem7229870 : term106 = term107.
Proof. exact (MK_COMB (@lem7229869) (@lem7229864)). Qed.
Lemma lem7229871 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7229873 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229874 : term110 = term111.
Proof. exact (@lem7229873 (NUMERAL 0) term13). Qed.
Lemma lem7229875 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229876 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229877 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229876 h1) (fun h1 : term111 = True => @lem7229875)). Qed.
Lemma lem7229878 : term111 = True.
Proof. exact (EQ_MP (@lem7229877) (@lem7229875)). Qed.
Lemma lem7229879 : term110 = True.
Proof. exact (TRANS (@lem7229874) (@lem7229878)). Qed.
Lemma lem7229880 : True = term110.
Proof. exact (SYM (@lem7229879)). Qed.
Lemma lem7229881 : term110.
Proof. exact (EQ_MP (@lem7229880) (@lem0)). Qed.
Lemma lem7229882 : term113.
Proof. exact (@lem7229871 (@lem7229881)). Qed.
Lemma lem7229884 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229885 : term110 = term111.
Proof. exact (@lem7229884 (NUMERAL 0) term13). Qed.
Lemma lem7229886 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229887 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229888 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229887 h1) (fun h1 : term111 = True => @lem7229886)). Qed.
Lemma lem7229889 : term111 = True.
Proof. exact (EQ_MP (@lem7229888) (@lem7229886)). Qed.
Lemma lem7229890 : term110 = True.
Proof. exact (TRANS (@lem7229885) (@lem7229889)). Qed.
Lemma lem7229891 : True = term110.
Proof. exact (SYM (@lem7229890)). Qed.
Lemma lem7229892 : term110.
Proof. exact (EQ_MP (@lem7229891) (@lem0)). Qed.
Lemma lem7229893 : term114.
Proof. exact (@lem7229882 (@lem7229892)). Qed.
Lemma lem7229895 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229896 : term110 = term111.
Proof. exact (@lem7229895 (NUMERAL 0) term13). Qed.
Lemma lem7229897 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229898 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229899 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229898 h1) (fun h1 : term111 = True => @lem7229897)). Qed.
Lemma lem7229900 : term111 = True.
Proof. exact (EQ_MP (@lem7229899) (@lem7229897)). Qed.
Lemma lem7229901 : term110 = True.
Proof. exact (TRANS (@lem7229896) (@lem7229900)). Qed.
Lemma lem7229902 : True = term110.
Proof. exact (SYM (@lem7229901)). Qed.
Lemma lem7229903 : term110.
Proof. exact (EQ_MP (@lem7229902) (@lem0)). Qed.
Lemma lem7229904 : term115.
Proof. exact (@lem7229893 (@lem7229903)). Qed.
Lemma lem7229906 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229907 : term71 = term72.
Proof. exact (@lem7229906 term13 term13). Qed.
Lemma lem7229908 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229909 : term74 = term13.
Proof. exact (EQ_MP (@lem7229908) (@lem940073)). Qed.
Lemma lem7229910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229911 : term72 = term44.
Proof. exact (MK_COMB (@lem7229910) (@lem7229909)). Qed.
Lemma lem7229912 : term71 = term44.
Proof. exact (TRANS (@lem7229907) (@lem7229911)). Qed.
Lemma lem7229914 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7229915 : term89 = term94.
Proof. exact (@lem7229914 term13 term13). Qed.
Lemma lem7229916 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229917 : term74 = term13.
Proof. exact (EQ_MP (@lem7229916) (@lem940073)). Qed.
Lemma lem7229918 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229919 : term72 = term44.
Proof. exact (MK_COMB (@lem7229918) (@lem7229917)). Qed.
Lemma lem7229920 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7229921 : term94 = term62.
Proof. exact (MK_COMB (@lem7229920) (@lem7229919)). Qed.
Lemma lem7229922 : term89 = term62.
Proof. exact (TRANS (@lem7229915) (@lem7229921)). Qed.
Lemma lem7229923 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7229924 : term116 = term104.
Proof. exact (MK_COMB (@lem7229923) (@lem7229922)). Qed.
Lemma lem7229925 : term117 = term106.
Proof. exact (MK_COMB (@lem7229924) (@lem7229912)). Qed.
Lemma lem7229927 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7229928 : term106 = term29.
Proof. exact (@lem7229927 term13). Qed.
Lemma lem7229929 : term117 = term29.
Proof. exact (TRANS (@lem7229925) (@lem7229928)). Qed.
Lemma lem7229930 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229931 : term119 = term120.
Proof. exact (MK_COMB (@lem7229930) (@lem7229929)). Qed.
Lemma lem7229932 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7229933 : term121 = term122.
Proof. exact (MK_COMB (@lem7229931) (@lem7229932)). Qed.
Lemma lem7229935 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229936 : term122 = term29.
Proof. exact (@lem7229935 term13). Qed.
Lemma lem7229937 : term121 = term29.
Proof. exact (TRANS (@lem7229933) (@lem7229936)). Qed.
Lemma lem7229939 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7229940 : term71 = term72.
Proof. exact (@lem7229939 term13 term13). Qed.
Lemma lem7229941 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7229942 : term74 = term13.
Proof. exact (EQ_MP (@lem7229941) (@lem940073)). Qed.
Lemma lem7229943 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7229944 : term72 = term44.
Proof. exact (MK_COMB (@lem7229943) (@lem7229942)). Qed.
Lemma lem7229945 : term71 = term44.
Proof. exact (TRANS (@lem7229940) (@lem7229944)). Qed.
Lemma lem7229946 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7229947 : term124 = term122.
Proof. exact (MK_COMB (@lem7229946) (@lem7229945)). Qed.
Lemma lem7229949 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7229950 : term122 = term29.
Proof. exact (@lem7229949 term13). Qed.
Lemma lem7229951 : term124 = term29.
Proof. exact (TRANS (@lem7229947) (@lem7229950)). Qed.
Lemma lem7229952 : term29 = term124.
Proof. exact (SYM (@lem7229951)). Qed.
Lemma lem7229953 : term121 = term124.
Proof. exact (TRANS (@lem7229937) (@lem7229952)). Qed.
Lemma lem7229954 : term107 = term59.
Proof. exact (@lem7229904 (@lem7229953)). Qed.
Lemma lem7229955 : term106 = term59.
Proof. exact (TRANS (@lem7229870) (@lem7229954)). Qed.
Lemma lem7229957 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7229958 : term59 = term29.
Proof. exact (@lem7229957 term29). Qed.
Lemma lem7229959 : term106 = term29.
Proof. exact (TRANS (@lem7229955) (@lem7229958)). Qed.
Lemma lem7229960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7229961 : term125 = term120.
Proof. exact (MK_COMB (@lem7229960) (@lem7229959)). Qed.
Lemma lem7229962 (_96871 : int) : (real_of_int _96871) = (real_of_int _96871).
Proof. exact (eq_refl (real_of_int _96871)). Qed.
Lemma lem7229963 (_96871 : int) : (term103 _96871) = (term126 _96871).
Proof. exact (MK_COMB (@lem7229961) (@lem7229962 _96871)). Qed.
Lemma lem7229964 (_96871 : int) : (term694 _96871) = (term126 _96871).
Proof. exact (TRANS (@lem7229861 _96871) (@lem7229963 _96871)). Qed.
Lemma lem7229965 (_96871 : int) : (term126 _96871) = term29.
Proof. exact (@lem1982719 (real_of_int _96871)). Qed.
Lemma lem7229966 (_96871 : int) : (term694 _96871) = term29.
Proof. exact (TRANS (@lem7229964 _96871) (@lem7229965 _96871)). Qed.
Lemma lem7229967 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7229968 (_96871 : int) : (term695 _96871) = term128.
Proof. exact (MK_COMB (@lem7229967) (@lem7229966 _96871)). Qed.
Lemma lem7229969 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem7229970 (_96871 : int) : (term693 _96871) = term129.
Proof. exact (MK_COMB (@lem7229968 _96871) (@lem7229969)). Qed.
Lemma lem7229971 (_96871 : int) : (term711 _96871) = term129.
Proof. exact (TRANS (@lem7229860 _96871) (@lem7229970 _96871)). Qed.
Lemma lem7229972 : term129 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem7229973 (_96871 : int) : (term711 _96871) = term62.
Proof. exact (TRANS (@lem7229971 _96871) (@lem7229972)). Qed.
Lemma lem7229974 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7229975 (_96871 : int) : (term712 _96871) = term131.
Proof. exact (MK_COMB (@lem7229974) (@lem7229973 _96871)). Qed.
Lemma lem7229976 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7229977 (_96871 : int) : (term710 _96871) = term132.
Proof. exact (MK_COMB (@lem7229975 _96871) (@lem7229976)). Qed.
Lemma lem7229978 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : term132.
Proof. exact (EQ_MP (@lem7229977 _96871) (@lem7229859 _96871 m f g h1)). Qed.
Lemma lem7229980 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7229981 : term132 = term135.
Proof. exact (@lem7229980 term29 term62). Qed.
Lemma lem7229983 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7229984 : term62 = term63.
Proof. exact (@lem7229983 term13). Qed.
Lemma lem7229986 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7229987 : term29 = term59.
Proof. exact (@lem7229986 (NUMERAL 0)). Qed.
Lemma lem7229988 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7229989 : term31 = term136.
Proof. exact (MK_COMB (@lem7229988) (@lem7229987)). Qed.
Lemma lem7229990 : term135 = term137.
Proof. exact (MK_COMB (@lem7229989) (@lem7229984)). Qed.
Lemma lem7229991 : term138.
Proof. exact (@lem1980026 term29 term44 term62 term44). Qed.
Lemma lem7229993 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7229994 : term110 = term111.
Proof. exact (@lem7229993 (NUMERAL 0) term13). Qed.
Lemma lem7229995 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7229996 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7229997 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7229996 h1) (fun h1 : term111 = True => @lem7229995)). Qed.
Lemma lem7229998 : term111 = True.
Proof. exact (EQ_MP (@lem7229997) (@lem7229995)). Qed.
Lemma lem7229999 : term110 = True.
Proof. exact (TRANS (@lem7229994) (@lem7229998)). Qed.
Lemma lem7230000 : True = term110.
Proof. exact (SYM (@lem7229999)). Qed.
Lemma lem7230001 : term110.
Proof. exact (EQ_MP (@lem7230000) (@lem0)). Qed.
Lemma lem7230002 : term139.
Proof. exact (@lem7229991 (@lem7230001)). Qed.
Lemma lem7230004 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230005 : term110 = term111.
Proof. exact (@lem7230004 (NUMERAL 0) term13). Qed.
Lemma lem7230006 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230007 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230008 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230007 h1) (fun h1 : term111 = True => @lem7230006)). Qed.
Lemma lem7230009 : term111 = True.
Proof. exact (EQ_MP (@lem7230008) (@lem7230006)). Qed.
Lemma lem7230010 : term110 = True.
Proof. exact (TRANS (@lem7230005) (@lem7230009)). Qed.
Lemma lem7230011 : True = term110.
Proof. exact (SYM (@lem7230010)). Qed.
Lemma lem7230012 : term110.
Proof. exact (EQ_MP (@lem7230011) (@lem0)). Qed.
Lemma lem7230013 : term137 = term140.
Proof. exact (@lem7230002 (@lem7230012)). Qed.
Lemma lem7230015 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7230016 : term89 = term94.
Proof. exact (@lem7230015 term13 term13). Qed.
Lemma lem7230017 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230018 : term74 = term13.
Proof. exact (EQ_MP (@lem7230017) (@lem940073)). Qed.
Lemma lem7230019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230020 : term72 = term44.
Proof. exact (MK_COMB (@lem7230019) (@lem7230018)). Qed.
Lemma lem7230021 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7230022 : term94 = term62.
Proof. exact (MK_COMB (@lem7230021) (@lem7230020)). Qed.
Lemma lem7230023 : term89 = term62.
Proof. exact (TRANS (@lem7230016) (@lem7230022)). Qed.
Lemma lem7230025 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230026 : term122 = term29.
Proof. exact (@lem7230025 term13). Qed.
Lemma lem7230027 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7230028 : term141 = term31.
Proof. exact (MK_COMB (@lem7230027) (@lem7230026)). Qed.
Lemma lem7230029 : term140 = term135.
Proof. exact (MK_COMB (@lem7230028) (@lem7230023)). Qed.
Lemma lem7230031 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7230032 : term135 = term144.
Proof. exact (@lem7230031 (NUMERAL 0) term13). Qed.
Lemma lem7230033 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230034 (h1 : term112 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7230035 : (term112 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230034 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem7230033)). Qed.
Lemma lem7230036 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7230035) (@lem7230033)). Qed.
Lemma lem7230037 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7230038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7230039 : term145 = (and True).
Proof. exact (MK_COMB (@lem7230038) (@lem7230037)). Qed.
Lemma lem7230040 : term144 = (True /\ False).
Proof. exact (MK_COMB (@lem7230039) (@lem7230036)). Qed.
Lemma lem7230042 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7230043 : term144 = False.
Proof. exact (TRANS (@lem7230040) (@lem7230042)). Qed.
Lemma lem7230044 : term135 = False.
Proof. exact (TRANS (@lem7230032) (@lem7230043)). Qed.
Lemma lem7230045 : term140 = False.
Proof. exact (TRANS (@lem7230029) (@lem7230044)). Qed.
Lemma lem7230046 : term137 = False.
Proof. exact (TRANS (@lem7230013) (@lem7230045)). Qed.
Lemma lem7230047 : term135 = False.
Proof. exact (TRANS (@lem7229990) (@lem7230046)). Qed.
Lemma lem7230048 : term132 = False.
Proof. exact (TRANS (@lem7229981) (@lem7230047)). Qed.
Lemma lem7230049 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term697 _96871 m f g) : False.
Proof. exact (EQ_MP (@lem7230048) (@lem7229978 _96871 m f g h1)). Qed.
Lemma lem7230050 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term665 _96871 m f g) : False.
Proof. exact (or_elim (@lem7229349 _96871 m f g h1) (fun h0 : term671 _96871 m f g => @lem7229699 _96871 m f g h0) (fun h0 : term697 _96871 m f g => @lem7230049 _96871 m f g h0)). Qed.
Lemma lem7230051 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term661 _96871 m f g) : term661 _96871 m f g.
Proof. exact (h1). Qed.
Lemma lem7230052 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term713 _96871 m f g.
Proof. exact (h1). Qed.
Lemma lem7230053 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term662 _96871 m f g.
Proof. exact (proj2 (@lem7230052 _96871 m f g h1)). Qed.
Lemma lem7230054 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term82 _96871.
Proof. exact (proj1 (@lem7230052 _96871 m f g h1)). Qed.
Lemma lem7230055 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term649 _96871 m f g.
Proof. exact (proj2 (@lem7230053 _96871 m f g h1)). Qed.
Lemma lem7230058 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term577 _96871.
Proof. exact (proj1 (@lem7230055 _96871 m f g h1)). Qed.
Lemma lem7230060 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7230061 : term672 = term110.
Proof. exact (@lem7230060 term29 term44). Qed.
Lemma lem7230063 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230064 : term44 = term88.
Proof. exact (@lem7230063 term13). Qed.
Lemma lem7230066 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230067 : term29 = term59.
Proof. exact (@lem7230066 (NUMERAL 0)). Qed.
Lemma lem7230068 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7230069 : term479 = term480.
Proof. exact (MK_COMB (@lem7230068) (@lem7230067)). Qed.
Lemma lem7230070 : term110 = term673.
Proof. exact (MK_COMB (@lem7230069) (@lem7230064)). Qed.
Lemma lem7230071 : term674.
Proof. exact (@lem1980255 term29 term44 term44 term44). Qed.
Lemma lem7230073 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230074 : term110 = term111.
Proof. exact (@lem7230073 (NUMERAL 0) term13). Qed.
Lemma lem7230075 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230076 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230077 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230076 h1) (fun h1 : term111 = True => @lem7230075)). Qed.
Lemma lem7230078 : term111 = True.
Proof. exact (EQ_MP (@lem7230077) (@lem7230075)). Qed.
Lemma lem7230079 : term110 = True.
Proof. exact (TRANS (@lem7230074) (@lem7230078)). Qed.
Lemma lem7230080 : True = term110.
Proof. exact (SYM (@lem7230079)). Qed.
Lemma lem7230081 : term110.
Proof. exact (EQ_MP (@lem7230080) (@lem0)). Qed.
Lemma lem7230082 : term675.
Proof. exact (@lem7230071 (@lem7230081)). Qed.
Lemma lem7230084 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230085 : term110 = term111.
Proof. exact (@lem7230084 (NUMERAL 0) term13). Qed.
Lemma lem7230086 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230087 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230088 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230087 h1) (fun h1 : term111 = True => @lem7230086)). Qed.
Lemma lem7230089 : term111 = True.
Proof. exact (EQ_MP (@lem7230088) (@lem7230086)). Qed.
Lemma lem7230090 : term110 = True.
Proof. exact (TRANS (@lem7230085) (@lem7230089)). Qed.
Lemma lem7230091 : True = term110.
Proof. exact (SYM (@lem7230090)). Qed.
Lemma lem7230092 : term110.
Proof. exact (EQ_MP (@lem7230091) (@lem0)). Qed.
Lemma lem7230093 : term673 = term676.
Proof. exact (@lem7230082 (@lem7230092)). Qed.
Lemma lem7230095 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7230096 : term71 = term72.
Proof. exact (@lem7230095 term13 term13). Qed.
Lemma lem7230097 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230098 : term74 = term13.
Proof. exact (EQ_MP (@lem7230097) (@lem940073)). Qed.
Lemma lem7230099 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230100 : term72 = term44.
Proof. exact (MK_COMB (@lem7230099) (@lem7230098)). Qed.
Lemma lem7230101 : term71 = term44.
Proof. exact (TRANS (@lem7230096) (@lem7230100)). Qed.
Lemma lem7230103 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230104 : term122 = term29.
Proof. exact (@lem7230103 term13). Qed.
Lemma lem7230105 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7230106 : term485 = term479.
Proof. exact (MK_COMB (@lem7230105) (@lem7230104)). Qed.
Lemma lem7230107 : term676 = term110.
Proof. exact (MK_COMB (@lem7230106) (@lem7230101)). Qed.
Lemma lem7230109 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230110 : term110 = term111.
Proof. exact (@lem7230109 (NUMERAL 0) term13). Qed.
Lemma lem7230111 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230112 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230113 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230112 h1) (fun h1 : term111 = True => @lem7230111)). Qed.
Lemma lem7230114 : term111 = True.
Proof. exact (EQ_MP (@lem7230113) (@lem7230111)). Qed.
Lemma lem7230115 : term110 = True.
Proof. exact (TRANS (@lem7230110) (@lem7230114)). Qed.
Lemma lem7230116 : term676 = True.
Proof. exact (TRANS (@lem7230107) (@lem7230115)). Qed.
Lemma lem7230117 : term673 = True.
Proof. exact (TRANS (@lem7230093) (@lem7230116)). Qed.
Lemma lem7230118 : term110 = True.
Proof. exact (TRANS (@lem7230070) (@lem7230117)). Qed.
Lemma lem7230119 : term672 = True.
Proof. exact (TRANS (@lem7230061) (@lem7230118)). Qed.
Lemma lem7230120 : True = term672.
Proof. exact (SYM (@lem7230119)). Qed.
Lemma lem7230121 : term672.
Proof. exact (EQ_MP (@lem7230120) (@lem0)). Qed.
Lemma lem7230122 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term677 _96871.
Proof. exact (conj (@lem7230121) (@lem7230054 _96871 m f g h1)). Qed.
Lemma lem7230124 (x : real) (y : real) : term678 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7230125 (_96871 : int) : term679 _96871.
Proof. exact (@lem7230124 term44 (real_of_int _96871)). Qed.
Lemma lem7230126 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term680 _96871.
Proof. exact (@lem7230125 _96871 (@lem7230122 _96871 m f g h1)). Qed.
Lemma lem7230127 (_96871 : int) : (term681 _96871) = (real_of_int _96871).
Proof. exact (@lem1982733 (real_of_int _96871)). Qed.
Lemma lem7230128 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7230129 (_96871 : int) : (term682 _96871) = (term81 _96871).
Proof. exact (MK_COMB (@lem7230128) (@lem7230127 _96871)). Qed.
Lemma lem7230130 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7230131 (_96871 : int) : (term680 _96871) = (term82 _96871).
Proof. exact (MK_COMB (@lem7230129 _96871) (@lem7230130)). Qed.
Lemma lem7230132 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term82 _96871.
Proof. exact (EQ_MP (@lem7230131 _96871) (@lem7230126 _96871 m f g h1)). Qed.
Lemma lem7230134 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7230135 : term672 = term110.
Proof. exact (@lem7230134 term29 term44). Qed.
Lemma lem7230137 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230138 : term44 = term88.
Proof. exact (@lem7230137 term13). Qed.
Lemma lem7230140 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230141 : term29 = term59.
Proof. exact (@lem7230140 (NUMERAL 0)). Qed.
Lemma lem7230142 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7230143 : term479 = term480.
Proof. exact (MK_COMB (@lem7230142) (@lem7230141)). Qed.
Lemma lem7230144 : term110 = term673.
Proof. exact (MK_COMB (@lem7230143) (@lem7230138)). Qed.
Lemma lem7230145 : term674.
Proof. exact (@lem1980255 term29 term44 term44 term44). Qed.
Lemma lem7230147 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230148 : term110 = term111.
Proof. exact (@lem7230147 (NUMERAL 0) term13). Qed.
Lemma lem7230149 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230150 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230151 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230150 h1) (fun h1 : term111 = True => @lem7230149)). Qed.
Lemma lem7230152 : term111 = True.
Proof. exact (EQ_MP (@lem7230151) (@lem7230149)). Qed.
Lemma lem7230153 : term110 = True.
Proof. exact (TRANS (@lem7230148) (@lem7230152)). Qed.
Lemma lem7230154 : True = term110.
Proof. exact (SYM (@lem7230153)). Qed.
Lemma lem7230155 : term110.
Proof. exact (EQ_MP (@lem7230154) (@lem0)). Qed.
Lemma lem7230156 : term675.
Proof. exact (@lem7230145 (@lem7230155)). Qed.
Lemma lem7230158 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230159 : term110 = term111.
Proof. exact (@lem7230158 (NUMERAL 0) term13). Qed.
Lemma lem7230160 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230161 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230162 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230161 h1) (fun h1 : term111 = True => @lem7230160)). Qed.
Lemma lem7230163 : term111 = True.
Proof. exact (EQ_MP (@lem7230162) (@lem7230160)). Qed.
Lemma lem7230164 : term110 = True.
Proof. exact (TRANS (@lem7230159) (@lem7230163)). Qed.
Lemma lem7230165 : True = term110.
Proof. exact (SYM (@lem7230164)). Qed.
Lemma lem7230166 : term110.
Proof. exact (EQ_MP (@lem7230165) (@lem0)). Qed.
Lemma lem7230167 : term673 = term676.
Proof. exact (@lem7230156 (@lem7230166)). Qed.
Lemma lem7230169 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7230170 : term71 = term72.
Proof. exact (@lem7230169 term13 term13). Qed.
Lemma lem7230171 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230172 : term74 = term13.
Proof. exact (EQ_MP (@lem7230171) (@lem940073)). Qed.
Lemma lem7230173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230174 : term72 = term44.
Proof. exact (MK_COMB (@lem7230173) (@lem7230172)). Qed.
Lemma lem7230175 : term71 = term44.
Proof. exact (TRANS (@lem7230170) (@lem7230174)). Qed.
Lemma lem7230177 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230178 : term122 = term29.
Proof. exact (@lem7230177 term13). Qed.
Lemma lem7230179 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7230180 : term485 = term479.
Proof. exact (MK_COMB (@lem7230179) (@lem7230178)). Qed.
Lemma lem7230181 : term676 = term110.
Proof. exact (MK_COMB (@lem7230180) (@lem7230175)). Qed.
Lemma lem7230183 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230184 : term110 = term111.
Proof. exact (@lem7230183 (NUMERAL 0) term13). Qed.
Lemma lem7230185 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230186 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230187 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230186 h1) (fun h1 : term111 = True => @lem7230185)). Qed.
Lemma lem7230188 : term111 = True.
Proof. exact (EQ_MP (@lem7230187) (@lem7230185)). Qed.
Lemma lem7230189 : term110 = True.
Proof. exact (TRANS (@lem7230184) (@lem7230188)). Qed.
Lemma lem7230190 : term676 = True.
Proof. exact (TRANS (@lem7230181) (@lem7230189)). Qed.
Lemma lem7230191 : term673 = True.
Proof. exact (TRANS (@lem7230167) (@lem7230190)). Qed.
Lemma lem7230192 : term110 = True.
Proof. exact (TRANS (@lem7230144) (@lem7230191)). Qed.
Lemma lem7230193 : term672 = True.
Proof. exact (TRANS (@lem7230135) (@lem7230192)). Qed.
Lemma lem7230194 : True = term672.
Proof. exact (SYM (@lem7230193)). Qed.
Lemma lem7230195 : term672.
Proof. exact (EQ_MP (@lem7230194) (@lem0)). Qed.
Lemma lem7230196 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term683 _96871.
Proof. exact (conj (@lem7230195) (@lem7230058 _96871 m f g h1)). Qed.
Lemma lem7230198 (x : real) (y : real) : term678 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7230199 (_96871 : int) : term684 _96871.
Proof. exact (@lem7230198 term44 (term98 _96871)). Qed.
Lemma lem7230200 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term685 _96871.
Proof. exact (@lem7230199 _96871 (@lem7230196 _96871 m f g h1)). Qed.
Lemma lem7230201 (_96871 : int) : (term686 _96871) = (term98 _96871).
Proof. exact (@lem1982733 (term98 _96871)). Qed.
Lemma lem7230202 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7230203 (_96871 : int) : (term687 _96871) = (term576 _96871).
Proof. exact (MK_COMB (@lem7230202) (@lem7230201 _96871)). Qed.
Lemma lem7230204 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7230205 (_96871 : int) : (term685 _96871) = (term577 _96871).
Proof. exact (MK_COMB (@lem7230203 _96871) (@lem7230204)). Qed.
Lemma lem7230206 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term577 _96871.
Proof. exact (EQ_MP (@lem7230205 _96871) (@lem7230200 _96871 m f g h1)). Qed.
Lemma lem7230207 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term688 _96871.
Proof. exact (conj (@lem7230206 _96871 m f g h1) (@lem7230132 _96871 m f g h1)). Qed.
Lemma lem7230209 (x : real) (y : real) : term689 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7230210 (_96871 : int) : term690 _96871.
Proof. exact (@lem7230209 (term98 _96871) (real_of_int _96871)). Qed.
Lemma lem7230211 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term691 _96871.
Proof. exact (@lem7230210 _96871 (@lem7230207 _96871 m f g h1)). Qed.
Lemma lem7230212 (_96871 : int) : (term692 _96871) = (term693 _96871).
Proof. exact (@lem1982759 (term101 _96871) (real_of_int _96871) term62). Qed.
Lemma lem7230213 (_96871 : int) : (term694 _96871) = (term103 _96871).
Proof. exact (@lem1982713 term62 (real_of_int _96871)). Qed.
Lemma lem7230215 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230216 : term44 = term88.
Proof. exact (@lem7230215 term13). Qed.
Lemma lem7230218 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7230219 : term62 = term63.
Proof. exact (@lem7230218 term13). Qed.
Lemma lem7230220 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7230221 : term104 = term105.
Proof. exact (MK_COMB (@lem7230220) (@lem7230219)). Qed.
Lemma lem7230222 : term106 = term107.
Proof. exact (MK_COMB (@lem7230221) (@lem7230216)). Qed.
Lemma lem7230223 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7230225 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230226 : term110 = term111.
Proof. exact (@lem7230225 (NUMERAL 0) term13). Qed.
Lemma lem7230227 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230228 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230229 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230228 h1) (fun h1 : term111 = True => @lem7230227)). Qed.
Lemma lem7230230 : term111 = True.
Proof. exact (EQ_MP (@lem7230229) (@lem7230227)). Qed.
Lemma lem7230231 : term110 = True.
Proof. exact (TRANS (@lem7230226) (@lem7230230)). Qed.
Lemma lem7230232 : True = term110.
Proof. exact (SYM (@lem7230231)). Qed.
Lemma lem7230233 : term110.
Proof. exact (EQ_MP (@lem7230232) (@lem0)). Qed.
Lemma lem7230234 : term113.
Proof. exact (@lem7230223 (@lem7230233)). Qed.
Lemma lem7230236 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230237 : term110 = term111.
Proof. exact (@lem7230236 (NUMERAL 0) term13). Qed.
Lemma lem7230238 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230239 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230240 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230239 h1) (fun h1 : term111 = True => @lem7230238)). Qed.
Lemma lem7230241 : term111 = True.
Proof. exact (EQ_MP (@lem7230240) (@lem7230238)). Qed.
Lemma lem7230242 : term110 = True.
Proof. exact (TRANS (@lem7230237) (@lem7230241)). Qed.
Lemma lem7230243 : True = term110.
Proof. exact (SYM (@lem7230242)). Qed.
Lemma lem7230244 : term110.
Proof. exact (EQ_MP (@lem7230243) (@lem0)). Qed.
Lemma lem7230245 : term114.
Proof. exact (@lem7230234 (@lem7230244)). Qed.
Lemma lem7230247 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230248 : term110 = term111.
Proof. exact (@lem7230247 (NUMERAL 0) term13). Qed.
Lemma lem7230249 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230250 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230251 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230250 h1) (fun h1 : term111 = True => @lem7230249)). Qed.
Lemma lem7230252 : term111 = True.
Proof. exact (EQ_MP (@lem7230251) (@lem7230249)). Qed.
Lemma lem7230253 : term110 = True.
Proof. exact (TRANS (@lem7230248) (@lem7230252)). Qed.
Lemma lem7230254 : True = term110.
Proof. exact (SYM (@lem7230253)). Qed.
Lemma lem7230255 : term110.
Proof. exact (EQ_MP (@lem7230254) (@lem0)). Qed.
Lemma lem7230256 : term115.
Proof. exact (@lem7230245 (@lem7230255)). Qed.
Lemma lem7230258 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7230259 : term71 = term72.
Proof. exact (@lem7230258 term13 term13). Qed.
Lemma lem7230260 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230261 : term74 = term13.
Proof. exact (EQ_MP (@lem7230260) (@lem940073)). Qed.
Lemma lem7230262 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230263 : term72 = term44.
Proof. exact (MK_COMB (@lem7230262) (@lem7230261)). Qed.
Lemma lem7230264 : term71 = term44.
Proof. exact (TRANS (@lem7230259) (@lem7230263)). Qed.
Lemma lem7230266 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7230267 : term89 = term94.
Proof. exact (@lem7230266 term13 term13). Qed.
Lemma lem7230268 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230269 : term74 = term13.
Proof. exact (EQ_MP (@lem7230268) (@lem940073)). Qed.
Lemma lem7230270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230271 : term72 = term44.
Proof. exact (MK_COMB (@lem7230270) (@lem7230269)). Qed.
Lemma lem7230272 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7230273 : term94 = term62.
Proof. exact (MK_COMB (@lem7230272) (@lem7230271)). Qed.
Lemma lem7230274 : term89 = term62.
Proof. exact (TRANS (@lem7230267) (@lem7230273)). Qed.
Lemma lem7230275 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7230276 : term116 = term104.
Proof. exact (MK_COMB (@lem7230275) (@lem7230274)). Qed.
Lemma lem7230277 : term117 = term106.
Proof. exact (MK_COMB (@lem7230276) (@lem7230264)). Qed.
Lemma lem7230279 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7230280 : term106 = term29.
Proof. exact (@lem7230279 term13). Qed.
Lemma lem7230281 : term117 = term29.
Proof. exact (TRANS (@lem7230277) (@lem7230280)). Qed.
Lemma lem7230282 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7230283 : term119 = term120.
Proof. exact (MK_COMB (@lem7230282) (@lem7230281)). Qed.
Lemma lem7230284 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7230285 : term121 = term122.
Proof. exact (MK_COMB (@lem7230283) (@lem7230284)). Qed.
Lemma lem7230287 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230288 : term122 = term29.
Proof. exact (@lem7230287 term13). Qed.
Lemma lem7230289 : term121 = term29.
Proof. exact (TRANS (@lem7230285) (@lem7230288)). Qed.
Lemma lem7230291 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7230292 : term71 = term72.
Proof. exact (@lem7230291 term13 term13). Qed.
Lemma lem7230293 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230294 : term74 = term13.
Proof. exact (EQ_MP (@lem7230293) (@lem940073)). Qed.
Lemma lem7230295 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230296 : term72 = term44.
Proof. exact (MK_COMB (@lem7230295) (@lem7230294)). Qed.
Lemma lem7230297 : term71 = term44.
Proof. exact (TRANS (@lem7230292) (@lem7230296)). Qed.
Lemma lem7230298 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7230299 : term124 = term122.
Proof. exact (MK_COMB (@lem7230298) (@lem7230297)). Qed.
Lemma lem7230301 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230302 : term122 = term29.
Proof. exact (@lem7230301 term13). Qed.
Lemma lem7230303 : term124 = term29.
Proof. exact (TRANS (@lem7230299) (@lem7230302)). Qed.
Lemma lem7230304 : term29 = term124.
Proof. exact (SYM (@lem7230303)). Qed.
Lemma lem7230305 : term121 = term124.
Proof. exact (TRANS (@lem7230289) (@lem7230304)). Qed.
Lemma lem7230306 : term107 = term59.
Proof. exact (@lem7230256 (@lem7230305)). Qed.
Lemma lem7230307 : term106 = term59.
Proof. exact (TRANS (@lem7230222) (@lem7230306)). Qed.
Lemma lem7230309 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7230310 : term59 = term29.
Proof. exact (@lem7230309 term29). Qed.
Lemma lem7230311 : term106 = term29.
Proof. exact (TRANS (@lem7230307) (@lem7230310)). Qed.
Lemma lem7230312 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7230313 : term125 = term120.
Proof. exact (MK_COMB (@lem7230312) (@lem7230311)). Qed.
Lemma lem7230314 (_96871 : int) : (real_of_int _96871) = (real_of_int _96871).
Proof. exact (eq_refl (real_of_int _96871)). Qed.
Lemma lem7230315 (_96871 : int) : (term103 _96871) = (term126 _96871).
Proof. exact (MK_COMB (@lem7230313) (@lem7230314 _96871)). Qed.
Lemma lem7230316 (_96871 : int) : (term694 _96871) = (term126 _96871).
Proof. exact (TRANS (@lem7230213 _96871) (@lem7230315 _96871)). Qed.
Lemma lem7230317 (_96871 : int) : (term126 _96871) = term29.
Proof. exact (@lem1982719 (real_of_int _96871)). Qed.
Lemma lem7230318 (_96871 : int) : (term694 _96871) = term29.
Proof. exact (TRANS (@lem7230316 _96871) (@lem7230317 _96871)). Qed.
Lemma lem7230319 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7230320 (_96871 : int) : (term695 _96871) = term128.
Proof. exact (MK_COMB (@lem7230319) (@lem7230318 _96871)). Qed.
Lemma lem7230321 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem7230322 (_96871 : int) : (term693 _96871) = term129.
Proof. exact (MK_COMB (@lem7230320 _96871) (@lem7230321)). Qed.
Lemma lem7230323 (_96871 : int) : (term692 _96871) = term129.
Proof. exact (TRANS (@lem7230212 _96871) (@lem7230322 _96871)). Qed.
Lemma lem7230324 : term129 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem7230325 (_96871 : int) : (term692 _96871) = term62.
Proof. exact (TRANS (@lem7230323 _96871) (@lem7230324)). Qed.
Lemma lem7230326 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7230327 (_96871 : int) : (term696 _96871) = term131.
Proof. exact (MK_COMB (@lem7230326) (@lem7230325 _96871)). Qed.
Lemma lem7230328 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7230329 (_96871 : int) : (term691 _96871) = term132.
Proof. exact (MK_COMB (@lem7230327 _96871) (@lem7230328)). Qed.
Lemma lem7230330 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : term132.
Proof. exact (EQ_MP (@lem7230329 _96871) (@lem7230211 _96871 m f g h1)). Qed.
Lemma lem7230332 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7230333 : term132 = term135.
Proof. exact (@lem7230332 term29 term62). Qed.
Lemma lem7230335 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7230336 : term62 = term63.
Proof. exact (@lem7230335 term13). Qed.
Lemma lem7230338 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230339 : term29 = term59.
Proof. exact (@lem7230338 (NUMERAL 0)). Qed.
Lemma lem7230340 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7230341 : term31 = term136.
Proof. exact (MK_COMB (@lem7230340) (@lem7230339)). Qed.
Lemma lem7230342 : term135 = term137.
Proof. exact (MK_COMB (@lem7230341) (@lem7230336)). Qed.
Lemma lem7230343 : term138.
Proof. exact (@lem1980026 term29 term44 term62 term44). Qed.
Lemma lem7230345 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230346 : term110 = term111.
Proof. exact (@lem7230345 (NUMERAL 0) term13). Qed.
Lemma lem7230347 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230348 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230349 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230348 h1) (fun h1 : term111 = True => @lem7230347)). Qed.
Lemma lem7230350 : term111 = True.
Proof. exact (EQ_MP (@lem7230349) (@lem7230347)). Qed.
Lemma lem7230351 : term110 = True.
Proof. exact (TRANS (@lem7230346) (@lem7230350)). Qed.
Lemma lem7230352 : True = term110.
Proof. exact (SYM (@lem7230351)). Qed.
Lemma lem7230353 : term110.
Proof. exact (EQ_MP (@lem7230352) (@lem0)). Qed.
Lemma lem7230354 : term139.
Proof. exact (@lem7230343 (@lem7230353)). Qed.
Lemma lem7230356 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230357 : term110 = term111.
Proof. exact (@lem7230356 (NUMERAL 0) term13). Qed.
Lemma lem7230358 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230359 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230360 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230359 h1) (fun h1 : term111 = True => @lem7230358)). Qed.
Lemma lem7230361 : term111 = True.
Proof. exact (EQ_MP (@lem7230360) (@lem7230358)). Qed.
Lemma lem7230362 : term110 = True.
Proof. exact (TRANS (@lem7230357) (@lem7230361)). Qed.
Lemma lem7230363 : True = term110.
Proof. exact (SYM (@lem7230362)). Qed.
Lemma lem7230364 : term110.
Proof. exact (EQ_MP (@lem7230363) (@lem0)). Qed.
Lemma lem7230365 : term137 = term140.
Proof. exact (@lem7230354 (@lem7230364)). Qed.
Lemma lem7230367 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7230368 : term89 = term94.
Proof. exact (@lem7230367 term13 term13). Qed.
Lemma lem7230369 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230370 : term74 = term13.
Proof. exact (EQ_MP (@lem7230369) (@lem940073)). Qed.
Lemma lem7230371 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230372 : term72 = term44.
Proof. exact (MK_COMB (@lem7230371) (@lem7230370)). Qed.
Lemma lem7230373 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7230374 : term94 = term62.
Proof. exact (MK_COMB (@lem7230373) (@lem7230372)). Qed.
Lemma lem7230375 : term89 = term62.
Proof. exact (TRANS (@lem7230368) (@lem7230374)). Qed.
Lemma lem7230377 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230378 : term122 = term29.
Proof. exact (@lem7230377 term13). Qed.
Lemma lem7230379 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7230380 : term141 = term31.
Proof. exact (MK_COMB (@lem7230379) (@lem7230378)). Qed.
Lemma lem7230381 : term140 = term135.
Proof. exact (MK_COMB (@lem7230380) (@lem7230375)). Qed.
Lemma lem7230383 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7230384 : term135 = term144.
Proof. exact (@lem7230383 (NUMERAL 0) term13). Qed.
Lemma lem7230385 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230386 (h1 : term112 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7230387 : (term112 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230386 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem7230385)). Qed.
Lemma lem7230388 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7230387) (@lem7230385)). Qed.
Lemma lem7230389 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7230390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7230391 : term145 = (and True).
Proof. exact (MK_COMB (@lem7230390) (@lem7230389)). Qed.
Lemma lem7230392 : term144 = (True /\ False).
Proof. exact (MK_COMB (@lem7230391) (@lem7230388)). Qed.
Lemma lem7230394 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7230395 : term144 = False.
Proof. exact (TRANS (@lem7230392) (@lem7230394)). Qed.
Lemma lem7230396 : term135 = False.
Proof. exact (TRANS (@lem7230384) (@lem7230395)). Qed.
Lemma lem7230397 : term140 = False.
Proof. exact (TRANS (@lem7230381) (@lem7230396)). Qed.
Lemma lem7230398 : term137 = False.
Proof. exact (TRANS (@lem7230365) (@lem7230397)). Qed.
Lemma lem7230399 : term135 = False.
Proof. exact (TRANS (@lem7230342) (@lem7230398)). Qed.
Lemma lem7230400 : term132 = False.
Proof. exact (TRANS (@lem7230333) (@lem7230399)). Qed.
Lemma lem7230401 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term713 _96871 m f g) : False.
Proof. exact (EQ_MP (@lem7230400) (@lem7230330 _96871 m f g h1)). Qed.
Lemma lem7230402 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term714 _96871 m f g.
Proof. exact (h1). Qed.
Lemma lem7230403 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term663 _96871 m f g.
Proof. exact (proj2 (@lem7230402 _96871 m f g h1)). Qed.
Lemma lem7230405 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term650 _96871 m f g.
Proof. exact (proj2 (@lem7230403 _96871 m f g h1)). Qed.
Lemma lem7230406 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term570 _96871.
Proof. exact (proj1 (@lem7230403 _96871 m f g h1)). Qed.
Lemma lem7230408 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term586 _96871.
Proof. exact (proj1 (@lem7230405 _96871 m f g h1)). Qed.
Lemma lem7230410 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7230411 : term672 = term110.
Proof. exact (@lem7230410 term29 term44). Qed.
Lemma lem7230413 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230414 : term44 = term88.
Proof. exact (@lem7230413 term13). Qed.
Lemma lem7230416 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230417 : term29 = term59.
Proof. exact (@lem7230416 (NUMERAL 0)). Qed.
Lemma lem7230418 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7230419 : term479 = term480.
Proof. exact (MK_COMB (@lem7230418) (@lem7230417)). Qed.
Lemma lem7230420 : term110 = term673.
Proof. exact (MK_COMB (@lem7230419) (@lem7230414)). Qed.
Lemma lem7230421 : term674.
Proof. exact (@lem1980255 term29 term44 term44 term44). Qed.
Lemma lem7230423 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230424 : term110 = term111.
Proof. exact (@lem7230423 (NUMERAL 0) term13). Qed.
Lemma lem7230425 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230426 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230427 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230426 h1) (fun h1 : term111 = True => @lem7230425)). Qed.
Lemma lem7230428 : term111 = True.
Proof. exact (EQ_MP (@lem7230427) (@lem7230425)). Qed.
Lemma lem7230429 : term110 = True.
Proof. exact (TRANS (@lem7230424) (@lem7230428)). Qed.
Lemma lem7230430 : True = term110.
Proof. exact (SYM (@lem7230429)). Qed.
Lemma lem7230431 : term110.
Proof. exact (EQ_MP (@lem7230430) (@lem0)). Qed.
Lemma lem7230432 : term675.
Proof. exact (@lem7230421 (@lem7230431)). Qed.
Lemma lem7230434 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230435 : term110 = term111.
Proof. exact (@lem7230434 (NUMERAL 0) term13). Qed.
Lemma lem7230436 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230437 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230438 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230437 h1) (fun h1 : term111 = True => @lem7230436)). Qed.
Lemma lem7230439 : term111 = True.
Proof. exact (EQ_MP (@lem7230438) (@lem7230436)). Qed.
Lemma lem7230440 : term110 = True.
Proof. exact (TRANS (@lem7230435) (@lem7230439)). Qed.
Lemma lem7230441 : True = term110.
Proof. exact (SYM (@lem7230440)). Qed.
Lemma lem7230442 : term110.
Proof. exact (EQ_MP (@lem7230441) (@lem0)). Qed.
Lemma lem7230443 : term673 = term676.
Proof. exact (@lem7230432 (@lem7230442)). Qed.
Lemma lem7230445 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7230446 : term71 = term72.
Proof. exact (@lem7230445 term13 term13). Qed.
Lemma lem7230447 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230448 : term74 = term13.
Proof. exact (EQ_MP (@lem7230447) (@lem940073)). Qed.
Lemma lem7230449 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230450 : term72 = term44.
Proof. exact (MK_COMB (@lem7230449) (@lem7230448)). Qed.
Lemma lem7230451 : term71 = term44.
Proof. exact (TRANS (@lem7230446) (@lem7230450)). Qed.
Lemma lem7230453 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230454 : term122 = term29.
Proof. exact (@lem7230453 term13). Qed.
Lemma lem7230455 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7230456 : term485 = term479.
Proof. exact (MK_COMB (@lem7230455) (@lem7230454)). Qed.
Lemma lem7230457 : term676 = term110.
Proof. exact (MK_COMB (@lem7230456) (@lem7230451)). Qed.
Lemma lem7230459 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230460 : term110 = term111.
Proof. exact (@lem7230459 (NUMERAL 0) term13). Qed.
Lemma lem7230461 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230462 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230463 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230462 h1) (fun h1 : term111 = True => @lem7230461)). Qed.
Lemma lem7230464 : term111 = True.
Proof. exact (EQ_MP (@lem7230463) (@lem7230461)). Qed.
Lemma lem7230465 : term110 = True.
Proof. exact (TRANS (@lem7230460) (@lem7230464)). Qed.
Lemma lem7230466 : term676 = True.
Proof. exact (TRANS (@lem7230457) (@lem7230465)). Qed.
Lemma lem7230467 : term673 = True.
Proof. exact (TRANS (@lem7230443) (@lem7230466)). Qed.
Lemma lem7230468 : term110 = True.
Proof. exact (TRANS (@lem7230420) (@lem7230467)). Qed.
Lemma lem7230469 : term672 = True.
Proof. exact (TRANS (@lem7230411) (@lem7230468)). Qed.
Lemma lem7230470 : True = term672.
Proof. exact (SYM (@lem7230469)). Qed.
Lemma lem7230471 : term672.
Proof. exact (EQ_MP (@lem7230470) (@lem0)). Qed.
Lemma lem7230472 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term698 _96871.
Proof. exact (conj (@lem7230471) (@lem7230408 _96871 m f g h1)). Qed.
Lemma lem7230474 (x : real) (y : real) : term678 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7230475 (_96871 : int) : term699 _96871.
Proof. exact (@lem7230474 term44 (term583 _96871)). Qed.
Lemma lem7230476 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term700 _96871.
Proof. exact (@lem7230475 _96871 (@lem7230472 _96871 m f g h1)). Qed.
Lemma lem7230477 (_96871 : int) : (term701 _96871) = (term583 _96871).
Proof. exact (@lem1982733 (term583 _96871)). Qed.
Lemma lem7230478 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7230479 (_96871 : int) : (term702 _96871) = (term585 _96871).
Proof. exact (MK_COMB (@lem7230478) (@lem7230477 _96871)). Qed.
Lemma lem7230480 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7230481 (_96871 : int) : (term700 _96871) = (term586 _96871).
Proof. exact (MK_COMB (@lem7230479 _96871) (@lem7230480)). Qed.
Lemma lem7230482 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term586 _96871.
Proof. exact (EQ_MP (@lem7230481 _96871) (@lem7230476 _96871 m f g h1)). Qed.
Lemma lem7230484 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7230485 : term672 = term110.
Proof. exact (@lem7230484 term29 term44). Qed.
Lemma lem7230487 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230488 : term44 = term88.
Proof. exact (@lem7230487 term13). Qed.
Lemma lem7230490 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230491 : term29 = term59.
Proof. exact (@lem7230490 (NUMERAL 0)). Qed.
Lemma lem7230492 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7230493 : term479 = term480.
Proof. exact (MK_COMB (@lem7230492) (@lem7230491)). Qed.
Lemma lem7230494 : term110 = term673.
Proof. exact (MK_COMB (@lem7230493) (@lem7230488)). Qed.
Lemma lem7230495 : term674.
Proof. exact (@lem1980255 term29 term44 term44 term44). Qed.
Lemma lem7230497 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230498 : term110 = term111.
Proof. exact (@lem7230497 (NUMERAL 0) term13). Qed.
Lemma lem7230499 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230500 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230501 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230500 h1) (fun h1 : term111 = True => @lem7230499)). Qed.
Lemma lem7230502 : term111 = True.
Proof. exact (EQ_MP (@lem7230501) (@lem7230499)). Qed.
Lemma lem7230503 : term110 = True.
Proof. exact (TRANS (@lem7230498) (@lem7230502)). Qed.
Lemma lem7230504 : True = term110.
Proof. exact (SYM (@lem7230503)). Qed.
Lemma lem7230505 : term110.
Proof. exact (EQ_MP (@lem7230504) (@lem0)). Qed.
Lemma lem7230506 : term675.
Proof. exact (@lem7230495 (@lem7230505)). Qed.
Lemma lem7230508 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230509 : term110 = term111.
Proof. exact (@lem7230508 (NUMERAL 0) term13). Qed.
Lemma lem7230510 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230511 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230512 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230511 h1) (fun h1 : term111 = True => @lem7230510)). Qed.
Lemma lem7230513 : term111 = True.
Proof. exact (EQ_MP (@lem7230512) (@lem7230510)). Qed.
Lemma lem7230514 : term110 = True.
Proof. exact (TRANS (@lem7230509) (@lem7230513)). Qed.
Lemma lem7230515 : True = term110.
Proof. exact (SYM (@lem7230514)). Qed.
Lemma lem7230516 : term110.
Proof. exact (EQ_MP (@lem7230515) (@lem0)). Qed.
Lemma lem7230517 : term673 = term676.
Proof. exact (@lem7230506 (@lem7230516)). Qed.
Lemma lem7230519 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7230520 : term71 = term72.
Proof. exact (@lem7230519 term13 term13). Qed.
Lemma lem7230521 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230522 : term74 = term13.
Proof. exact (EQ_MP (@lem7230521) (@lem940073)). Qed.
Lemma lem7230523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230524 : term72 = term44.
Proof. exact (MK_COMB (@lem7230523) (@lem7230522)). Qed.
Lemma lem7230525 : term71 = term44.
Proof. exact (TRANS (@lem7230520) (@lem7230524)). Qed.
Lemma lem7230527 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230528 : term122 = term29.
Proof. exact (@lem7230527 term13). Qed.
Lemma lem7230529 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7230530 : term485 = term479.
Proof. exact (MK_COMB (@lem7230529) (@lem7230528)). Qed.
Lemma lem7230531 : term676 = term110.
Proof. exact (MK_COMB (@lem7230530) (@lem7230525)). Qed.
Lemma lem7230533 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230534 : term110 = term111.
Proof. exact (@lem7230533 (NUMERAL 0) term13). Qed.
Lemma lem7230535 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230536 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230537 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230536 h1) (fun h1 : term111 = True => @lem7230535)). Qed.
Lemma lem7230538 : term111 = True.
Proof. exact (EQ_MP (@lem7230537) (@lem7230535)). Qed.
Lemma lem7230539 : term110 = True.
Proof. exact (TRANS (@lem7230534) (@lem7230538)). Qed.
Lemma lem7230540 : term676 = True.
Proof. exact (TRANS (@lem7230531) (@lem7230539)). Qed.
Lemma lem7230541 : term673 = True.
Proof. exact (TRANS (@lem7230517) (@lem7230540)). Qed.
Lemma lem7230542 : term110 = True.
Proof. exact (TRANS (@lem7230494) (@lem7230541)). Qed.
Lemma lem7230543 : term672 = True.
Proof. exact (TRANS (@lem7230485) (@lem7230542)). Qed.
Lemma lem7230544 : True = term672.
Proof. exact (SYM (@lem7230543)). Qed.
Lemma lem7230545 : term672.
Proof. exact (EQ_MP (@lem7230544) (@lem0)). Qed.
Lemma lem7230546 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term703 _96871.
Proof. exact (conj (@lem7230545) (@lem7230406 _96871 m f g h1)). Qed.
Lemma lem7230548 (x : real) (y : real) : term678 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7230549 (_96871 : int) : term704 _96871.
Proof. exact (@lem7230548 term44 (term101 _96871)). Qed.
Lemma lem7230550 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term705 _96871.
Proof. exact (@lem7230549 _96871 (@lem7230546 _96871 m f g h1)). Qed.
Lemma lem7230551 (_96871 : int) : (term706 _96871) = (term101 _96871).
Proof. exact (@lem1982733 (term101 _96871)). Qed.
Lemma lem7230552 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7230553 (_96871 : int) : (term707 _96871) = (term569 _96871).
Proof. exact (MK_COMB (@lem7230552) (@lem7230551 _96871)). Qed.
Lemma lem7230554 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7230555 (_96871 : int) : (term705 _96871) = (term570 _96871).
Proof. exact (MK_COMB (@lem7230553 _96871) (@lem7230554)). Qed.
Lemma lem7230556 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term570 _96871.
Proof. exact (EQ_MP (@lem7230555 _96871) (@lem7230550 _96871 m f g h1)). Qed.
Lemma lem7230557 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term708 _96871.
Proof. exact (conj (@lem7230556 _96871 m f g h1) (@lem7230482 _96871 m f g h1)). Qed.
Lemma lem7230559 (x : real) (y : real) : term689 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7230560 (_96871 : int) : term709 _96871.
Proof. exact (@lem7230559 (term101 _96871) (term583 _96871)). Qed.
Lemma lem7230561 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term710 _96871.
Proof. exact (@lem7230560 _96871 (@lem7230557 _96871 m f g h1)). Qed.
Lemma lem7230562 (_96871 : int) : (term711 _96871) = (term693 _96871).
Proof. exact (@lem1982763 (term101 _96871) (real_of_int _96871) term62). Qed.
Lemma lem7230563 (_96871 : int) : (term694 _96871) = (term103 _96871).
Proof. exact (@lem1982713 term62 (real_of_int _96871)). Qed.
Lemma lem7230565 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230566 : term44 = term88.
Proof. exact (@lem7230565 term13). Qed.
Lemma lem7230568 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7230569 : term62 = term63.
Proof. exact (@lem7230568 term13). Qed.
Lemma lem7230570 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7230571 : term104 = term105.
Proof. exact (MK_COMB (@lem7230570) (@lem7230569)). Qed.
Lemma lem7230572 : term106 = term107.
Proof. exact (MK_COMB (@lem7230571) (@lem7230566)). Qed.
Lemma lem7230573 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7230575 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230576 : term110 = term111.
Proof. exact (@lem7230575 (NUMERAL 0) term13). Qed.
Lemma lem7230577 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230578 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230579 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230578 h1) (fun h1 : term111 = True => @lem7230577)). Qed.
Lemma lem7230580 : term111 = True.
Proof. exact (EQ_MP (@lem7230579) (@lem7230577)). Qed.
Lemma lem7230581 : term110 = True.
Proof. exact (TRANS (@lem7230576) (@lem7230580)). Qed.
Lemma lem7230582 : True = term110.
Proof. exact (SYM (@lem7230581)). Qed.
Lemma lem7230583 : term110.
Proof. exact (EQ_MP (@lem7230582) (@lem0)). Qed.
Lemma lem7230584 : term113.
Proof. exact (@lem7230573 (@lem7230583)). Qed.
Lemma lem7230586 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230587 : term110 = term111.
Proof. exact (@lem7230586 (NUMERAL 0) term13). Qed.
Lemma lem7230588 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230589 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230590 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230589 h1) (fun h1 : term111 = True => @lem7230588)). Qed.
Lemma lem7230591 : term111 = True.
Proof. exact (EQ_MP (@lem7230590) (@lem7230588)). Qed.
Lemma lem7230592 : term110 = True.
Proof. exact (TRANS (@lem7230587) (@lem7230591)). Qed.
Lemma lem7230593 : True = term110.
Proof. exact (SYM (@lem7230592)). Qed.
Lemma lem7230594 : term110.
Proof. exact (EQ_MP (@lem7230593) (@lem0)). Qed.
Lemma lem7230595 : term114.
Proof. exact (@lem7230584 (@lem7230594)). Qed.
Lemma lem7230597 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230598 : term110 = term111.
Proof. exact (@lem7230597 (NUMERAL 0) term13). Qed.
Lemma lem7230599 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230600 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230601 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230600 h1) (fun h1 : term111 = True => @lem7230599)). Qed.
Lemma lem7230602 : term111 = True.
Proof. exact (EQ_MP (@lem7230601) (@lem7230599)). Qed.
Lemma lem7230603 : term110 = True.
Proof. exact (TRANS (@lem7230598) (@lem7230602)). Qed.
Lemma lem7230604 : True = term110.
Proof. exact (SYM (@lem7230603)). Qed.
Lemma lem7230605 : term110.
Proof. exact (EQ_MP (@lem7230604) (@lem0)). Qed.
Lemma lem7230606 : term115.
Proof. exact (@lem7230595 (@lem7230605)). Qed.
Lemma lem7230608 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7230609 : term71 = term72.
Proof. exact (@lem7230608 term13 term13). Qed.
Lemma lem7230610 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230611 : term74 = term13.
Proof. exact (EQ_MP (@lem7230610) (@lem940073)). Qed.
Lemma lem7230612 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230613 : term72 = term44.
Proof. exact (MK_COMB (@lem7230612) (@lem7230611)). Qed.
Lemma lem7230614 : term71 = term44.
Proof. exact (TRANS (@lem7230609) (@lem7230613)). Qed.
Lemma lem7230616 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7230617 : term89 = term94.
Proof. exact (@lem7230616 term13 term13). Qed.
Lemma lem7230618 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230619 : term74 = term13.
Proof. exact (EQ_MP (@lem7230618) (@lem940073)). Qed.
Lemma lem7230620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230621 : term72 = term44.
Proof. exact (MK_COMB (@lem7230620) (@lem7230619)). Qed.
Lemma lem7230622 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7230623 : term94 = term62.
Proof. exact (MK_COMB (@lem7230622) (@lem7230621)). Qed.
Lemma lem7230624 : term89 = term62.
Proof. exact (TRANS (@lem7230617) (@lem7230623)). Qed.
Lemma lem7230625 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7230626 : term116 = term104.
Proof. exact (MK_COMB (@lem7230625) (@lem7230624)). Qed.
Lemma lem7230627 : term117 = term106.
Proof. exact (MK_COMB (@lem7230626) (@lem7230614)). Qed.
Lemma lem7230629 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7230630 : term106 = term29.
Proof. exact (@lem7230629 term13). Qed.
Lemma lem7230631 : term117 = term29.
Proof. exact (TRANS (@lem7230627) (@lem7230630)). Qed.
Lemma lem7230632 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7230633 : term119 = term120.
Proof. exact (MK_COMB (@lem7230632) (@lem7230631)). Qed.
Lemma lem7230634 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7230635 : term121 = term122.
Proof. exact (MK_COMB (@lem7230633) (@lem7230634)). Qed.
Lemma lem7230637 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230638 : term122 = term29.
Proof. exact (@lem7230637 term13). Qed.
Lemma lem7230639 : term121 = term29.
Proof. exact (TRANS (@lem7230635) (@lem7230638)). Qed.
Lemma lem7230641 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7230642 : term71 = term72.
Proof. exact (@lem7230641 term13 term13). Qed.
Lemma lem7230643 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230644 : term74 = term13.
Proof. exact (EQ_MP (@lem7230643) (@lem940073)). Qed.
Lemma lem7230645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230646 : term72 = term44.
Proof. exact (MK_COMB (@lem7230645) (@lem7230644)). Qed.
Lemma lem7230647 : term71 = term44.
Proof. exact (TRANS (@lem7230642) (@lem7230646)). Qed.
Lemma lem7230648 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7230649 : term124 = term122.
Proof. exact (MK_COMB (@lem7230648) (@lem7230647)). Qed.
Lemma lem7230651 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230652 : term122 = term29.
Proof. exact (@lem7230651 term13). Qed.
Lemma lem7230653 : term124 = term29.
Proof. exact (TRANS (@lem7230649) (@lem7230652)). Qed.
Lemma lem7230654 : term29 = term124.
Proof. exact (SYM (@lem7230653)). Qed.
Lemma lem7230655 : term121 = term124.
Proof. exact (TRANS (@lem7230639) (@lem7230654)). Qed.
Lemma lem7230656 : term107 = term59.
Proof. exact (@lem7230606 (@lem7230655)). Qed.
Lemma lem7230657 : term106 = term59.
Proof. exact (TRANS (@lem7230572) (@lem7230656)). Qed.
Lemma lem7230659 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7230660 : term59 = term29.
Proof. exact (@lem7230659 term29). Qed.
Lemma lem7230661 : term106 = term29.
Proof. exact (TRANS (@lem7230657) (@lem7230660)). Qed.
Lemma lem7230662 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7230663 : term125 = term120.
Proof. exact (MK_COMB (@lem7230662) (@lem7230661)). Qed.
Lemma lem7230664 (_96871 : int) : (real_of_int _96871) = (real_of_int _96871).
Proof. exact (eq_refl (real_of_int _96871)). Qed.
Lemma lem7230665 (_96871 : int) : (term103 _96871) = (term126 _96871).
Proof. exact (MK_COMB (@lem7230663) (@lem7230664 _96871)). Qed.
Lemma lem7230666 (_96871 : int) : (term694 _96871) = (term126 _96871).
Proof. exact (TRANS (@lem7230563 _96871) (@lem7230665 _96871)). Qed.
Lemma lem7230667 (_96871 : int) : (term126 _96871) = term29.
Proof. exact (@lem1982719 (real_of_int _96871)). Qed.
Lemma lem7230668 (_96871 : int) : (term694 _96871) = term29.
Proof. exact (TRANS (@lem7230666 _96871) (@lem7230667 _96871)). Qed.
Lemma lem7230669 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7230670 (_96871 : int) : (term695 _96871) = term128.
Proof. exact (MK_COMB (@lem7230669) (@lem7230668 _96871)). Qed.
Lemma lem7230671 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem7230672 (_96871 : int) : (term693 _96871) = term129.
Proof. exact (MK_COMB (@lem7230670 _96871) (@lem7230671)). Qed.
Lemma lem7230673 (_96871 : int) : (term711 _96871) = term129.
Proof. exact (TRANS (@lem7230562 _96871) (@lem7230672 _96871)). Qed.
Lemma lem7230674 : term129 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem7230675 (_96871 : int) : (term711 _96871) = term62.
Proof. exact (TRANS (@lem7230673 _96871) (@lem7230674)). Qed.
Lemma lem7230676 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7230677 (_96871 : int) : (term712 _96871) = term131.
Proof. exact (MK_COMB (@lem7230676) (@lem7230675 _96871)). Qed.
Lemma lem7230678 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7230679 (_96871 : int) : (term710 _96871) = term132.
Proof. exact (MK_COMB (@lem7230677 _96871) (@lem7230678)). Qed.
Lemma lem7230680 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : term132.
Proof. exact (EQ_MP (@lem7230679 _96871) (@lem7230561 _96871 m f g h1)). Qed.
Lemma lem7230682 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7230683 : term132 = term135.
Proof. exact (@lem7230682 term29 term62). Qed.
Lemma lem7230685 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7230686 : term62 = term63.
Proof. exact (@lem7230685 term13). Qed.
Lemma lem7230688 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7230689 : term29 = term59.
Proof. exact (@lem7230688 (NUMERAL 0)). Qed.
Lemma lem7230690 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7230691 : term31 = term136.
Proof. exact (MK_COMB (@lem7230690) (@lem7230689)). Qed.
Lemma lem7230692 : term135 = term137.
Proof. exact (MK_COMB (@lem7230691) (@lem7230686)). Qed.
Lemma lem7230693 : term138.
Proof. exact (@lem1980026 term29 term44 term62 term44). Qed.
Lemma lem7230695 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230696 : term110 = term111.
Proof. exact (@lem7230695 (NUMERAL 0) term13). Qed.
Lemma lem7230697 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230698 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230699 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230698 h1) (fun h1 : term111 = True => @lem7230697)). Qed.
Lemma lem7230700 : term111 = True.
Proof. exact (EQ_MP (@lem7230699) (@lem7230697)). Qed.
Lemma lem7230701 : term110 = True.
Proof. exact (TRANS (@lem7230696) (@lem7230700)). Qed.
Lemma lem7230702 : True = term110.
Proof. exact (SYM (@lem7230701)). Qed.
Lemma lem7230703 : term110.
Proof. exact (EQ_MP (@lem7230702) (@lem0)). Qed.
Lemma lem7230704 : term139.
Proof. exact (@lem7230693 (@lem7230703)). Qed.
Lemma lem7230706 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7230707 : term110 = term111.
Proof. exact (@lem7230706 (NUMERAL 0) term13). Qed.
Lemma lem7230708 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230709 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7230710 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230709 h1) (fun h1 : term111 = True => @lem7230708)). Qed.
Lemma lem7230711 : term111 = True.
Proof. exact (EQ_MP (@lem7230710) (@lem7230708)). Qed.
Lemma lem7230712 : term110 = True.
Proof. exact (TRANS (@lem7230707) (@lem7230711)). Qed.
Lemma lem7230713 : True = term110.
Proof. exact (SYM (@lem7230712)). Qed.
Lemma lem7230714 : term110.
Proof. exact (EQ_MP (@lem7230713) (@lem0)). Qed.
Lemma lem7230715 : term137 = term140.
Proof. exact (@lem7230704 (@lem7230714)). Qed.
Lemma lem7230717 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7230718 : term89 = term94.
Proof. exact (@lem7230717 term13 term13). Qed.
Lemma lem7230719 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7230720 : term74 = term13.
Proof. exact (EQ_MP (@lem7230719) (@lem940073)). Qed.
Lemma lem7230721 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7230722 : term72 = term44.
Proof. exact (MK_COMB (@lem7230721) (@lem7230720)). Qed.
Lemma lem7230723 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7230724 : term94 = term62.
Proof. exact (MK_COMB (@lem7230723) (@lem7230722)). Qed.
Lemma lem7230725 : term89 = term62.
Proof. exact (TRANS (@lem7230718) (@lem7230724)). Qed.
Lemma lem7230727 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7230728 : term122 = term29.
Proof. exact (@lem7230727 term13). Qed.
Lemma lem7230729 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7230730 : term141 = term31.
Proof. exact (MK_COMB (@lem7230729) (@lem7230728)). Qed.
Lemma lem7230731 : term140 = term135.
Proof. exact (MK_COMB (@lem7230730) (@lem7230725)). Qed.
Lemma lem7230733 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7230734 : term135 = term144.
Proof. exact (@lem7230733 (NUMERAL 0) term13). Qed.
Lemma lem7230735 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7230736 (h1 : term112 = (BIT1 0)) : (term13 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7230737 : (term112 = (BIT1 0)) = ((term13 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7230736 h1) (fun h1 : (term13 = (NUMERAL 0)) = False => @lem7230735)). Qed.
Lemma lem7230738 : (term13 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7230737) (@lem7230735)). Qed.
Lemma lem7230739 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7230740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7230741 : term145 = (and True).
Proof. exact (MK_COMB (@lem7230740) (@lem7230739)). Qed.
Lemma lem7230742 : term144 = (True /\ False).
Proof. exact (MK_COMB (@lem7230741) (@lem7230738)). Qed.
Lemma lem7230744 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7230745 : term144 = False.
Proof. exact (TRANS (@lem7230742) (@lem7230744)). Qed.
Lemma lem7230746 : term135 = False.
Proof. exact (TRANS (@lem7230734) (@lem7230745)). Qed.
Lemma lem7230747 : term140 = False.
Proof. exact (TRANS (@lem7230731) (@lem7230746)). Qed.
Lemma lem7230748 : term137 = False.
Proof. exact (TRANS (@lem7230715) (@lem7230747)). Qed.
Lemma lem7230749 : term135 = False.
Proof. exact (TRANS (@lem7230692) (@lem7230748)). Qed.
Lemma lem7230750 : term132 = False.
Proof. exact (TRANS (@lem7230683) (@lem7230749)). Qed.
Lemma lem7230751 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term714 _96871 m f g) : False.
Proof. exact (EQ_MP (@lem7230750) (@lem7230680 _96871 m f g h1)). Qed.
Lemma lem7230752 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term661 _96871 m f g) : False.
Proof. exact (or_elim (@lem7230051 _96871 m f g h1) (fun h0 : term713 _96871 m f g => @lem7230401 _96871 m f g h0) (fun h0 : term714 _96871 m f g => @lem7230751 _96871 m f g h0)). Qed.
Lemma lem7230753 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term670 _96871 m f g) : False.
Proof. exact (or_elim (@lem7229348 _96871 m f g h1) (fun h0 : term665 _96871 m f g => @lem7230050 _96871 m f g h0) (fun h0 : term661 _96871 m f g => @lem7230752 _96871 m f g h0)). Qed.
Lemma lem7230755 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term670 _96871 m f g) : term670 _96871 m f g.
Proof. exact (h1). Qed.
Lemma lem7230756 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term670 _96871 m f g) : (term670 _96871 m f g) = False.
Proof. exact (prop_ext (fun h2 : term670 _96871 m f g => @lem7230753 _96871 m f g h1) (fun h2 : False => @lem7230755 _96871 m f g h1)). Qed.
Lemma lem7230757 (_96871 : int) (m : nat) (f : nat -> real) (g : nat -> real) (h1 : term670 _96871 m f g) : False.
Proof. exact (EQ_MP (@lem7230756 _96871 m f g h1) (@lem7230755 _96871 m f g h1)). Qed.
Lemma lem7230758 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term564 _96871 f g m) : term564 _96871 f g m.
Proof. exact (h1). Qed.
Lemma lem7230759 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term564 _96871 f g m) : term670 _96871 m f g.
Proof. exact (EQ_MP (@lem7229326 _96871 m f g) (@lem7230758 _96871 f g m h1)). Qed.
Lemma lem7230760 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term564 _96871 f g m) : (term670 _96871 m f g) = False.
Proof. exact (prop_ext (fun h2 : term670 _96871 m f g => @lem7230757 _96871 m f g h2) (fun h2 : False => @lem7230759 _96871 f g m h1)). Qed.
Lemma lem7230761 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term564 _96871 f g m) : False.
Proof. exact (EQ_MP (@lem7230760 _96871 f g m h1) (@lem7230759 _96871 f g m h1)). Qed.
Lemma lem7230762 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : term715 _96871 f g m.
Proof. exact (fun h0 : term564 _96871 f g m => @lem7230761 _96871 f g m h0). Qed.
Lemma lem7230763 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : term716 _96871 f g m.
Proof. exact (@lem1386578 (term717 _96871 f g m)). Qed.
Lemma lem7230766 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : term717 _96871 f g m.
Proof. exact (@lem7230763 _96871 f g m (@lem7230762 _96871 f g m)). Qed.
Lemma lem7230767 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term563 _96871 f g m) = (term532 _96871 f g m).
Proof. exact (SYM (@lem7228783 _96871 f g m)). Qed.
Lemma lem7230768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7230769 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : (term717 _96871 f g m) = (term517 _96871 f g m).
Proof. exact (MK_COMB (@lem7230768) (@lem7230767 _96871 f g m)). Qed.
Lemma lem7230770 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : term517 _96871 f g m.
Proof. exact (EQ_MP (@lem7230769 _96871 f g m) (@lem7230766 _96871 f g m)). Qed.
Lemma lem7230771 (_96871 : int) (f : nat -> real) (g : nat -> real) (m : nat) : term518 _96871 f g m.
Proof. exact (EQ_MP (@lem7228644 _96871 f g m) (@lem7230770 _96871 f g m)). Qed.
Lemma lem7230772 (f : nat -> real) (g : nat -> real) (m : nat) : term718 f g m.
Proof. exact (@lem7230771 (int_of_num m) f g m). Qed.
Lemma lem7230773 (f : nat -> real) (g : nat -> real) (m : nat) : term516 f g m.
Proof. exact (@lem7230772 f g m (@lem7228643 m)). Qed.
Lemma lem7230774 (f : nat -> real) (g : nat -> real) (m : nat) : (term516 f g m) = (term500 f g m).
Proof. exact (SYM (@lem7228640 f g m)). Qed.
Lemma lem7230775 (f : nat -> real) (g : nat -> real) (m : nat) : term500 f g m.
Proof. exact (EQ_MP (@lem7230774 f g m) (@lem7230773 f g m)). Qed.
Lemma lem7230776 (f : nat -> real) (g : nat -> real) (m : nat) : (term500 f g m) = ((term500 f g m) = True).
Proof. exact (@lem7 (term500 f g m)). Qed.
Lemma lem7230777 (f : nat -> real) (g : nat -> real) (m : nat) : (term500 f g m) = True.
Proof. exact (EQ_MP (@lem7230776 f g m) (@lem7230775 f g m)). Qed.
Lemma lem7230778 (f : nat -> real) (g : nat -> real) (m : nat) : True = (term500 f g m).
Proof. exact (SYM (@lem7230777 f g m)). Qed.
Lemma lem7230779 (f : nat -> real) (g : nat -> real) (m : nat) : term500 f g m.
Proof. exact (EQ_MP (@lem7230778 f g m) (@lem0)). Qed.
Lemma lem7230780 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term212 m) : term498 f g m.
Proof. exact (@lem7230779 f g m (@lem7227192 m h1)). Qed.
Lemma lem7230781 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term363 m) (h2 : term212 m) : term29 = (term384 f g m).
Proof. exact (@lem7230780 f g m h2 (@lem7227702 m h1)). Qed.
Lemma lem7230782 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term363 m) (h2 : term212 m) : term29 = (term368 m g f).
Proof. exact (EQ_MP (@lem7227774 m g f) (@lem7230781 f g m h1 h2)). Qed.
Lemma lem7230783 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term280 f g) = (term360 m g f).
Proof. exact (EQ_MP (@lem7227746 g f m h1) (@lem7228515 g f)). Qed.
Lemma lem7230784 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term363 m) (h2 : term212 m) : term29 = (term301 m g f).
Proof. exact (EQ_MP (@lem7227717 g f m h1) (@lem7230782 g f m h1 h2)). Qed.
Lemma lem7230785 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term363 m) (h2 : term212 m) : (term363 m) = (term29 = (term301 m g f)).
Proof. exact (prop_ext (fun h3 : term363 m => @lem7230784 g f m h1 h2) (fun h3 : term29 = (term301 m g f) => @lem7227702 m h1)). Qed.
Lemma lem7230786 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term363 m) (h2 : term212 m) : term29 = (term301 m g f).
Proof. exact (EQ_MP (@lem7230785 g f m h1 h2) (@lem7227702 m h1)). Qed.
Lemma lem7230787 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term212 m) : term347 m g f.
Proof. exact (fun h0 : term363 m => @lem7230786 g f m h0 h1). Qed.
Lemma lem7230788 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term280 f g) = (term301 m g f).
Proof. exact (EQ_MP (@lem7227701 g f m h1) (@lem7230783 g f m h1)). Qed.
Lemma lem7230789 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((term280 f g) = (term301 m g f)).
Proof. exact (prop_ext (fun h2 : m = (NUMERAL 0) => @lem7230788 g f m h1) (fun h2 : (term280 f g) = (term301 m g f) => @lem7227686 m h1)). Qed.
Lemma lem7230790 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : m = (NUMERAL 0)) : (term280 f g) = (term301 m g f).
Proof. exact (EQ_MP (@lem7230789 g f m h1) (@lem7227686 m h1)). Qed.
Lemma lem7230791 (m : nat) (g : nat -> real) (f : nat -> real) : term351 m g f.
Proof. exact (fun h0 : m = (NUMERAL 0) => @lem7230790 g f m h0). Qed.
Lemma lem7230792 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term212 m) : term354 m g f.
Proof. exact (conj (@lem7230791 m g f) (@lem7230787 g f m h1)). Qed.
Lemma lem7230793 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term212 m) : (term284 m f g) = (term301 m g f).
Proof. exact (EQ_MP (@lem7227685 m g f) (@lem7230792 g f m h1)). Qed.
Lemma lem7230795 (m : nat) (n : nat) : (term163 m n) = (term164 m n).
Proof. exact (EQ_MP (@lem7227130 m n) (@lem7227129 m n)). Qed.
Lemma lem7230796 (m : nat) (n : nat) (h1 : term163 m n) : term164 m n.
Proof. exact (EQ_MP (@lem7230795 m n) (@lem7227244 m n h1)). Qed.
Lemma lem7230797 (m : nat) (n : nat) (h1 : term164 m n) : term164 m n.
Proof. exact (h1). Qed.
Lemma lem7230798 (m : nat) (n : nat) (h1 : m = (S n)) : m = (S n).
Proof. exact (h1). Qed.
Lemma lem7230799 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7230800 (g : nat -> real) (f : nat -> real) (n : nat) : (term719 g f n) = (term719 g f n).
Proof. exact (eq_refl (term719 g f n)). Qed.
Lemma lem7230801 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : m = (S n)) : (term720 g f n m) = (term721 g f n).
Proof. exact (MK_COMB (@lem7230800 g f n) (@lem7230798 m n h1)). Qed.
Lemma lem7230802 (g : nat -> real) (f : nat -> real) (n : nat) : (term721 g f n) = ((term722 f g n) = (term723 g f n)).
Proof. exact (eq_refl (term721 g f n)). Qed.
Lemma lem7230803 (g : nat -> real) (f : nat -> real) (n : nat) (m : nat) : (term724 g f n m) = (term724 g f n m).
Proof. exact (eq_refl (term724 g f n m)). Qed.
Lemma lem7230804 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : ((term720 g f n m) = (term721 g f n)) = ((term720 g f n m) = ((term722 f g n) = (term723 g f n))).
Proof. exact (MK_COMB (@lem7230803 g f n m) (@lem7230802 g f n)). Qed.
Lemma lem7230805 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term720 g f n m) = ((term318 m f g n) = (term338 m g f n)).
Proof. exact (eq_refl (term720 g f n m)). Qed.
Lemma lem7230806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7230807 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term724 g f n m) = (term725 m g f n).
Proof. exact (MK_COMB (@lem7230806) (@lem7230805 m g f n)). Qed.
Lemma lem7230808 (g : nat -> real) (f : nat -> real) (n : nat) : ((term722 f g n) = (term723 g f n)) = ((term722 f g n) = (term723 g f n)).
Proof. exact (eq_refl ((term722 f g n) = (term723 g f n))). Qed.
Lemma lem7230809 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : ((term720 g f n m) = ((term722 f g n) = (term723 g f n))) = (((term318 m f g n) = (term338 m g f n)) = ((term722 f g n) = (term723 g f n))).
Proof. exact (MK_COMB (@lem7230807 m g f n) (@lem7230808 g f n)). Qed.
Lemma lem7230810 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : ((term720 g f n m) = (term721 g f n)) = (((term318 m f g n) = (term338 m g f n)) = ((term722 f g n) = (term723 g f n))).
Proof. exact (TRANS (@lem7230804 m g f n) (@lem7230809 m g f n)). Qed.
Lemma lem7230811 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : m = (S n)) : ((term318 m f g n) = (term338 m g f n)) = ((term722 f g n) = (term723 g f n)).
Proof. exact (EQ_MP (@lem7230810 m g f n) (@lem7230801 g f m n h1)). Qed.
Lemma lem7230812 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : m = (S n)) : ((term722 f g n) = (term723 g f n)) = ((term318 m f g n) = (term338 m g f n)).
Proof. exact (SYM (@lem7230811 g f m n h1)). Qed.
Lemma lem7230826 (n : nat) : (term5 n) = ((term5 n) = True).
Proof. exact (@lem7 (term5 n)). Qed.
Lemma lem7230828 (f : nat -> real) : term249 f.
Proof. exact (@lem7216202 f). Qed.
Lemma lem7230829 (f : nat -> real) : (term249 f) = (term250 f).
Proof. exact (eq_refl (term249 f)). Qed.
Lemma lem7230830 (f : nat -> real) : term250 f.
Proof. exact (EQ_MP (@lem7230829 f) (@lem7230828 f)). Qed.
Lemma lem7230831 (f : nat -> real) (m : nat) : term251 f m.
Proof. exact (@lem7230830 f m). Qed.
Lemma lem7230832 (m : nat) (f : nat -> real) : (term251 f m) = (term252 m f).
Proof. exact (eq_refl (term251 f m)). Qed.
Lemma lem7230833 (m : nat) (f : nat -> real) : term252 m f.
Proof. exact (EQ_MP (@lem7230832 m f) (@lem7230831 f m)). Qed.
Lemma lem7230834 (m : nat) (f : nat -> real) (n : nat) : term253 m f n.
Proof. exact (@lem7230833 m f n). Qed.
Lemma lem7230835 (m : nat) (n : nat) (f : nat -> real) : (term253 m f n) = (term254 m n f).
Proof. exact (eq_refl (term253 m f n)). Qed.
Lemma lem7230836 (m : nat) (n : nat) (f : nat -> real) : term254 m n f.
Proof. exact (EQ_MP (@lem7230835 m n f) (@lem7230834 m f n)). Qed.
Lemma lem7230837 (n : nat) (m : nat) (h1 : Peano.lt n m) : Peano.lt n m.
Proof. exact (h1). Qed.
Lemma lem7230838 (f : nat -> real) (n : nat) (m : nat) (h1 : Peano.lt n m) : (term255 m n f) = term29.
Proof. exact (@lem7230836 m n f (@lem7230837 n m h1)). Qed.
Lemma lem7230844 (m : nat) : term726 m.
Proof. exact (@lem7227124 m). Qed.
Lemma lem7230845 (m : nat) : (term726 m) = (term154 m).
Proof. exact (eq_refl (term726 m)). Qed.
Lemma lem7230846 (m : nat) : term154 m.
Proof. exact (EQ_MP (@lem7230845 m) (@lem7230844 m)). Qed.
Lemma lem7230847 (m : nat) (n : nat) : term727 m n.
Proof. exact (@lem7230846 m n). Qed.
Lemma lem7230848 (m : nat) (n : nat) : (term727 m n) = ((Peano.le n m) = (term150 m n)).
Proof. exact (eq_refl (term727 m n)). Qed.
Lemma lem7230853 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term728 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7230854 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term729 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7230853 _2963 g t e g' t' e'). Qed.
Lemma lem7230855 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term730 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7230854 _2963 g t e g' t'). Qed.
Lemma lem7230856 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term731 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7230855 _2963 g t e g'). Qed.
Lemma lem7230857 (g : Prop) (t : real) (e : real) : term732 g t e.
Proof. exact (@lem7230856 real g t e). Qed.
Lemma lem7230858 (n : nat) (g : nat -> real) (f : nat -> real) : term733 n g f.
Proof. exact (@lem7230857 (term734 n) (term735 n g f) term29). Qed.
Lemma lem7230859 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) : term736 n g f g'.
Proof. exact (@lem7230858 n g f g'). Qed.
Lemma lem7230860 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) : (term736 n g f g') = (term737 n g f g').
Proof. exact (eq_refl (term736 n g f g')). Qed.
Lemma lem7230861 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) : term737 n g f g'.
Proof. exact (EQ_MP (@lem7230860 n g f g') (@lem7230859 n g f g')). Qed.
Lemma lem7230862 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) : term738 n g f g' t'.
Proof. exact (@lem7230861 n g f g' t'). Qed.
Lemma lem7230863 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) : (term738 n g f g' t') = (term739 n g f g' t').
Proof. exact (eq_refl (term738 n g f g' t')). Qed.
Lemma lem7230864 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) : term739 n g f g' t'.
Proof. exact (EQ_MP (@lem7230863 n g f g' t') (@lem7230862 n g f g' t')). Qed.
Lemma lem7230865 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : term740 n g f g' t' e'.
Proof. exact (@lem7230864 n g f g' t' e'). Qed.
Lemma lem7230866 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : (term740 n g f g' t' e') = (term741 n g f g' t' e').
Proof. exact (eq_refl (term740 n g f g' t' e')). Qed.
Lemma lem7230867 (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : term741 n g f g' t' e'.
Proof. exact (EQ_MP (@lem7230866 n g f g' t' e') (@lem7230865 n g f g' t' e')). Qed.
Lemma lem7230869 (m : nat) (n : nat) : (Peano.le n m) = (term150 m n).
Proof. exact (EQ_MP (@lem7230848 m n) (@lem7230847 m n)). Qed.
Lemma lem7230870 (n : nat) : (term734 n) = (term742 n).
Proof. exact (@lem7230869 n (S n)). Qed.
Lemma lem7230872 (n : nat) : (term5 n) = True.
Proof. exact (EQ_MP (@lem7230826 n) (@lem7227110 n)). Qed.
Lemma lem7230873 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7230874 (n : nat) : (term742 n) = (~ True).
Proof. exact (MK_COMB (@lem7230873) (@lem7230872 n)). Qed.
Lemma lem7230876 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem7230877 (n : nat) : (term742 n) = False.
Proof. exact (TRANS (@lem7230874 n) (@lem7230876)). Qed.
Lemma lem7230878 (n : nat) : (term734 n) = False.
Proof. exact (TRANS (@lem7230870 n) (@lem7230877 n)). Qed.
Lemma lem7230879 (n : nat) (g : nat -> real) (f : nat -> real) (t' : real) (e' : real) : term743 n g f t' e'.
Proof. exact (@lem7230867 n g f False t' e'). Qed.
Lemma lem7230880 (n : nat) (g : nat -> real) (f : nat -> real) (t' : real) (e' : real) : term744 n g f t' e'.
Proof. exact (@lem7230879 n g f t' e' (@lem7230878 n)). Qed.
Lemma lem7230885 (m : nat) (n : nat) (f : nat -> real) : term254 m n f.
Proof. exact (fun h0 : Peano.lt n m => @lem7230838 f n m h0). Qed.
Lemma lem7230886 (n : nat) (g : nat -> real) (f : nat -> real) : term745 n g f.
Proof. exact (@lem7230885 (S n) n (term288 g f)). Qed.
Lemma lem7230888 (n : nat) : (term5 n) = True.
Proof. exact (EQ_MP (@lem7230826 n) (@lem7227110 n)). Qed.
Lemma lem7230889 (n : nat) : True = (term5 n).
Proof. exact (SYM (@lem7230888 n)). Qed.
Lemma lem7230890 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem7230889 n) (@lem0)). Qed.
Lemma lem7230891 (n : nat) (g : nat -> real) (f : nat -> real) : (term746 n g f) = term29.
Proof. exact (@lem7230886 n g f (@lem7230890 n)). Qed.
Lemma lem7230892 (f : nat -> real) (g : nat -> real) (n : nat) : (term747 f g n) = (term747 f g n).
Proof. exact (eq_refl (term747 f g n)). Qed.
Lemma lem7230893 (f : nat -> real) (g : nat -> real) (n : nat) : (term735 n g f) = (term748 f g n).
Proof. exact (MK_COMB (@lem7230892 f g n) (@lem7230891 n g f)). Qed.
Lemma lem7230894 (f : nat -> real) (g : nat -> real) (n : nat) : term749 f g n.
Proof. exact (fun h0 : False => @lem7230893 f g n). Qed.
Lemma lem7230895 (f : nat -> real) (g : nat -> real) (n : nat) (e' : real) : term750 f g n e'.
Proof. exact (@lem7230880 n g f (term748 f g n) e'). Qed.
Lemma lem7230896 (f : nat -> real) (g : nat -> real) (n : nat) (e' : real) : term751 f g n e'.
Proof. exact (@lem7230895 f g n e' (@lem7230894 f g n)). Qed.
Lemma lem7230902 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7230903 : term752.
Proof. exact (fun h0 : ~ False => @lem7230902). Qed.
Lemma lem7230904 (f : nat -> real) (g : nat -> real) (n : nat) : term753 f g n.
Proof. exact (@lem7230896 f g n term29). Qed.
Lemma lem7230905 (f : nat -> real) (g : nat -> real) (n : nat) : (term754 n g f) = (term755 f g n).
Proof. exact (@lem7230904 f g n (@lem7230903)). Qed.
Lemma lem7230907 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7230908 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7230907 real t1 t2). Qed.
Lemma lem7230909 (f : nat -> real) (g : nat -> real) (n : nat) : (term755 f g n) = term29.
Proof. exact (@lem7230908 (term748 f g n) term29). Qed.
Lemma lem7230910 (n : nat) (g : nat -> real) (f : nat -> real) : (term754 n g f) = term29.
Proof. exact (TRANS (@lem7230905 f g n) (@lem7230909 f g n)). Qed.
Lemma lem7230911 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7230912 (n : nat) (g : nat -> real) (f : nat -> real) : (term756 n g f) = term128.
Proof. exact (MK_COMB (@lem7230911) (@lem7230910 n g f)). Qed.
Lemma lem7230913 (f : nat -> real) (g : nat -> real) (n : nat) : (term316 f g n) = (term316 f g n).
Proof. exact (eq_refl (term316 f g n)). Qed.
Lemma lem7230914 (f : nat -> real) (g : nat -> real) (n : nat) : (term722 f g n) = (term757 f g n).
Proof. exact (MK_COMB (@lem7230912 n g f) (@lem7230913 f g n)). Qed.
Lemma lem7230915 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7230916 (f : nat -> real) (g : nat -> real) (n : nat) : (term758 f g n) = (term759 f g n).
Proof. exact (MK_COMB (@lem7230915) (@lem7230914 f g n)). Qed.
Lemma lem7230918 (m : nat) (n : nat) (f : nat -> real) : term254 m n f.
Proof. exact (fun h0 : Peano.lt n m => @lem7230838 f n m h0). Qed.
Lemma lem7230919 (n : nat) (g : nat -> real) (f : nat -> real) : term745 n g f.
Proof. exact (@lem7230918 (S n) n (term288 g f)). Qed.
Lemma lem7230921 (n : nat) : (term5 n) = True.
Proof. exact (EQ_MP (@lem7230826 n) (@lem7227110 n)). Qed.
Lemma lem7230922 (n : nat) : True = (term5 n).
Proof. exact (SYM (@lem7230921 n)). Qed.
Lemma lem7230923 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem7230922 n) (@lem0)). Qed.
Lemma lem7230924 (n : nat) (g : nat -> real) (f : nat -> real) : (term746 n g f) = term29.
Proof. exact (@lem7230919 n g f (@lem7230923 n)). Qed.
Lemma lem7230925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7230926 (n : nat) (g : nat -> real) (f : nat -> real) : (term760 n g f) = term128.
Proof. exact (MK_COMB (@lem7230925) (@lem7230924 n g f)). Qed.
Lemma lem7230927 (g : nat -> real) (f : nat -> real) (n : nat) : (term329 g f n) = (term329 g f n).
Proof. exact (eq_refl (term329 g f n)). Qed.
Lemma lem7230928 (g : nat -> real) (f : nat -> real) (n : nat) : (term761 g f n) = (term762 g f n).
Proof. exact (MK_COMB (@lem7230926 n g f) (@lem7230927 g f n)). Qed.
Lemma lem7230929 (f : nat -> real) (g : nat -> real) (n : nat) : (term763 f g n) = (term763 f g n).
Proof. exact (eq_refl (term763 f g n)). Qed.
Lemma lem7230930 (g : nat -> real) (f : nat -> real) (n : nat) : (term723 g f n) = (term764 g f n).
Proof. exact (MK_COMB (@lem7230929 f g n) (@lem7230928 g f n)). Qed.
Lemma lem7230931 (g : nat -> real) (f : nat -> real) (n : nat) : ((term722 f g n) = (term723 g f n)) = ((term757 f g n) = (term764 g f n)).
Proof. exact (MK_COMB (@lem7230916 f g n) (@lem7230930 g f n)). Qed.
Lemma lem7230934 (g : nat -> real) (f : nat -> real) (n : nat) : ((term757 f g n) = (term764 g f n)) = ((term722 f g n) = (term723 g f n)).
Proof. exact (SYM (@lem7230931 g f n)). Qed.
Lemma lem7230959 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem7230964 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term728 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7230965 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term729 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7230964 _2963 g t e g' t' e'). Qed.
Lemma lem7230966 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term730 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7230965 _2963 g t e g' t'). Qed.
Lemma lem7230967 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term731 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7230966 _2963 g t e g'). Qed.
Lemma lem7230968 (g : Prop) (t : real) (e : real) : term732 g t e.
Proof. exact (@lem7230967 real g t e). Qed.
Lemma lem7230969 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : term765 m n g f.
Proof. exact (@lem7230968 (Peano.le m n) (term766 m n g f) term29). Qed.
Lemma lem7230970 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) : term767 m n g f g'.
Proof. exact (@lem7230969 m n g f g'). Qed.
Lemma lem7230971 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) : (term767 m n g f g') = (term768 m n g f g').
Proof. exact (eq_refl (term767 m n g f g')). Qed.
Lemma lem7230972 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) : term768 m n g f g'.
Proof. exact (EQ_MP (@lem7230971 m n g f g') (@lem7230970 m n g f g')). Qed.
Lemma lem7230973 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) : term769 m n g f g' t'.
Proof. exact (@lem7230972 m n g f g' t'). Qed.
Lemma lem7230974 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) : (term769 m n g f g' t') = (term770 m n g f g' t').
Proof. exact (eq_refl (term769 m n g f g' t')). Qed.
Lemma lem7230975 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) : term770 m n g f g' t'.
Proof. exact (EQ_MP (@lem7230974 m n g f g' t') (@lem7230973 m n g f g' t')). Qed.
Lemma lem7230976 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : term771 m n g f g' t' e'.
Proof. exact (@lem7230975 m n g f g' t' e'). Qed.
Lemma lem7230977 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : (term771 m n g f g' t' e') = (term772 m n g f g' t' e').
Proof. exact (eq_refl (term771 m n g f g' t' e')). Qed.
Lemma lem7230978 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : term772 m n g f g' t' e'.
Proof. exact (EQ_MP (@lem7230977 m n g f g' t' e') (@lem7230976 m n g f g' t' e')). Qed.
Lemma lem7230980 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem7230959 m n) (@lem7230799 m n h1)). Qed.
Lemma lem7230981 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (t' : real) (e' : real) : term773 m n g f t' e'.
Proof. exact (@lem7230978 m n g f True t' e'). Qed.
Lemma lem7230982 (g : nat -> real) (f : nat -> real) (t' : real) (e' : real) (m : nat) (n : nat) (h1 : Peano.le m n) : term774 m n g f t' e'.
Proof. exact (@lem7230981 m n g f t' e' (@lem7230980 m n h1)). Qed.
Lemma lem7230993 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term766 m n g f) = (term766 m n g f).
Proof. exact (eq_refl (term766 m n g f)). Qed.
Lemma lem7230994 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : term775 m n g f.
Proof. exact (fun h0 : True => @lem7230993 m n g f). Qed.
Lemma lem7230995 (g : nat -> real) (f : nat -> real) (e' : real) (m : nat) (n : nat) (h1 : Peano.le m n) : term776 m n g f e'.
Proof. exact (@lem7230982 g f (term766 m n g f) e' m n h1). Qed.
Lemma lem7230996 (g : nat -> real) (f : nat -> real) (e' : real) (m : nat) (n : nat) (h1 : Peano.le m n) : term777 m n g f e'.
Proof. exact (@lem7230995 g f e' m n h1 (@lem7230994 m n g f)). Qed.
Lemma lem7231000 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7231001 : term778.
Proof. exact (fun h0 : ~ True => @lem7231000). Qed.
Lemma lem7231002 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : term779 m n g f.
Proof. exact (@lem7230996 g f term29 m n h1). Qed.
Lemma lem7231003 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term184 m n g f) = (term780 m n g f).
Proof. exact (@lem7231002 g f m n h1 (@lem7231001)). Qed.
Lemma lem7231005 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7231006 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7231005 real t2 t1). Qed.
Lemma lem7231007 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term780 m n g f) = (term766 m n g f).
Proof. exact (@lem7231006 term29 (term766 m n g f)). Qed.
Lemma lem7231013 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term184 m n g f) = (term766 m n g f).
Proof. exact (TRANS (@lem7231003 g f m n h1) (@lem7231007 m n g f)). Qed.
Lemma lem7231014 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231015 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term311 m n g f) = (term781 m n g f).
Proof. exact (MK_COMB (@lem7231014) (@lem7231013 g f m n h1)). Qed.
Lemma lem7231021 (f : nat -> real) (g : nat -> real) (n : nat) : (term316 f g n) = (term316 f g n).
Proof. exact (eq_refl (term316 f g n)). Qed.
Lemma lem7231022 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term318 m f g n) = (term782 m f g n).
Proof. exact (MK_COMB (@lem7231015 g f m n h1) (@lem7231021 f g n)). Qed.
Lemma lem7231028 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7231029 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term322 m f g n) = (term783 m f g n).
Proof. exact (MK_COMB (@lem7231028) (@lem7231022 f g m n h1)). Qed.
Lemma lem7231040 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term338 m g f n) = (term338 m g f n).
Proof. exact (eq_refl (term338 m g f n)). Qed.
Lemma lem7231041 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term318 m f g n) = (term338 m g f n)) = ((term782 m f g n) = (term338 m g f n)).
Proof. exact (MK_COMB (@lem7231029 f g m n h1) (@lem7231040 m g f n)). Qed.
Lemma lem7231054 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term782 m f g n) = (term338 m g f n)) = ((term318 m f g n) = (term338 m g f n)).
Proof. exact (SYM (@lem7231041 g f m n h1)). Qed.
Lemma lem7231055 : term784.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem7231056 : term785.
Proof. exact (proj2 (@lem7231055)). Qed.
Lemma lem7231064 : term786.
Proof. exact (proj1 (@lem7231056)). Qed.
Lemma lem7231065 (m : nat) : term787 m.
Proof. exact (@lem7231064 m). Qed.
Lemma lem7231066 (m : nat) : (term787 m) = (term788 m).
Proof. exact (eq_refl (term787 m)). Qed.
Lemma lem7231067 (m : nat) : term788 m.
Proof. exact (EQ_MP (@lem7231066 m) (@lem7231065 m)). Qed.
Lemma lem7231068 (m : nat) (n : nat) : term789 m n.
Proof. exact (@lem7231067 m n). Qed.
Lemma lem7231069 (m : nat) (n : nat) : (term789 m n) = ((term790 m n) = (term791 m n)).
Proof. exact (eq_refl (term789 m n)). Qed.
Lemma lem7231079 (m : nat) : term792 m.
Proof. exact (@lem7226639 m). Qed.
Lemma lem7231080 (m : nat) : (term792 m) = ((term0 m) = (S m)).
Proof. exact (eq_refl (term792 m)). Qed.
Lemma lem7231085 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231069 m n) (@lem7231068 m n)). Qed.
Lemma lem7231086 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231085 n term13). Qed.
Lemma lem7231088 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231080 m) (@lem7231079 m)). Qed.
Lemma lem7231089 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231088 n). Qed.
Lemma lem7231090 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231091 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231090) (@lem7231089 n)). Qed.
Lemma lem7231092 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231086 n) (@lem7231091 n)). Qed.
Lemma lem7231093 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231094 (g : nat -> real) (n : nat) : (term796 g n) = (term797 g n).
Proof. exact (MK_COMB (@lem7231093 g) (@lem7231092 n)). Qed.
Lemma lem7231095 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231096 (g : nat -> real) (n : nat) : (term798 g n) = (term799 g n).
Proof. exact (MK_COMB (@lem7231095) (@lem7231094 g n)). Qed.
Lemma lem7231097 (g : nat -> real) (n : nat) : (term800 g n) = (term800 g n).
Proof. exact (eq_refl (term800 g n)). Qed.
Lemma lem7231098 (g : nat -> real) (n : nat) : (term801 g n) = (term802 g n).
Proof. exact (MK_COMB (@lem7231096 g n) (@lem7231097 g n)). Qed.
Lemma lem7231099 (f : nat -> real) (n : nat) : (term803 f n) = (term803 f n).
Proof. exact (eq_refl (term803 f n)). Qed.
Lemma lem7231100 (f : nat -> real) (g : nat -> real) (n : nat) : (term316 f g n) = (term804 f g n).
Proof. exact (MK_COMB (@lem7231099 f n) (@lem7231098 g n)). Qed.
Lemma lem7231101 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem7231102 (f : nat -> real) (g : nat -> real) (n : nat) : (term757 f g n) = (term805 f g n).
Proof. exact (MK_COMB (@lem7231101) (@lem7231100 f g n)). Qed.
Lemma lem7231103 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7231104 (f : nat -> real) (g : nat -> real) (n : nat) : (term759 f g n) = (term806 f g n).
Proof. exact (MK_COMB (@lem7231103) (@lem7231102 f g n)). Qed.
Lemma lem7231106 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231069 m n) (@lem7231068 m n)). Qed.
Lemma lem7231107 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231106 n term13). Qed.
Lemma lem7231109 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231080 m) (@lem7231079 m)). Qed.
Lemma lem7231110 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231109 n). Qed.
Lemma lem7231111 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231112 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231111) (@lem7231110 n)). Qed.
Lemma lem7231113 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231107 n) (@lem7231112 n)). Qed.
Lemma lem7231114 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7231115 (f : nat -> real) (n : nat) : (term796 f n) = (term797 f n).
Proof. exact (MK_COMB (@lem7231114 f) (@lem7231113 n)). Qed.
Lemma lem7231116 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231117 (f : nat -> real) (n : nat) : (term807 f n) = (term808 f n).
Proof. exact (MK_COMB (@lem7231116) (@lem7231115 f n)). Qed.
Lemma lem7231119 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231069 m n) (@lem7231068 m n)). Qed.
Lemma lem7231120 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231119 n term13). Qed.
Lemma lem7231122 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231080 m) (@lem7231079 m)). Qed.
Lemma lem7231123 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231122 n). Qed.
Lemma lem7231124 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231125 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231124) (@lem7231123 n)). Qed.
Lemma lem7231126 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231120 n) (@lem7231125 n)). Qed.
Lemma lem7231127 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231128 (g : nat -> real) (n : nat) : (term796 g n) = (term797 g n).
Proof. exact (MK_COMB (@lem7231127 g) (@lem7231126 n)). Qed.
Lemma lem7231129 (f : nat -> real) (g : nat -> real) (n : nat) : (term809 f g n) = (term810 f g n).
Proof. exact (MK_COMB (@lem7231117 f n) (@lem7231128 g n)). Qed.
Lemma lem7231130 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231131 (f : nat -> real) (g : nat -> real) (n : nat) : (term811 f g n) = (term812 f g n).
Proof. exact (MK_COMB (@lem7231130) (@lem7231129 f g n)). Qed.
Lemma lem7231132 (f : nat -> real) (g : nat -> real) (n : nat) : (term813 f g n) = (term813 f g n).
Proof. exact (eq_refl (term813 f g n)). Qed.
Lemma lem7231133 (f : nat -> real) (g : nat -> real) (n : nat) : (term814 f g n) = (term815 f g n).
Proof. exact (MK_COMB (@lem7231131 f g n) (@lem7231132 f g n)). Qed.
Lemma lem7231134 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231135 (f : nat -> real) (g : nat -> real) (n : nat) : (term763 f g n) = (term816 f g n).
Proof. exact (MK_COMB (@lem7231134) (@lem7231133 f g n)). Qed.
Lemma lem7231137 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231069 m n) (@lem7231068 m n)). Qed.
Lemma lem7231138 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231137 n term13). Qed.
Lemma lem7231140 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231080 m) (@lem7231079 m)). Qed.
Lemma lem7231141 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231140 n). Qed.
Lemma lem7231142 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231143 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231142) (@lem7231141 n)). Qed.
Lemma lem7231144 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231138 n) (@lem7231143 n)). Qed.
Lemma lem7231145 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231146 (g : nat -> real) (n : nat) : (term796 g n) = (term797 g n).
Proof. exact (MK_COMB (@lem7231145 g) (@lem7231144 n)). Qed.
Lemma lem7231147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231148 (g : nat -> real) (n : nat) : (term807 g n) = (term808 g n).
Proof. exact (MK_COMB (@lem7231147) (@lem7231146 g n)). Qed.
Lemma lem7231150 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231069 m n) (@lem7231068 m n)). Qed.
Lemma lem7231151 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231150 n term13). Qed.
Lemma lem7231153 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231080 m) (@lem7231079 m)). Qed.
Lemma lem7231154 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231153 n). Qed.
Lemma lem7231155 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231156 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231155) (@lem7231154 n)). Qed.
Lemma lem7231157 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231151 n) (@lem7231156 n)). Qed.
Lemma lem7231158 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7231159 (f : nat -> real) (n : nat) : (term796 f n) = (term797 f n).
Proof. exact (MK_COMB (@lem7231158 f) (@lem7231157 n)). Qed.
Lemma lem7231160 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231161 (f : nat -> real) (n : nat) : (term798 f n) = (term799 f n).
Proof. exact (MK_COMB (@lem7231160) (@lem7231159 f n)). Qed.
Lemma lem7231162 (f : nat -> real) (n : nat) : (term800 f n) = (term800 f n).
Proof. exact (eq_refl (term800 f n)). Qed.
Lemma lem7231163 (f : nat -> real) (n : nat) : (term801 f n) = (term802 f n).
Proof. exact (MK_COMB (@lem7231161 f n) (@lem7231162 f n)). Qed.
Lemma lem7231164 (g : nat -> real) (f : nat -> real) (n : nat) : (term329 g f n) = (term817 g f n).
Proof. exact (MK_COMB (@lem7231148 g n) (@lem7231163 f n)). Qed.
Lemma lem7231165 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem7231166 (g : nat -> real) (f : nat -> real) (n : nat) : (term762 g f n) = (term818 g f n).
Proof. exact (MK_COMB (@lem7231165) (@lem7231164 g f n)). Qed.
Lemma lem7231167 (g : nat -> real) (f : nat -> real) (n : nat) : (term764 g f n) = (term819 g f n).
Proof. exact (MK_COMB (@lem7231135 f g n) (@lem7231166 g f n)). Qed.
Lemma lem7231168 (g : nat -> real) (f : nat -> real) (n : nat) : ((term757 f g n) = (term764 g f n)) = ((term805 f g n) = (term819 g f n)).
Proof. exact (MK_COMB (@lem7231104 f g n) (@lem7231167 g f n)). Qed.
Lemma lem7231171 (g : nat -> real) (f : nat -> real) (n : nat) : ((term805 f g n) = (term819 g f n)) = ((term757 f g n) = (term764 g f n)).
Proof. exact (SYM (@lem7231168 g f n)). Qed.
Lemma lem7231172 : term784.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem7231173 : term785.
Proof. exact (proj2 (@lem7231172)). Qed.
Lemma lem7231181 : term786.
Proof. exact (proj1 (@lem7231173)). Qed.
Lemma lem7231182 (m : nat) : term787 m.
Proof. exact (@lem7231181 m). Qed.
Lemma lem7231183 (m : nat) : (term787 m) = (term788 m).
Proof. exact (eq_refl (term787 m)). Qed.
Lemma lem7231184 (m : nat) : term788 m.
Proof. exact (EQ_MP (@lem7231183 m) (@lem7231182 m)). Qed.
Lemma lem7231185 (m : nat) (n : nat) : term789 m n.
Proof. exact (@lem7231184 m n). Qed.
Lemma lem7231186 (m : nat) (n : nat) : (term789 m n) = ((term790 m n) = (term791 m n)).
Proof. exact (eq_refl (term789 m n)). Qed.
Lemma lem7231196 (m : nat) : term792 m.
Proof. exact (@lem7226639 m). Qed.
Lemma lem7231197 (m : nat) : (term792 m) = ((term0 m) = (S m)).
Proof. exact (eq_refl (term792 m)). Qed.
Lemma lem7231204 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231205 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231204 n). Qed.
Lemma lem7231206 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7231207 (f : nat -> real) (n : nat) : (term820 f n) = (term800 f n).
Proof. exact (MK_COMB (@lem7231206 f) (@lem7231205 n)). Qed.
Lemma lem7231208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231209 (f : nat -> real) (n : nat) : (term821 f n) = (term803 f n).
Proof. exact (MK_COMB (@lem7231208) (@lem7231207 f n)). Qed.
Lemma lem7231211 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231212 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231211 n). Qed.
Lemma lem7231213 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231214 (g : nat -> real) (n : nat) : (term820 g n) = (term800 g n).
Proof. exact (MK_COMB (@lem7231213 g) (@lem7231212 n)). Qed.
Lemma lem7231215 (f : nat -> real) (g : nat -> real) (n : nat) : (term822 f g n) = (term813 f g n).
Proof. exact (MK_COMB (@lem7231209 f n) (@lem7231214 g n)). Qed.
Lemma lem7231216 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231217 (f : nat -> real) (g : nat -> real) (n : nat) : (term823 f g n) = (term824 f g n).
Proof. exact (MK_COMB (@lem7231216) (@lem7231215 f g n)). Qed.
Lemma lem7231218 (f : nat -> real) (g : nat -> real) (m : nat) : (term374 f g m) = (term374 f g m).
Proof. exact (eq_refl (term374 f g m)). Qed.
Lemma lem7231219 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term825 n f g m) = (term826 n f g m).
Proof. exact (MK_COMB (@lem7231217 f g n) (@lem7231218 f g m)). Qed.
Lemma lem7231220 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231221 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term827 n f g m) = (term828 n f g m).
Proof. exact (MK_COMB (@lem7231220) (@lem7231219 n f g m)). Qed.
Lemma lem7231223 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231224 (k : nat) : (term0 k) = (S k).
Proof. exact (@lem7231223 k). Qed.
Lemma lem7231225 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231226 (g : nat -> real) (k : nat) : (term820 g k) = (term800 g k).
Proof. exact (MK_COMB (@lem7231225 g) (@lem7231224 k)). Qed.
Lemma lem7231227 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231228 (g : nat -> real) (k : nat) : (term821 g k) = (term803 g k).
Proof. exact (MK_COMB (@lem7231227) (@lem7231226 g k)). Qed.
Lemma lem7231230 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231231 (k : nat) : (term0 k) = (S k).
Proof. exact (@lem7231230 k). Qed.
Lemma lem7231232 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7231233 (f : nat -> real) (k : nat) : (term820 f k) = (term800 f k).
Proof. exact (MK_COMB (@lem7231232 f) (@lem7231231 k)). Qed.
Lemma lem7231234 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231235 (f : nat -> real) (k : nat) : (term829 f k) = (term830 f k).
Proof. exact (MK_COMB (@lem7231234) (@lem7231233 f k)). Qed.
Lemma lem7231236 (f : nat -> real) (k : nat) : (f k) = (f k).
Proof. exact (eq_refl (f k)). Qed.
Lemma lem7231237 (f : nat -> real) (k : nat) : (term831 f k) = (term832 f k).
Proof. exact (MK_COMB (@lem7231235 f k) (@lem7231236 f k)). Qed.
Lemma lem7231238 (g : nat -> real) (f : nat -> real) (k : nat) : (term292 g f k) = (term833 g f k).
Proof. exact (MK_COMB (@lem7231228 g k) (@lem7231237 f k)). Qed.
Lemma lem7231239 (g : nat -> real) (f : nat -> real) : (term288 g f) = (term834 g f).
Proof. exact (fun_ext (fun k : nat => @lem7231238 g f k)). Qed.
Lemma lem7231240 (m : nat) (n : nat) : (term835 m n) = (term835 m n).
Proof. exact (eq_refl (term835 m n)). Qed.
Lemma lem7231241 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term335 m n g f) = (term836 m n g f).
Proof. exact (MK_COMB (@lem7231240 m n) (@lem7231239 g f)). Qed.
Lemma lem7231242 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term766 m n g f) = (term837 m n g f).
Proof. exact (MK_COMB (@lem7231221 n f g m) (@lem7231241 m n g f)). Qed.
Lemma lem7231243 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231244 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term781 m n g f) = (term838 m n g f).
Proof. exact (MK_COMB (@lem7231243) (@lem7231242 m n g f)). Qed.
Lemma lem7231246 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231186 m n) (@lem7231185 m n)). Qed.
Lemma lem7231247 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231246 n term13). Qed.
Lemma lem7231249 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231250 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231249 n). Qed.
Lemma lem7231251 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231252 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231251) (@lem7231250 n)). Qed.
Lemma lem7231253 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231247 n) (@lem7231252 n)). Qed.
Lemma lem7231254 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231255 (g : nat -> real) (n : nat) : (term796 g n) = (term797 g n).
Proof. exact (MK_COMB (@lem7231254 g) (@lem7231253 n)). Qed.
Lemma lem7231256 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231257 (g : nat -> real) (n : nat) : (term798 g n) = (term799 g n).
Proof. exact (MK_COMB (@lem7231256) (@lem7231255 g n)). Qed.
Lemma lem7231258 (g : nat -> real) (n : nat) : (term800 g n) = (term800 g n).
Proof. exact (eq_refl (term800 g n)). Qed.
Lemma lem7231259 (g : nat -> real) (n : nat) : (term801 g n) = (term802 g n).
Proof. exact (MK_COMB (@lem7231257 g n) (@lem7231258 g n)). Qed.
Lemma lem7231260 (f : nat -> real) (n : nat) : (term803 f n) = (term803 f n).
Proof. exact (eq_refl (term803 f n)). Qed.
Lemma lem7231261 (f : nat -> real) (g : nat -> real) (n : nat) : (term316 f g n) = (term804 f g n).
Proof. exact (MK_COMB (@lem7231260 f n) (@lem7231259 g n)). Qed.
Lemma lem7231262 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term782 m f g n) = (term839 m f g n).
Proof. exact (MK_COMB (@lem7231244 m n g f) (@lem7231261 f g n)). Qed.
Lemma lem7231263 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7231264 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term783 m f g n) = (term840 m f g n).
Proof. exact (MK_COMB (@lem7231263) (@lem7231262 m f g n)). Qed.
Lemma lem7231266 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231186 m n) (@lem7231185 m n)). Qed.
Lemma lem7231267 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231266 n term13). Qed.
Lemma lem7231269 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231270 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231269 n). Qed.
Lemma lem7231271 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231272 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231271) (@lem7231270 n)). Qed.
Lemma lem7231273 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231267 n) (@lem7231272 n)). Qed.
Lemma lem7231274 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7231275 (f : nat -> real) (n : nat) : (term796 f n) = (term797 f n).
Proof. exact (MK_COMB (@lem7231274 f) (@lem7231273 n)). Qed.
Lemma lem7231276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231277 (f : nat -> real) (n : nat) : (term807 f n) = (term808 f n).
Proof. exact (MK_COMB (@lem7231276) (@lem7231275 f n)). Qed.
Lemma lem7231279 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231186 m n) (@lem7231185 m n)). Qed.
Lemma lem7231280 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231279 n term13). Qed.
Lemma lem7231282 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231283 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231282 n). Qed.
Lemma lem7231284 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231285 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231284) (@lem7231283 n)). Qed.
Lemma lem7231286 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231280 n) (@lem7231285 n)). Qed.
Lemma lem7231287 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231288 (g : nat -> real) (n : nat) : (term796 g n) = (term797 g n).
Proof. exact (MK_COMB (@lem7231287 g) (@lem7231286 n)). Qed.
Lemma lem7231289 (f : nat -> real) (g : nat -> real) (n : nat) : (term809 f g n) = (term810 f g n).
Proof. exact (MK_COMB (@lem7231277 f n) (@lem7231288 g n)). Qed.
Lemma lem7231290 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231291 (f : nat -> real) (g : nat -> real) (n : nat) : (term811 f g n) = (term812 f g n).
Proof. exact (MK_COMB (@lem7231290) (@lem7231289 f g n)). Qed.
Lemma lem7231292 (f : nat -> real) (g : nat -> real) (m : nat) : (term374 f g m) = (term374 f g m).
Proof. exact (eq_refl (term374 f g m)). Qed.
Lemma lem7231293 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term841 n f g m) = (term842 n f g m).
Proof. exact (MK_COMB (@lem7231291 f g n) (@lem7231292 f g m)). Qed.
Lemma lem7231294 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231295 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term337 n f g m) = (term843 n f g m).
Proof. exact (MK_COMB (@lem7231294) (@lem7231293 n f g m)). Qed.
Lemma lem7231297 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231298 (k : nat) : (term0 k) = (S k).
Proof. exact (@lem7231297 k). Qed.
Lemma lem7231299 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231300 (g : nat -> real) (k : nat) : (term820 g k) = (term800 g k).
Proof. exact (MK_COMB (@lem7231299 g) (@lem7231298 k)). Qed.
Lemma lem7231301 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231302 (g : nat -> real) (k : nat) : (term821 g k) = (term803 g k).
Proof. exact (MK_COMB (@lem7231301) (@lem7231300 g k)). Qed.
Lemma lem7231304 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231305 (k : nat) : (term0 k) = (S k).
Proof. exact (@lem7231304 k). Qed.
Lemma lem7231306 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7231307 (f : nat -> real) (k : nat) : (term820 f k) = (term800 f k).
Proof. exact (MK_COMB (@lem7231306 f) (@lem7231305 k)). Qed.
Lemma lem7231308 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231309 (f : nat -> real) (k : nat) : (term829 f k) = (term830 f k).
Proof. exact (MK_COMB (@lem7231308) (@lem7231307 f k)). Qed.
Lemma lem7231310 (f : nat -> real) (k : nat) : (f k) = (f k).
Proof. exact (eq_refl (f k)). Qed.
Lemma lem7231311 (f : nat -> real) (k : nat) : (term831 f k) = (term832 f k).
Proof. exact (MK_COMB (@lem7231309 f k) (@lem7231310 f k)). Qed.
Lemma lem7231312 (g : nat -> real) (f : nat -> real) (k : nat) : (term292 g f k) = (term833 g f k).
Proof. exact (MK_COMB (@lem7231302 g k) (@lem7231311 f k)). Qed.
Lemma lem7231313 (g : nat -> real) (f : nat -> real) : (term288 g f) = (term834 g f).
Proof. exact (fun_ext (fun k : nat => @lem7231312 g f k)). Qed.
Lemma lem7231314 (m : nat) (n : nat) : (term835 m n) = (term835 m n).
Proof. exact (eq_refl (term835 m n)). Qed.
Lemma lem7231315 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term335 m n g f) = (term836 m n g f).
Proof. exact (MK_COMB (@lem7231314 m n) (@lem7231313 g f)). Qed.
Lemma lem7231316 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231317 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term330 m n g f) = (term844 m n g f).
Proof. exact (MK_COMB (@lem7231316) (@lem7231315 m n g f)). Qed.
Lemma lem7231319 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231186 m n) (@lem7231185 m n)). Qed.
Lemma lem7231320 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231319 n term13). Qed.
Lemma lem7231322 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231323 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231322 n). Qed.
Lemma lem7231324 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231325 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231324) (@lem7231323 n)). Qed.
Lemma lem7231326 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231320 n) (@lem7231325 n)). Qed.
Lemma lem7231327 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7231328 (g : nat -> real) (n : nat) : (term796 g n) = (term797 g n).
Proof. exact (MK_COMB (@lem7231327 g) (@lem7231326 n)). Qed.
Lemma lem7231329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231330 (g : nat -> real) (n : nat) : (term807 g n) = (term808 g n).
Proof. exact (MK_COMB (@lem7231329) (@lem7231328 g n)). Qed.
Lemma lem7231332 (m : nat) (n : nat) : (term790 m n) = (term791 m n).
Proof. exact (EQ_MP (@lem7231186 m n) (@lem7231185 m n)). Qed.
Lemma lem7231333 (n : nat) : (term793 n) = (term794 n).
Proof. exact (@lem7231332 n term13). Qed.
Lemma lem7231335 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem7231197 m) (@lem7231196 m)). Qed.
Lemma lem7231336 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem7231335 n). Qed.
Lemma lem7231337 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7231338 (n : nat) : (term794 n) = (term795 n).
Proof. exact (MK_COMB (@lem7231337) (@lem7231336 n)). Qed.
Lemma lem7231339 (n : nat) : (term793 n) = (term795 n).
Proof. exact (TRANS (@lem7231333 n) (@lem7231338 n)). Qed.
Lemma lem7231340 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7231341 (f : nat -> real) (n : nat) : (term796 f n) = (term797 f n).
Proof. exact (MK_COMB (@lem7231340 f) (@lem7231339 n)). Qed.
Lemma lem7231342 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231343 (f : nat -> real) (n : nat) : (term798 f n) = (term799 f n).
Proof. exact (MK_COMB (@lem7231342) (@lem7231341 f n)). Qed.
Lemma lem7231344 (f : nat -> real) (n : nat) : (term800 f n) = (term800 f n).
Proof. exact (eq_refl (term800 f n)). Qed.
Lemma lem7231345 (f : nat -> real) (n : nat) : (term801 f n) = (term802 f n).
Proof. exact (MK_COMB (@lem7231343 f n) (@lem7231344 f n)). Qed.
Lemma lem7231346 (g : nat -> real) (f : nat -> real) (n : nat) : (term329 g f n) = (term817 g f n).
Proof. exact (MK_COMB (@lem7231330 g n) (@lem7231345 f n)). Qed.
Lemma lem7231347 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term332 m g f n) = (term845 m g f n).
Proof. exact (MK_COMB (@lem7231317 m n g f) (@lem7231346 g f n)). Qed.
Lemma lem7231348 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term338 m g f n) = (term846 m g f n).
Proof. exact (MK_COMB (@lem7231295 n f g m) (@lem7231347 m g f n)). Qed.
Lemma lem7231349 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : ((term782 m f g n) = (term338 m g f n)) = ((term839 m f g n) = (term846 m g f n)).
Proof. exact (MK_COMB (@lem7231264 m f g n) (@lem7231348 m g f n)). Qed.
Lemma lem7231352 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : ((term839 m f g n) = (term846 m g f n)) = ((term782 m f g n) = (term338 m g f n)).
Proof. exact (SYM (@lem7231349 m g f n)). Qed.
Lemma lem7231363 (g : nat -> real) (f : nat -> real) (n : nat) : (term847 g f n) = (term848 g f n).
Proof. exact (@lem1988318 (term805 f g n) (term819 g f n)). Qed.
Lemma lem7231369 (f : nat -> real) (n : nat) : (term802 f n) = (term849 f n).
Proof. exact (@lem1982792 (term797 f n) (term800 f n)). Qed.
Lemma lem7231374 (f : nat -> real) (n : nat) : (term849 f n) = (term850 f n).
Proof. exact (@lem1982761 (term851 f n) (term797 f n)). Qed.
Lemma lem7231376 (f : nat -> real) (n : nat) : (term802 f n) = (term850 f n).
Proof. exact (TRANS (@lem7231369 f n) (@lem7231374 f n)). Qed.
Lemma lem7231379 (g : nat -> real) (n : nat) : (term808 g n) = (term808 g n).
Proof. exact (eq_refl (term808 g n)). Qed.
Lemma lem7231380 (g : nat -> real) (f : nat -> real) (n : nat) : (term817 g f n) = (term852 g f n).
Proof. exact (MK_COMB (@lem7231379 g n) (@lem7231376 f n)). Qed.
Lemma lem7231381 (g : nat -> real) (f : nat -> real) (n : nat) : (term852 g f n) = (term853 g f n).
Proof. exact (@lem1982781 (term851 f n) (term797 g n) (term797 f n)). Qed.
Lemma lem7231382 (f : nat -> real) (g : nat -> real) (n : nat) : (term810 g f n) = (term810 f g n).
Proof. exact (@lem1982747 (term797 f n) (term797 g n)). Qed.
Lemma lem7231383 (g : nat -> real) (f : nat -> real) (n : nat) : (term854 g f n) = (term855 g f n).
Proof. exact (@lem1982751 term62 (term797 g n) (term800 f n)). Qed.
Lemma lem7231384 (f : nat -> real) (g : nat -> real) (n : nat) : (term856 g f n) = (term857 f g n).
Proof. exact (@lem1982747 (term800 f n) (term797 g n)). Qed.
Lemma lem7231385 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7231386 (f : nat -> real) (g : nat -> real) (n : nat) : (term855 g f n) = (term858 f g n).
Proof. exact (MK_COMB (@lem7231385) (@lem7231384 f g n)). Qed.
Lemma lem7231387 (f : nat -> real) (g : nat -> real) (n : nat) : (term854 g f n) = (term858 f g n).
Proof. exact (TRANS (@lem7231383 g f n) (@lem7231386 f g n)). Qed.
Lemma lem7231388 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231389 (f : nat -> real) (g : nat -> real) (n : nat) : (term859 g f n) = (term860 f g n).
Proof. exact (MK_COMB (@lem7231388) (@lem7231387 f g n)). Qed.
Lemma lem7231390 (f : nat -> real) (g : nat -> real) (n : nat) : (term853 g f n) = (term861 f g n).
Proof. exact (MK_COMB (@lem7231389 f g n) (@lem7231382 f g n)). Qed.
Lemma lem7231391 (f : nat -> real) (g : nat -> real) (n : nat) : (term852 g f n) = (term861 f g n).
Proof. exact (TRANS (@lem7231381 g f n) (@lem7231390 f g n)). Qed.
Lemma lem7231392 (f : nat -> real) (g : nat -> real) (n : nat) : (term817 g f n) = (term861 f g n).
Proof. exact (TRANS (@lem7231380 g f n) (@lem7231391 f g n)). Qed.
Lemma lem7231395 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem7231396 (f : nat -> real) (g : nat -> real) (n : nat) : (term818 g f n) = (term862 f g n).
Proof. exact (MK_COMB (@lem7231395) (@lem7231392 f g n)). Qed.
Lemma lem7231397 (f : nat -> real) (g : nat -> real) (n : nat) : (term862 f g n) = (term861 f g n).
Proof. exact (@lem1982721 (term861 f g n)). Qed.
Lemma lem7231398 (f : nat -> real) (g : nat -> real) (n : nat) : (term818 g f n) = (term861 f g n).
Proof. exact (TRANS (@lem7231396 f g n) (@lem7231397 f g n)). Qed.
Lemma lem7231416 (f : nat -> real) (g : nat -> real) (n : nat) : (term815 f g n) = (term863 f g n).
Proof. exact (@lem1982792 (term810 f g n) (term813 f g n)). Qed.
Lemma lem7231421 (f : nat -> real) (g : nat -> real) (n : nat) : (term863 f g n) = (term864 f g n).
Proof. exact (@lem1982761 (term865 f g n) (term810 f g n)). Qed.
Lemma lem7231423 (f : nat -> real) (g : nat -> real) (n : nat) : (term815 f g n) = (term864 f g n).
Proof. exact (TRANS (@lem7231416 f g n) (@lem7231421 f g n)). Qed.
Lemma lem7231424 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231425 (f : nat -> real) (g : nat -> real) (n : nat) : (term816 f g n) = (term866 f g n).
Proof. exact (MK_COMB (@lem7231424) (@lem7231423 f g n)). Qed.
Lemma lem7231426 (f : nat -> real) (g : nat -> real) (n : nat) : (term819 g f n) = (term867 f g n).
Proof. exact (MK_COMB (@lem7231425 f g n) (@lem7231398 f g n)). Qed.
Lemma lem7231427 (f : nat -> real) (g : nat -> real) (n : nat) : (term867 f g n) = (term868 f g n).
Proof. exact (@lem1982792 (term864 f g n) (term861 f g n)). Qed.
Lemma lem7231428 (f : nat -> real) (g : nat -> real) (n : nat) : (term869 f g n) = (term870 f g n).
Proof. exact (@lem1982781 (term858 f g n) term62 (term810 f g n)). Qed.
Lemma lem7231429 (f : nat -> real) (g : nat -> real) (n : nat) : (term871 f g n) = (term871 f g n).
Proof. exact (eq_refl (term871 f g n)). Qed.
Lemma lem7231430 (f : nat -> real) (g : nat -> real) (n : nat) : (term872 f g n) = (term873 f g n).
Proof. exact (@lem1982749 term62 term62 (term857 f g n)). Qed.
Lemma lem7231432 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7231433 : term62 = term63.
Proof. exact (@lem7231432 term13). Qed.
Lemma lem7231435 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7231436 : term62 = term63.
Proof. exact (@lem7231435 term13). Qed.
Lemma lem7231437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231438 : term64 = term65.
Proof. exact (MK_COMB (@lem7231437) (@lem7231436)). Qed.
Lemma lem7231439 : term415 = term416.
Proof. exact (MK_COMB (@lem7231438) (@lem7231433)). Qed.
Lemma lem7231440 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7231442 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231443 : term71 = term72.
Proof. exact (@lem7231442 term13 term13). Qed.
Lemma lem7231444 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231445 : term74 = term13.
Proof. exact (EQ_MP (@lem7231444) (@lem940073)). Qed.
Lemma lem7231446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231447 : term72 = term44.
Proof. exact (MK_COMB (@lem7231446) (@lem7231445)). Qed.
Lemma lem7231448 : term71 = term44.
Proof. exact (TRANS (@lem7231443) (@lem7231447)). Qed.
Lemma lem7231450 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7231451 : term415 = term72.
Proof. exact (@lem7231450 term13 term13). Qed.
Lemma lem7231452 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231453 : term74 = term13.
Proof. exact (EQ_MP (@lem7231452) (@lem940073)). Qed.
Lemma lem7231454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231455 : term72 = term44.
Proof. exact (MK_COMB (@lem7231454) (@lem7231453)). Qed.
Lemma lem7231456 : term415 = term44.
Proof. exact (TRANS (@lem7231451) (@lem7231455)). Qed.
Lemma lem7231457 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7231458 : term419 = term420.
Proof. exact (MK_COMB (@lem7231457) (@lem7231456)). Qed.
Lemma lem7231459 : term417 = term88.
Proof. exact (MK_COMB (@lem7231458) (@lem7231448)). Qed.
Lemma lem7231460 : term416 = term88.
Proof. exact (TRANS (@lem7231440) (@lem7231459)). Qed.
Lemma lem7231461 : term415 = term88.
Proof. exact (TRANS (@lem7231439) (@lem7231460)). Qed.
Lemma lem7231463 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7231464 : term88 = term44.
Proof. exact (@lem7231463 term44). Qed.
Lemma lem7231465 : term415 = term44.
Proof. exact (TRANS (@lem7231461) (@lem7231464)). Qed.
Lemma lem7231466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231467 : term421 = term422.
Proof. exact (MK_COMB (@lem7231466) (@lem7231465)). Qed.
Lemma lem7231468 (f : nat -> real) (g : nat -> real) (n : nat) : (term857 f g n) = (term857 f g n).
Proof. exact (eq_refl (term857 f g n)). Qed.
Lemma lem7231469 (f : nat -> real) (g : nat -> real) (n : nat) : (term873 f g n) = (term874 f g n).
Proof. exact (MK_COMB (@lem7231467) (@lem7231468 f g n)). Qed.
Lemma lem7231470 (f : nat -> real) (g : nat -> real) (n : nat) : (term872 f g n) = (term874 f g n).
Proof. exact (TRANS (@lem7231430 f g n) (@lem7231469 f g n)). Qed.
Lemma lem7231471 (f : nat -> real) (g : nat -> real) (n : nat) : (term874 f g n) = (term857 f g n).
Proof. exact (@lem1982709 (term857 f g n)). Qed.
Lemma lem7231472 (f : nat -> real) (g : nat -> real) (n : nat) : (term872 f g n) = (term857 f g n).
Proof. exact (TRANS (@lem7231470 f g n) (@lem7231471 f g n)). Qed.
Lemma lem7231473 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231474 (f : nat -> real) (g : nat -> real) (n : nat) : (term875 f g n) = (term876 f g n).
Proof. exact (MK_COMB (@lem7231473) (@lem7231472 f g n)). Qed.
Lemma lem7231475 (f : nat -> real) (g : nat -> real) (n : nat) : (term870 f g n) = (term877 f g n).
Proof. exact (MK_COMB (@lem7231474 f g n) (@lem7231429 f g n)). Qed.
Lemma lem7231476 (f : nat -> real) (g : nat -> real) (n : nat) : (term869 f g n) = (term877 f g n).
Proof. exact (TRANS (@lem7231428 f g n) (@lem7231475 f g n)). Qed.
Lemma lem7231477 (f : nat -> real) (g : nat -> real) (n : nat) : (term878 f g n) = (term878 f g n).
Proof. exact (eq_refl (term878 f g n)). Qed.
Lemma lem7231478 (f : nat -> real) (g : nat -> real) (n : nat) : (term868 f g n) = (term879 f g n).
Proof. exact (MK_COMB (@lem7231477 f g n) (@lem7231476 f g n)). Qed.
Lemma lem7231479 (f : nat -> real) (g : nat -> real) (n : nat) : (term879 f g n) = (term880 f g n).
Proof. exact (@lem1982755 (term865 f g n) (term810 f g n) (term877 f g n)). Qed.
Lemma lem7231480 (f : nat -> real) (g : nat -> real) (n : nat) : (term881 f g n) = (term882 f g n).
Proof. exact (@lem1982757 (term857 f g n) (term810 f g n) (term871 f g n)). Qed.
Lemma lem7231481 (f : nat -> real) (g : nat -> real) (n : nat) : (term883 f g n) = (term884 f g n).
Proof. exact (@lem1982715 term62 (term810 f g n)). Qed.
Lemma lem7231483 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7231484 : term44 = term88.
Proof. exact (@lem7231483 term13). Qed.
Lemma lem7231486 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7231487 : term62 = term63.
Proof. exact (@lem7231486 term13). Qed.
Lemma lem7231488 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231489 : term104 = term105.
Proof. exact (MK_COMB (@lem7231488) (@lem7231487)). Qed.
Lemma lem7231490 : term106 = term107.
Proof. exact (MK_COMB (@lem7231489) (@lem7231484)). Qed.
Lemma lem7231491 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7231493 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231494 : term110 = term111.
Proof. exact (@lem7231493 (NUMERAL 0) term13). Qed.
Lemma lem7231495 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231496 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231497 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231496 h1) (fun h1 : term111 = True => @lem7231495)). Qed.
Lemma lem7231498 : term111 = True.
Proof. exact (EQ_MP (@lem7231497) (@lem7231495)). Qed.
Lemma lem7231499 : term110 = True.
Proof. exact (TRANS (@lem7231494) (@lem7231498)). Qed.
Lemma lem7231500 : True = term110.
Proof. exact (SYM (@lem7231499)). Qed.
Lemma lem7231501 : term110.
Proof. exact (EQ_MP (@lem7231500) (@lem0)). Qed.
Lemma lem7231502 : term113.
Proof. exact (@lem7231491 (@lem7231501)). Qed.
Lemma lem7231504 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231505 : term110 = term111.
Proof. exact (@lem7231504 (NUMERAL 0) term13). Qed.
Lemma lem7231506 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231507 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231508 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231507 h1) (fun h1 : term111 = True => @lem7231506)). Qed.
Lemma lem7231509 : term111 = True.
Proof. exact (EQ_MP (@lem7231508) (@lem7231506)). Qed.
Lemma lem7231510 : term110 = True.
Proof. exact (TRANS (@lem7231505) (@lem7231509)). Qed.
Lemma lem7231511 : True = term110.
Proof. exact (SYM (@lem7231510)). Qed.
Lemma lem7231512 : term110.
Proof. exact (EQ_MP (@lem7231511) (@lem0)). Qed.
Lemma lem7231513 : term114.
Proof. exact (@lem7231502 (@lem7231512)). Qed.
Lemma lem7231515 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231516 : term110 = term111.
Proof. exact (@lem7231515 (NUMERAL 0) term13). Qed.
Lemma lem7231517 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231518 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231519 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231518 h1) (fun h1 : term111 = True => @lem7231517)). Qed.
Lemma lem7231520 : term111 = True.
Proof. exact (EQ_MP (@lem7231519) (@lem7231517)). Qed.
Lemma lem7231521 : term110 = True.
Proof. exact (TRANS (@lem7231516) (@lem7231520)). Qed.
Lemma lem7231522 : True = term110.
Proof. exact (SYM (@lem7231521)). Qed.
Lemma lem7231523 : term110.
Proof. exact (EQ_MP (@lem7231522) (@lem0)). Qed.
Lemma lem7231524 : term115.
Proof. exact (@lem7231513 (@lem7231523)). Qed.
Lemma lem7231526 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231527 : term71 = term72.
Proof. exact (@lem7231526 term13 term13). Qed.
Lemma lem7231528 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231529 : term74 = term13.
Proof. exact (EQ_MP (@lem7231528) (@lem940073)). Qed.
Lemma lem7231530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231531 : term72 = term44.
Proof. exact (MK_COMB (@lem7231530) (@lem7231529)). Qed.
Lemma lem7231532 : term71 = term44.
Proof. exact (TRANS (@lem7231527) (@lem7231531)). Qed.
Lemma lem7231534 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7231535 : term89 = term94.
Proof. exact (@lem7231534 term13 term13). Qed.
Lemma lem7231536 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231537 : term74 = term13.
Proof. exact (EQ_MP (@lem7231536) (@lem940073)). Qed.
Lemma lem7231538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231539 : term72 = term44.
Proof. exact (MK_COMB (@lem7231538) (@lem7231537)). Qed.
Lemma lem7231540 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7231541 : term94 = term62.
Proof. exact (MK_COMB (@lem7231540) (@lem7231539)). Qed.
Lemma lem7231542 : term89 = term62.
Proof. exact (TRANS (@lem7231535) (@lem7231541)). Qed.
Lemma lem7231543 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231544 : term116 = term104.
Proof. exact (MK_COMB (@lem7231543) (@lem7231542)). Qed.
Lemma lem7231545 : term117 = term106.
Proof. exact (MK_COMB (@lem7231544) (@lem7231532)). Qed.
Lemma lem7231547 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7231548 : term106 = term29.
Proof. exact (@lem7231547 term13). Qed.
Lemma lem7231549 : term117 = term29.
Proof. exact (TRANS (@lem7231545) (@lem7231548)). Qed.
Lemma lem7231550 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231551 : term119 = term120.
Proof. exact (MK_COMB (@lem7231550) (@lem7231549)). Qed.
Lemma lem7231552 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7231553 : term121 = term122.
Proof. exact (MK_COMB (@lem7231551) (@lem7231552)). Qed.
Lemma lem7231555 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7231556 : term122 = term29.
Proof. exact (@lem7231555 term13). Qed.
Lemma lem7231557 : term121 = term29.
Proof. exact (TRANS (@lem7231553) (@lem7231556)). Qed.
Lemma lem7231559 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231560 : term71 = term72.
Proof. exact (@lem7231559 term13 term13). Qed.
Lemma lem7231561 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231562 : term74 = term13.
Proof. exact (EQ_MP (@lem7231561) (@lem940073)). Qed.
Lemma lem7231563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231564 : term72 = term44.
Proof. exact (MK_COMB (@lem7231563) (@lem7231562)). Qed.
Lemma lem7231565 : term71 = term44.
Proof. exact (TRANS (@lem7231560) (@lem7231564)). Qed.
Lemma lem7231566 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7231567 : term124 = term122.
Proof. exact (MK_COMB (@lem7231566) (@lem7231565)). Qed.
Lemma lem7231569 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7231570 : term122 = term29.
Proof. exact (@lem7231569 term13). Qed.
Lemma lem7231571 : term124 = term29.
Proof. exact (TRANS (@lem7231567) (@lem7231570)). Qed.
Lemma lem7231572 : term29 = term124.
Proof. exact (SYM (@lem7231571)). Qed.
Lemma lem7231573 : term121 = term124.
Proof. exact (TRANS (@lem7231557) (@lem7231572)). Qed.
Lemma lem7231574 : term107 = term59.
Proof. exact (@lem7231524 (@lem7231573)). Qed.
Lemma lem7231575 : term106 = term59.
Proof. exact (TRANS (@lem7231490) (@lem7231574)). Qed.
Lemma lem7231577 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7231578 : term59 = term29.
Proof. exact (@lem7231577 term29). Qed.
Lemma lem7231579 : term106 = term29.
Proof. exact (TRANS (@lem7231575) (@lem7231578)). Qed.
Lemma lem7231580 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231581 : term125 = term120.
Proof. exact (MK_COMB (@lem7231580) (@lem7231579)). Qed.
Lemma lem7231582 (f : nat -> real) (g : nat -> real) (n : nat) : (term810 f g n) = (term810 f g n).
Proof. exact (eq_refl (term810 f g n)). Qed.
Lemma lem7231583 (f : nat -> real) (g : nat -> real) (n : nat) : (term884 f g n) = (term885 f g n).
Proof. exact (MK_COMB (@lem7231581) (@lem7231582 f g n)). Qed.
Lemma lem7231584 (f : nat -> real) (g : nat -> real) (n : nat) : (term883 f g n) = (term885 f g n).
Proof. exact (TRANS (@lem7231481 f g n) (@lem7231583 f g n)). Qed.
Lemma lem7231585 (f : nat -> real) (g : nat -> real) (n : nat) : (term885 f g n) = term29.
Proof. exact (@lem1982719 (term810 f g n)). Qed.
Lemma lem7231586 (f : nat -> real) (g : nat -> real) (n : nat) : (term883 f g n) = term29.
Proof. exact (TRANS (@lem7231584 f g n) (@lem7231585 f g n)). Qed.
Lemma lem7231587 (f : nat -> real) (g : nat -> real) (n : nat) : (term876 f g n) = (term876 f g n).
Proof. exact (eq_refl (term876 f g n)). Qed.
Lemma lem7231588 (f : nat -> real) (g : nat -> real) (n : nat) : (term882 f g n) = (term886 f g n).
Proof. exact (MK_COMB (@lem7231587 f g n) (@lem7231586 f g n)). Qed.
Lemma lem7231589 (f : nat -> real) (g : nat -> real) (n : nat) : (term881 f g n) = (term886 f g n).
Proof. exact (TRANS (@lem7231480 f g n) (@lem7231588 f g n)). Qed.
Lemma lem7231590 (f : nat -> real) (g : nat -> real) (n : nat) : (term886 f g n) = (term857 f g n).
Proof. exact (@lem1982723 (term857 f g n)). Qed.
Lemma lem7231591 (f : nat -> real) (g : nat -> real) (n : nat) : (term881 f g n) = (term857 f g n).
Proof. exact (TRANS (@lem7231589 f g n) (@lem7231590 f g n)). Qed.
Lemma lem7231592 (f : nat -> real) (g : nat -> real) (n : nat) : (term887 f g n) = (term887 f g n).
Proof. exact (eq_refl (term887 f g n)). Qed.
Lemma lem7231593 (f : nat -> real) (g : nat -> real) (n : nat) : (term880 f g n) = (term888 f g n).
Proof. exact (MK_COMB (@lem7231592 f g n) (@lem7231591 f g n)). Qed.
Lemma lem7231594 (f : nat -> real) (g : nat -> real) (n : nat) : (term879 f g n) = (term888 f g n).
Proof. exact (TRANS (@lem7231479 f g n) (@lem7231593 f g n)). Qed.
Lemma lem7231595 (f : nat -> real) (g : nat -> real) (n : nat) : (term868 f g n) = (term888 f g n).
Proof. exact (TRANS (@lem7231478 f g n) (@lem7231594 f g n)). Qed.
Lemma lem7231596 (f : nat -> real) (g : nat -> real) (n : nat) : (term867 f g n) = (term888 f g n).
Proof. exact (TRANS (@lem7231427 f g n) (@lem7231595 f g n)). Qed.
Lemma lem7231597 (f : nat -> real) (g : nat -> real) (n : nat) : (term819 g f n) = (term888 f g n).
Proof. exact (TRANS (@lem7231426 f g n) (@lem7231596 f g n)). Qed.
Lemma lem7231603 (g : nat -> real) (n : nat) : (term802 g n) = (term849 g n).
Proof. exact (@lem1982792 (term797 g n) (term800 g n)). Qed.
Lemma lem7231608 (g : nat -> real) (n : nat) : (term849 g n) = (term850 g n).
Proof. exact (@lem1982761 (term851 g n) (term797 g n)). Qed.
Lemma lem7231610 (g : nat -> real) (n : nat) : (term802 g n) = (term850 g n).
Proof. exact (TRANS (@lem7231603 g n) (@lem7231608 g n)). Qed.
Lemma lem7231613 (f : nat -> real) (n : nat) : (term803 f n) = (term803 f n).
Proof. exact (eq_refl (term803 f n)). Qed.
Lemma lem7231614 (f : nat -> real) (g : nat -> real) (n : nat) : (term804 f g n) = (term889 f g n).
Proof. exact (MK_COMB (@lem7231613 f n) (@lem7231610 g n)). Qed.
Lemma lem7231615 (f : nat -> real) (g : nat -> real) (n : nat) : (term889 f g n) = (term890 f g n).
Proof. exact (@lem1982781 (term851 g n) (term800 f n) (term797 g n)). Qed.
Lemma lem7231616 (f : nat -> real) (g : nat -> real) (n : nat) : (term857 f g n) = (term857 f g n).
Proof. exact (eq_refl (term857 f g n)). Qed.
Lemma lem7231621 (f : nat -> real) (g : nat -> real) (n : nat) : (term891 f g n) = (term865 f g n).
Proof. exact (@lem1982751 term62 (term800 f n) (term800 g n)). Qed.
Lemma lem7231622 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231623 (f : nat -> real) (g : nat -> real) (n : nat) : (term892 f g n) = (term887 f g n).
Proof. exact (MK_COMB (@lem7231622) (@lem7231621 f g n)). Qed.
Lemma lem7231624 (f : nat -> real) (g : nat -> real) (n : nat) : (term890 f g n) = (term888 f g n).
Proof. exact (MK_COMB (@lem7231623 f g n) (@lem7231616 f g n)). Qed.
Lemma lem7231625 (f : nat -> real) (g : nat -> real) (n : nat) : (term889 f g n) = (term888 f g n).
Proof. exact (TRANS (@lem7231615 f g n) (@lem7231624 f g n)). Qed.
Lemma lem7231626 (f : nat -> real) (g : nat -> real) (n : nat) : (term804 f g n) = (term888 f g n).
Proof. exact (TRANS (@lem7231614 f g n) (@lem7231625 f g n)). Qed.
Lemma lem7231629 : term128 = term128.
Proof. exact (eq_refl term128). Qed.
Lemma lem7231630 (f : nat -> real) (g : nat -> real) (n : nat) : (term805 f g n) = (term893 f g n).
Proof. exact (MK_COMB (@lem7231629) (@lem7231626 f g n)). Qed.
Lemma lem7231631 (f : nat -> real) (g : nat -> real) (n : nat) : (term893 f g n) = (term888 f g n).
Proof. exact (@lem1982721 (term888 f g n)). Qed.
Lemma lem7231632 (f : nat -> real) (g : nat -> real) (n : nat) : (term805 f g n) = (term888 f g n).
Proof. exact (TRANS (@lem7231630 f g n) (@lem7231631 f g n)). Qed.
Lemma lem7231633 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7231634 (f : nat -> real) (g : nat -> real) (n : nat) : (term894 f g n) = (term895 f g n).
Proof. exact (MK_COMB (@lem7231633) (@lem7231632 f g n)). Qed.
Lemma lem7231635 (f : nat -> real) (g : nat -> real) (n : nat) : (term896 g f n) = (term897 f g n).
Proof. exact (MK_COMB (@lem7231634 f g n) (@lem7231597 f g n)). Qed.
Lemma lem7231636 (f : nat -> real) (g : nat -> real) (n : nat) : (term897 f g n) = (term898 f g n).
Proof. exact (@lem1982792 (term888 f g n) (term888 f g n)). Qed.
Lemma lem7231637 (f : nat -> real) (g : nat -> real) (n : nat) : (term899 f g n) = (term900 f g n).
Proof. exact (@lem1982781 (term865 f g n) term62 (term857 f g n)). Qed.
Lemma lem7231638 (f : nat -> real) (g : nat -> real) (n : nat) : (term858 f g n) = (term858 f g n).
Proof. exact (eq_refl (term858 f g n)). Qed.
Lemma lem7231639 (f : nat -> real) (g : nat -> real) (n : nat) : (term901 f g n) = (term902 f g n).
Proof. exact (@lem1982749 term62 term62 (term813 f g n)). Qed.
Lemma lem7231641 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7231642 : term62 = term63.
Proof. exact (@lem7231641 term13). Qed.
Lemma lem7231644 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7231645 : term62 = term63.
Proof. exact (@lem7231644 term13). Qed.
Lemma lem7231646 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231647 : term64 = term65.
Proof. exact (MK_COMB (@lem7231646) (@lem7231645)). Qed.
Lemma lem7231648 : term415 = term416.
Proof. exact (MK_COMB (@lem7231647) (@lem7231642)). Qed.
Lemma lem7231649 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7231651 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231652 : term71 = term72.
Proof. exact (@lem7231651 term13 term13). Qed.
Lemma lem7231653 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231654 : term74 = term13.
Proof. exact (EQ_MP (@lem7231653) (@lem940073)). Qed.
Lemma lem7231655 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231656 : term72 = term44.
Proof. exact (MK_COMB (@lem7231655) (@lem7231654)). Qed.
Lemma lem7231657 : term71 = term44.
Proof. exact (TRANS (@lem7231652) (@lem7231656)). Qed.
Lemma lem7231659 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7231660 : term415 = term72.
Proof. exact (@lem7231659 term13 term13). Qed.
Lemma lem7231661 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231662 : term74 = term13.
Proof. exact (EQ_MP (@lem7231661) (@lem940073)). Qed.
Lemma lem7231663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231664 : term72 = term44.
Proof. exact (MK_COMB (@lem7231663) (@lem7231662)). Qed.
Lemma lem7231665 : term415 = term44.
Proof. exact (TRANS (@lem7231660) (@lem7231664)). Qed.
Lemma lem7231666 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7231667 : term419 = term420.
Proof. exact (MK_COMB (@lem7231666) (@lem7231665)). Qed.
Lemma lem7231668 : term417 = term88.
Proof. exact (MK_COMB (@lem7231667) (@lem7231657)). Qed.
Lemma lem7231669 : term416 = term88.
Proof. exact (TRANS (@lem7231649) (@lem7231668)). Qed.
Lemma lem7231670 : term415 = term88.
Proof. exact (TRANS (@lem7231648) (@lem7231669)). Qed.
Lemma lem7231672 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7231673 : term88 = term44.
Proof. exact (@lem7231672 term44). Qed.
Lemma lem7231674 : term415 = term44.
Proof. exact (TRANS (@lem7231670) (@lem7231673)). Qed.
Lemma lem7231675 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231676 : term421 = term422.
Proof. exact (MK_COMB (@lem7231675) (@lem7231674)). Qed.
Lemma lem7231677 (f : nat -> real) (g : nat -> real) (n : nat) : (term813 f g n) = (term813 f g n).
Proof. exact (eq_refl (term813 f g n)). Qed.
Lemma lem7231678 (f : nat -> real) (g : nat -> real) (n : nat) : (term902 f g n) = (term903 f g n).
Proof. exact (MK_COMB (@lem7231676) (@lem7231677 f g n)). Qed.
Lemma lem7231679 (f : nat -> real) (g : nat -> real) (n : nat) : (term901 f g n) = (term903 f g n).
Proof. exact (TRANS (@lem7231639 f g n) (@lem7231678 f g n)). Qed.
Lemma lem7231680 (f : nat -> real) (g : nat -> real) (n : nat) : (term903 f g n) = (term813 f g n).
Proof. exact (@lem1982709 (term813 f g n)). Qed.
Lemma lem7231681 (f : nat -> real) (g : nat -> real) (n : nat) : (term901 f g n) = (term813 f g n).
Proof. exact (TRANS (@lem7231679 f g n) (@lem7231680 f g n)). Qed.
Lemma lem7231682 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231683 (f : nat -> real) (g : nat -> real) (n : nat) : (term904 f g n) = (term905 f g n).
Proof. exact (MK_COMB (@lem7231682) (@lem7231681 f g n)). Qed.
Lemma lem7231684 (f : nat -> real) (g : nat -> real) (n : nat) : (term900 f g n) = (term906 f g n).
Proof. exact (MK_COMB (@lem7231683 f g n) (@lem7231638 f g n)). Qed.
Lemma lem7231685 (f : nat -> real) (g : nat -> real) (n : nat) : (term899 f g n) = (term906 f g n).
Proof. exact (TRANS (@lem7231637 f g n) (@lem7231684 f g n)). Qed.
Lemma lem7231686 (f : nat -> real) (g : nat -> real) (n : nat) : (term907 f g n) = (term907 f g n).
Proof. exact (eq_refl (term907 f g n)). Qed.
Lemma lem7231687 (f : nat -> real) (g : nat -> real) (n : nat) : (term898 f g n) = (term908 f g n).
Proof. exact (MK_COMB (@lem7231686 f g n) (@lem7231685 f g n)). Qed.
Lemma lem7231688 (f : nat -> real) (g : nat -> real) (n : nat) : (term908 f g n) = (term909 f g n).
Proof. exact (@lem1982753 (term865 f g n) (term813 f g n) (term857 f g n) (term858 f g n)). Qed.
Lemma lem7231689 (f : nat -> real) (g : nat -> real) (n : nat) : (term910 f g n) = (term911 f g n).
Proof. exact (@lem1982713 term62 (term813 f g n)). Qed.
Lemma lem7231691 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7231692 : term44 = term88.
Proof. exact (@lem7231691 term13). Qed.
Lemma lem7231694 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7231695 : term62 = term63.
Proof. exact (@lem7231694 term13). Qed.
Lemma lem7231696 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231697 : term104 = term105.
Proof. exact (MK_COMB (@lem7231696) (@lem7231695)). Qed.
Lemma lem7231698 : term106 = term107.
Proof. exact (MK_COMB (@lem7231697) (@lem7231692)). Qed.
Lemma lem7231699 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7231701 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231702 : term110 = term111.
Proof. exact (@lem7231701 (NUMERAL 0) term13). Qed.
Lemma lem7231703 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231704 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231705 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231704 h1) (fun h1 : term111 = True => @lem7231703)). Qed.
Lemma lem7231706 : term111 = True.
Proof. exact (EQ_MP (@lem7231705) (@lem7231703)). Qed.
Lemma lem7231707 : term110 = True.
Proof. exact (TRANS (@lem7231702) (@lem7231706)). Qed.
Lemma lem7231708 : True = term110.
Proof. exact (SYM (@lem7231707)). Qed.
Lemma lem7231709 : term110.
Proof. exact (EQ_MP (@lem7231708) (@lem0)). Qed.
Lemma lem7231710 : term113.
Proof. exact (@lem7231699 (@lem7231709)). Qed.
Lemma lem7231712 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231713 : term110 = term111.
Proof. exact (@lem7231712 (NUMERAL 0) term13). Qed.
Lemma lem7231714 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231715 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231716 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231715 h1) (fun h1 : term111 = True => @lem7231714)). Qed.
Lemma lem7231717 : term111 = True.
Proof. exact (EQ_MP (@lem7231716) (@lem7231714)). Qed.
Lemma lem7231718 : term110 = True.
Proof. exact (TRANS (@lem7231713) (@lem7231717)). Qed.
Lemma lem7231719 : True = term110.
Proof. exact (SYM (@lem7231718)). Qed.
Lemma lem7231720 : term110.
Proof. exact (EQ_MP (@lem7231719) (@lem0)). Qed.
Lemma lem7231721 : term114.
Proof. exact (@lem7231710 (@lem7231720)). Qed.
Lemma lem7231723 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231724 : term110 = term111.
Proof. exact (@lem7231723 (NUMERAL 0) term13). Qed.
Lemma lem7231725 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231726 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231727 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231726 h1) (fun h1 : term111 = True => @lem7231725)). Qed.
Lemma lem7231728 : term111 = True.
Proof. exact (EQ_MP (@lem7231727) (@lem7231725)). Qed.
Lemma lem7231729 : term110 = True.
Proof. exact (TRANS (@lem7231724) (@lem7231728)). Qed.
Lemma lem7231730 : True = term110.
Proof. exact (SYM (@lem7231729)). Qed.
Lemma lem7231731 : term110.
Proof. exact (EQ_MP (@lem7231730) (@lem0)). Qed.
Lemma lem7231732 : term115.
Proof. exact (@lem7231721 (@lem7231731)). Qed.
Lemma lem7231734 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231735 : term71 = term72.
Proof. exact (@lem7231734 term13 term13). Qed.
Lemma lem7231736 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231737 : term74 = term13.
Proof. exact (EQ_MP (@lem7231736) (@lem940073)). Qed.
Lemma lem7231738 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231739 : term72 = term44.
Proof. exact (MK_COMB (@lem7231738) (@lem7231737)). Qed.
Lemma lem7231740 : term71 = term44.
Proof. exact (TRANS (@lem7231735) (@lem7231739)). Qed.
Lemma lem7231742 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7231743 : term89 = term94.
Proof. exact (@lem7231742 term13 term13). Qed.
Lemma lem7231744 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231745 : term74 = term13.
Proof. exact (EQ_MP (@lem7231744) (@lem940073)). Qed.
Lemma lem7231746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231747 : term72 = term44.
Proof. exact (MK_COMB (@lem7231746) (@lem7231745)). Qed.
Lemma lem7231748 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7231749 : term94 = term62.
Proof. exact (MK_COMB (@lem7231748) (@lem7231747)). Qed.
Lemma lem7231750 : term89 = term62.
Proof. exact (TRANS (@lem7231743) (@lem7231749)). Qed.
Lemma lem7231751 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231752 : term116 = term104.
Proof. exact (MK_COMB (@lem7231751) (@lem7231750)). Qed.
Lemma lem7231753 : term117 = term106.
Proof. exact (MK_COMB (@lem7231752) (@lem7231740)). Qed.
Lemma lem7231755 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7231756 : term106 = term29.
Proof. exact (@lem7231755 term13). Qed.
Lemma lem7231757 : term117 = term29.
Proof. exact (TRANS (@lem7231753) (@lem7231756)). Qed.
Lemma lem7231758 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231759 : term119 = term120.
Proof. exact (MK_COMB (@lem7231758) (@lem7231757)). Qed.
Lemma lem7231760 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7231761 : term121 = term122.
Proof. exact (MK_COMB (@lem7231759) (@lem7231760)). Qed.
Lemma lem7231763 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7231764 : term122 = term29.
Proof. exact (@lem7231763 term13). Qed.
Lemma lem7231765 : term121 = term29.
Proof. exact (TRANS (@lem7231761) (@lem7231764)). Qed.
Lemma lem7231767 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231768 : term71 = term72.
Proof. exact (@lem7231767 term13 term13). Qed.
Lemma lem7231769 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231770 : term74 = term13.
Proof. exact (EQ_MP (@lem7231769) (@lem940073)). Qed.
Lemma lem7231771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231772 : term72 = term44.
Proof. exact (MK_COMB (@lem7231771) (@lem7231770)). Qed.
Lemma lem7231773 : term71 = term44.
Proof. exact (TRANS (@lem7231768) (@lem7231772)). Qed.
Lemma lem7231774 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7231775 : term124 = term122.
Proof. exact (MK_COMB (@lem7231774) (@lem7231773)). Qed.
Lemma lem7231777 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7231778 : term122 = term29.
Proof. exact (@lem7231777 term13). Qed.
Lemma lem7231779 : term124 = term29.
Proof. exact (TRANS (@lem7231775) (@lem7231778)). Qed.
Lemma lem7231780 : term29 = term124.
Proof. exact (SYM (@lem7231779)). Qed.
Lemma lem7231781 : term121 = term124.
Proof. exact (TRANS (@lem7231765) (@lem7231780)). Qed.
Lemma lem7231782 : term107 = term59.
Proof. exact (@lem7231732 (@lem7231781)). Qed.
Lemma lem7231783 : term106 = term59.
Proof. exact (TRANS (@lem7231698) (@lem7231782)). Qed.
Lemma lem7231785 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7231786 : term59 = term29.
Proof. exact (@lem7231785 term29). Qed.
Lemma lem7231787 : term106 = term29.
Proof. exact (TRANS (@lem7231783) (@lem7231786)). Qed.
Lemma lem7231788 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231789 : term125 = term120.
Proof. exact (MK_COMB (@lem7231788) (@lem7231787)). Qed.
Lemma lem7231790 (f : nat -> real) (g : nat -> real) (n : nat) : (term813 f g n) = (term813 f g n).
Proof. exact (eq_refl (term813 f g n)). Qed.
Lemma lem7231791 (f : nat -> real) (g : nat -> real) (n : nat) : (term911 f g n) = (term912 f g n).
Proof. exact (MK_COMB (@lem7231789) (@lem7231790 f g n)). Qed.
Lemma lem7231792 (f : nat -> real) (g : nat -> real) (n : nat) : (term910 f g n) = (term912 f g n).
Proof. exact (TRANS (@lem7231689 f g n) (@lem7231791 f g n)). Qed.
Lemma lem7231793 (f : nat -> real) (g : nat -> real) (n : nat) : (term912 f g n) = term29.
Proof. exact (@lem1982719 (term813 f g n)). Qed.
Lemma lem7231794 (f : nat -> real) (g : nat -> real) (n : nat) : (term910 f g n) = term29.
Proof. exact (TRANS (@lem7231792 f g n) (@lem7231793 f g n)). Qed.
Lemma lem7231795 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231796 (f : nat -> real) (g : nat -> real) (n : nat) : (term913 f g n) = term128.
Proof. exact (MK_COMB (@lem7231795) (@lem7231794 f g n)). Qed.
Lemma lem7231797 (f : nat -> real) (g : nat -> real) (n : nat) : (term914 f g n) = (term915 f g n).
Proof. exact (@lem1982715 term62 (term857 f g n)). Qed.
Lemma lem7231799 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7231800 : term44 = term88.
Proof. exact (@lem7231799 term13). Qed.
Lemma lem7231802 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7231803 : term62 = term63.
Proof. exact (@lem7231802 term13). Qed.
Lemma lem7231804 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231805 : term104 = term105.
Proof. exact (MK_COMB (@lem7231804) (@lem7231803)). Qed.
Lemma lem7231806 : term106 = term107.
Proof. exact (MK_COMB (@lem7231805) (@lem7231800)). Qed.
Lemma lem7231807 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7231809 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231810 : term110 = term111.
Proof. exact (@lem7231809 (NUMERAL 0) term13). Qed.
Lemma lem7231811 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231812 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231813 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231812 h1) (fun h1 : term111 = True => @lem7231811)). Qed.
Lemma lem7231814 : term111 = True.
Proof. exact (EQ_MP (@lem7231813) (@lem7231811)). Qed.
Lemma lem7231815 : term110 = True.
Proof. exact (TRANS (@lem7231810) (@lem7231814)). Qed.
Lemma lem7231816 : True = term110.
Proof. exact (SYM (@lem7231815)). Qed.
Lemma lem7231817 : term110.
Proof. exact (EQ_MP (@lem7231816) (@lem0)). Qed.
Lemma lem7231818 : term113.
Proof. exact (@lem7231807 (@lem7231817)). Qed.
Lemma lem7231820 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231821 : term110 = term111.
Proof. exact (@lem7231820 (NUMERAL 0) term13). Qed.
Lemma lem7231822 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231823 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231824 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231823 h1) (fun h1 : term111 = True => @lem7231822)). Qed.
Lemma lem7231825 : term111 = True.
Proof. exact (EQ_MP (@lem7231824) (@lem7231822)). Qed.
Lemma lem7231826 : term110 = True.
Proof. exact (TRANS (@lem7231821) (@lem7231825)). Qed.
Lemma lem7231827 : True = term110.
Proof. exact (SYM (@lem7231826)). Qed.
Lemma lem7231828 : term110.
Proof. exact (EQ_MP (@lem7231827) (@lem0)). Qed.
Lemma lem7231829 : term114.
Proof. exact (@lem7231818 (@lem7231828)). Qed.
Lemma lem7231831 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231832 : term110 = term111.
Proof. exact (@lem7231831 (NUMERAL 0) term13). Qed.
Lemma lem7231833 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7231834 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7231835 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7231834 h1) (fun h1 : term111 = True => @lem7231833)). Qed.
Lemma lem7231836 : term111 = True.
Proof. exact (EQ_MP (@lem7231835) (@lem7231833)). Qed.
Lemma lem7231837 : term110 = True.
Proof. exact (TRANS (@lem7231832) (@lem7231836)). Qed.
Lemma lem7231838 : True = term110.
Proof. exact (SYM (@lem7231837)). Qed.
Lemma lem7231839 : term110.
Proof. exact (EQ_MP (@lem7231838) (@lem0)). Qed.
Lemma lem7231840 : term115.
Proof. exact (@lem7231829 (@lem7231839)). Qed.
Lemma lem7231842 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231843 : term71 = term72.
Proof. exact (@lem7231842 term13 term13). Qed.
Lemma lem7231844 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231845 : term74 = term13.
Proof. exact (EQ_MP (@lem7231844) (@lem940073)). Qed.
Lemma lem7231846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231847 : term72 = term44.
Proof. exact (MK_COMB (@lem7231846) (@lem7231845)). Qed.
Lemma lem7231848 : term71 = term44.
Proof. exact (TRANS (@lem7231843) (@lem7231847)). Qed.
Lemma lem7231850 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7231851 : term89 = term94.
Proof. exact (@lem7231850 term13 term13). Qed.
Lemma lem7231852 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231853 : term74 = term13.
Proof. exact (EQ_MP (@lem7231852) (@lem940073)). Qed.
Lemma lem7231854 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231855 : term72 = term44.
Proof. exact (MK_COMB (@lem7231854) (@lem7231853)). Qed.
Lemma lem7231856 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7231857 : term94 = term62.
Proof. exact (MK_COMB (@lem7231856) (@lem7231855)). Qed.
Lemma lem7231858 : term89 = term62.
Proof. exact (TRANS (@lem7231851) (@lem7231857)). Qed.
Lemma lem7231859 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7231860 : term116 = term104.
Proof. exact (MK_COMB (@lem7231859) (@lem7231858)). Qed.
Lemma lem7231861 : term117 = term106.
Proof. exact (MK_COMB (@lem7231860) (@lem7231848)). Qed.
Lemma lem7231863 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7231864 : term106 = term29.
Proof. exact (@lem7231863 term13). Qed.
Lemma lem7231865 : term117 = term29.
Proof. exact (TRANS (@lem7231861) (@lem7231864)). Qed.
Lemma lem7231866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231867 : term119 = term120.
Proof. exact (MK_COMB (@lem7231866) (@lem7231865)). Qed.
Lemma lem7231868 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7231869 : term121 = term122.
Proof. exact (MK_COMB (@lem7231867) (@lem7231868)). Qed.
Lemma lem7231871 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7231872 : term122 = term29.
Proof. exact (@lem7231871 term13). Qed.
Lemma lem7231873 : term121 = term29.
Proof. exact (TRANS (@lem7231869) (@lem7231872)). Qed.
Lemma lem7231875 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231876 : term71 = term72.
Proof. exact (@lem7231875 term13 term13). Qed.
Lemma lem7231877 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231878 : term74 = term13.
Proof. exact (EQ_MP (@lem7231877) (@lem940073)). Qed.
Lemma lem7231879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231880 : term72 = term44.
Proof. exact (MK_COMB (@lem7231879) (@lem7231878)). Qed.
Lemma lem7231881 : term71 = term44.
Proof. exact (TRANS (@lem7231876) (@lem7231880)). Qed.
Lemma lem7231882 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7231883 : term124 = term122.
Proof. exact (MK_COMB (@lem7231882) (@lem7231881)). Qed.
Lemma lem7231885 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7231886 : term122 = term29.
Proof. exact (@lem7231885 term13). Qed.
Lemma lem7231887 : term124 = term29.
Proof. exact (TRANS (@lem7231883) (@lem7231886)). Qed.
Lemma lem7231888 : term29 = term124.
Proof. exact (SYM (@lem7231887)). Qed.
Lemma lem7231889 : term121 = term124.
Proof. exact (TRANS (@lem7231873) (@lem7231888)). Qed.
Lemma lem7231890 : term107 = term59.
Proof. exact (@lem7231840 (@lem7231889)). Qed.
Lemma lem7231891 : term106 = term59.
Proof. exact (TRANS (@lem7231806) (@lem7231890)). Qed.
Lemma lem7231893 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7231894 : term59 = term29.
Proof. exact (@lem7231893 term29). Qed.
Lemma lem7231895 : term106 = term29.
Proof. exact (TRANS (@lem7231891) (@lem7231894)). Qed.
Lemma lem7231896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231897 : term125 = term120.
Proof. exact (MK_COMB (@lem7231896) (@lem7231895)). Qed.
Lemma lem7231898 (f : nat -> real) (g : nat -> real) (n : nat) : (term857 f g n) = (term857 f g n).
Proof. exact (eq_refl (term857 f g n)). Qed.
Lemma lem7231899 (f : nat -> real) (g : nat -> real) (n : nat) : (term915 f g n) = (term916 f g n).
Proof. exact (MK_COMB (@lem7231897) (@lem7231898 f g n)). Qed.
Lemma lem7231900 (f : nat -> real) (g : nat -> real) (n : nat) : (term914 f g n) = (term916 f g n).
Proof. exact (TRANS (@lem7231797 f g n) (@lem7231899 f g n)). Qed.
Lemma lem7231901 (f : nat -> real) (g : nat -> real) (n : nat) : (term916 f g n) = term29.
Proof. exact (@lem1982719 (term857 f g n)). Qed.
Lemma lem7231902 (f : nat -> real) (g : nat -> real) (n : nat) : (term914 f g n) = term29.
Proof. exact (TRANS (@lem7231900 f g n) (@lem7231901 f g n)). Qed.
Lemma lem7231903 (f : nat -> real) (g : nat -> real) (n : nat) : (term909 f g n) = term465.
Proof. exact (MK_COMB (@lem7231796 f g n) (@lem7231902 f g n)). Qed.
Lemma lem7231904 (f : nat -> real) (g : nat -> real) (n : nat) : (term908 f g n) = term465.
Proof. exact (TRANS (@lem7231688 f g n) (@lem7231903 f g n)). Qed.
Lemma lem7231905 : term465 = term29.
Proof. exact (@lem1982721 term29). Qed.
Lemma lem7231906 (f : nat -> real) (g : nat -> real) (n : nat) : (term908 f g n) = term29.
Proof. exact (TRANS (@lem7231904 f g n) (@lem7231905)). Qed.
Lemma lem7231907 (f : nat -> real) (g : nat -> real) (n : nat) : (term898 f g n) = term29.
Proof. exact (TRANS (@lem7231687 f g n) (@lem7231906 f g n)). Qed.
Lemma lem7231908 (f : nat -> real) (g : nat -> real) (n : nat) : (term897 f g n) = term29.
Proof. exact (TRANS (@lem7231636 f g n) (@lem7231907 f g n)). Qed.
Lemma lem7231909 (g : nat -> real) (f : nat -> real) (n : nat) : (term896 g f n) = term29.
Proof. exact (TRANS (@lem7231635 f g n) (@lem7231908 f g n)). Qed.
Lemma lem7231910 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7231911 (g : nat -> real) (f : nat -> real) (n : nat) : (term917 g f n) = term467.
Proof. exact (MK_COMB (@lem7231910) (@lem7231909 g f n)). Qed.
Lemma lem7231912 : term467 = term66.
Proof. exact (@lem1982785 term29). Qed.
Lemma lem7231914 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7231915 : term29 = term59.
Proof. exact (@lem7231914 (NUMERAL 0)). Qed.
Lemma lem7231917 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7231918 : term62 = term63.
Proof. exact (@lem7231917 term13). Qed.
Lemma lem7231919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7231920 : term64 = term65.
Proof. exact (MK_COMB (@lem7231919) (@lem7231918)). Qed.
Lemma lem7231921 : term66 = term67.
Proof. exact (MK_COMB (@lem7231920) (@lem7231915)). Qed.
Lemma lem7231922 : term67 = term68.
Proof. exact (@lem1981613 term62 term29 term44 term44). Qed.
Lemma lem7231924 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7231925 : term71 = term72.
Proof. exact (@lem7231924 term13 term13). Qed.
Lemma lem7231926 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7231927 : term74 = term13.
Proof. exact (EQ_MP (@lem7231926) (@lem940073)). Qed.
Lemma lem7231928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7231929 : term72 = term44.
Proof. exact (MK_COMB (@lem7231928) (@lem7231927)). Qed.
Lemma lem7231930 : term71 = term44.
Proof. exact (TRANS (@lem7231925) (@lem7231929)). Qed.
Lemma lem7231932 (x : nat) : (term75 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7231933 : term66 = term29.
Proof. exact (@lem7231932 term13). Qed.
Lemma lem7231934 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7231935 : term76 = term77.
Proof. exact (MK_COMB (@lem7231934) (@lem7231933)). Qed.
Lemma lem7231936 : term68 = term59.
Proof. exact (MK_COMB (@lem7231935) (@lem7231930)). Qed.
Lemma lem7231937 : term67 = term59.
Proof. exact (TRANS (@lem7231922) (@lem7231936)). Qed.
Lemma lem7231938 : term66 = term59.
Proof. exact (TRANS (@lem7231921) (@lem7231937)). Qed.
Lemma lem7231940 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7231941 : term59 = term29.
Proof. exact (@lem7231940 term29). Qed.
Lemma lem7231942 : term66 = term29.
Proof. exact (TRANS (@lem7231938) (@lem7231941)). Qed.
Lemma lem7231943 : term467 = term29.
Proof. exact (TRANS (@lem7231912) (@lem7231942)). Qed.
Lemma lem7231944 (g : nat -> real) (f : nat -> real) (n : nat) : (term918 g f n) = (term918 g f n).
Proof. exact (eq_refl (term918 g f n)). Qed.
Lemma lem7231945 (g : nat -> real) (f : nat -> real) (n : nat) : ((term917 g f n) = term467) = ((term917 g f n) = term29).
Proof. exact (MK_COMB (@lem7231944 g f n) (@lem7231943)). Qed.
Lemma lem7231946 (g : nat -> real) (f : nat -> real) (n : nat) : (term917 g f n) = term29.
Proof. exact (EQ_MP (@lem7231945 g f n) (@lem7231911 g f n)). Qed.
Lemma lem7231947 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7231948 (g : nat -> real) (f : nat -> real) (n : nat) : (term919 g f n) = term470.
Proof. exact (MK_COMB (@lem7231947) (@lem7231946 g f n)). Qed.
Lemma lem7231949 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7231950 (g : nat -> real) (f : nat -> real) (n : nat) : (term920 g f n) = term472.
Proof. exact (MK_COMB (@lem7231948 g f n) (@lem7231949)). Qed.
Lemma lem7231951 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7231952 (g : nat -> real) (f : nat -> real) (n : nat) : (term921 g f n) = term470.
Proof. exact (MK_COMB (@lem7231951) (@lem7231909 g f n)). Qed.
Lemma lem7231953 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7231954 (g : nat -> real) (f : nat -> real) (n : nat) : (term922 g f n) = term472.
Proof. exact (MK_COMB (@lem7231952 g f n) (@lem7231953)). Qed.
Lemma lem7231955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7231956 (g : nat -> real) (f : nat -> real) (n : nat) : (term923 g f n) = term476.
Proof. exact (MK_COMB (@lem7231955) (@lem7231954 g f n)). Qed.
Lemma lem7231957 (g : nat -> real) (f : nat -> real) (n : nat) : (term848 g f n) = term477.
Proof. exact (MK_COMB (@lem7231956 g f n) (@lem7231950 g f n)). Qed.
Lemma lem7231971 (g : nat -> real) (f : nat -> real) (n : nat) : (term847 g f n) = term477.
Proof. exact (TRANS (@lem7231363 g f n) (@lem7231957 g f n)). Qed.
Lemma lem7231981 (h1 : term477) : term477.
Proof. exact (h1). Qed.
Lemma lem7231982 (h1 : term472) : term472.
Proof. exact (h1). Qed.
Lemma lem7231984 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7231985 : term472 = term478.
Proof. exact (@lem7231984 term29 term29). Qed.
Lemma lem7231987 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7231988 : term29 = term59.
Proof. exact (@lem7231987 (NUMERAL 0)). Qed.
Lemma lem7231990 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7231991 : term29 = term59.
Proof. exact (@lem7231990 (NUMERAL 0)). Qed.
Lemma lem7231992 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7231993 : term479 = term480.
Proof. exact (MK_COMB (@lem7231992) (@lem7231991)). Qed.
Lemma lem7231994 : term478 = term481.
Proof. exact (MK_COMB (@lem7231993) (@lem7231988)). Qed.
Lemma lem7231995 : term482.
Proof. exact (@lem1980255 term29 term44 term29 term44). Qed.
Lemma lem7231997 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7231998 : term110 = term111.
Proof. exact (@lem7231997 (NUMERAL 0) term13). Qed.
Lemma lem7231999 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232000 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232001 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232000 h1) (fun h1 : term111 = True => @lem7231999)). Qed.
Lemma lem7232002 : term111 = True.
Proof. exact (EQ_MP (@lem7232001) (@lem7231999)). Qed.
Lemma lem7232003 : term110 = True.
Proof. exact (TRANS (@lem7231998) (@lem7232002)). Qed.
Lemma lem7232004 : True = term110.
Proof. exact (SYM (@lem7232003)). Qed.
Lemma lem7232005 : term110.
Proof. exact (EQ_MP (@lem7232004) (@lem0)). Qed.
Lemma lem7232006 : term483.
Proof. exact (@lem7231995 (@lem7232005)). Qed.
Lemma lem7232008 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232009 : term110 = term111.
Proof. exact (@lem7232008 (NUMERAL 0) term13). Qed.
Lemma lem7232010 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232011 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232012 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232011 h1) (fun h1 : term111 = True => @lem7232010)). Qed.
Lemma lem7232013 : term111 = True.
Proof. exact (EQ_MP (@lem7232012) (@lem7232010)). Qed.
Lemma lem7232014 : term110 = True.
Proof. exact (TRANS (@lem7232009) (@lem7232013)). Qed.
Lemma lem7232015 : True = term110.
Proof. exact (SYM (@lem7232014)). Qed.
Lemma lem7232016 : term110.
Proof. exact (EQ_MP (@lem7232015) (@lem0)). Qed.
Lemma lem7232017 : term481 = term484.
Proof. exact (@lem7232006 (@lem7232016)). Qed.
Lemma lem7232019 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232020 : term122 = term29.
Proof. exact (@lem7232019 term13). Qed.
Lemma lem7232022 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232023 : term122 = term29.
Proof. exact (@lem7232022 term13). Qed.
Lemma lem7232024 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7232025 : term485 = term479.
Proof. exact (MK_COMB (@lem7232024) (@lem7232023)). Qed.
Lemma lem7232026 : term484 = term478.
Proof. exact (MK_COMB (@lem7232025) (@lem7232020)). Qed.
Lemma lem7232028 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232029 : term478 = term486.
Proof. exact (@lem7232028 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7232030 : term486 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7232031 : term478 = False.
Proof. exact (TRANS (@lem7232029) (@lem7232030)). Qed.
Lemma lem7232032 : term484 = False.
Proof. exact (TRANS (@lem7232026) (@lem7232031)). Qed.
Lemma lem7232033 : term481 = False.
Proof. exact (TRANS (@lem7232017) (@lem7232032)). Qed.
Lemma lem7232034 : term478 = False.
Proof. exact (TRANS (@lem7231994) (@lem7232033)). Qed.
Lemma lem7232035 : term472 = False.
Proof. exact (TRANS (@lem7231985) (@lem7232034)). Qed.
Lemma lem7232036 (h1 : term472) : False.
Proof. exact (EQ_MP (@lem7232035) (@lem7231982 h1)). Qed.
Lemma lem7232037 (h1 : term472) : term472.
Proof. exact (h1). Qed.
Lemma lem7232039 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7232040 : term472 = term478.
Proof. exact (@lem7232039 term29 term29). Qed.
Lemma lem7232042 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7232043 : term29 = term59.
Proof. exact (@lem7232042 (NUMERAL 0)). Qed.
Lemma lem7232045 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7232046 : term29 = term59.
Proof. exact (@lem7232045 (NUMERAL 0)). Qed.
Lemma lem7232047 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7232048 : term479 = term480.
Proof. exact (MK_COMB (@lem7232047) (@lem7232046)). Qed.
Lemma lem7232049 : term478 = term481.
Proof. exact (MK_COMB (@lem7232048) (@lem7232043)). Qed.
Lemma lem7232050 : term482.
Proof. exact (@lem1980255 term29 term44 term29 term44). Qed.
Lemma lem7232052 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232053 : term110 = term111.
Proof. exact (@lem7232052 (NUMERAL 0) term13). Qed.
Lemma lem7232054 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232055 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232056 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232055 h1) (fun h1 : term111 = True => @lem7232054)). Qed.
Lemma lem7232057 : term111 = True.
Proof. exact (EQ_MP (@lem7232056) (@lem7232054)). Qed.
Lemma lem7232058 : term110 = True.
Proof. exact (TRANS (@lem7232053) (@lem7232057)). Qed.
Lemma lem7232059 : True = term110.
Proof. exact (SYM (@lem7232058)). Qed.
Lemma lem7232060 : term110.
Proof. exact (EQ_MP (@lem7232059) (@lem0)). Qed.
Lemma lem7232061 : term483.
Proof. exact (@lem7232050 (@lem7232060)). Qed.
Lemma lem7232063 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232064 : term110 = term111.
Proof. exact (@lem7232063 (NUMERAL 0) term13). Qed.
Lemma lem7232065 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232066 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232067 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232066 h1) (fun h1 : term111 = True => @lem7232065)). Qed.
Lemma lem7232068 : term111 = True.
Proof. exact (EQ_MP (@lem7232067) (@lem7232065)). Qed.
Lemma lem7232069 : term110 = True.
Proof. exact (TRANS (@lem7232064) (@lem7232068)). Qed.
Lemma lem7232070 : True = term110.
Proof. exact (SYM (@lem7232069)). Qed.
Lemma lem7232071 : term110.
Proof. exact (EQ_MP (@lem7232070) (@lem0)). Qed.
Lemma lem7232072 : term481 = term484.
Proof. exact (@lem7232061 (@lem7232071)). Qed.
Lemma lem7232074 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232075 : term122 = term29.
Proof. exact (@lem7232074 term13). Qed.
Lemma lem7232077 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232078 : term122 = term29.
Proof. exact (@lem7232077 term13). Qed.
Lemma lem7232079 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7232080 : term485 = term479.
Proof. exact (MK_COMB (@lem7232079) (@lem7232078)). Qed.
Lemma lem7232081 : term484 = term478.
Proof. exact (MK_COMB (@lem7232080) (@lem7232075)). Qed.
Lemma lem7232083 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232084 : term478 = term486.
Proof. exact (@lem7232083 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7232085 : term486 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7232086 : term478 = False.
Proof. exact (TRANS (@lem7232084) (@lem7232085)). Qed.
Lemma lem7232087 : term484 = False.
Proof. exact (TRANS (@lem7232081) (@lem7232086)). Qed.
Lemma lem7232088 : term481 = False.
Proof. exact (TRANS (@lem7232072) (@lem7232087)). Qed.
Lemma lem7232089 : term478 = False.
Proof. exact (TRANS (@lem7232049) (@lem7232088)). Qed.
Lemma lem7232090 : term472 = False.
Proof. exact (TRANS (@lem7232040) (@lem7232089)). Qed.
Lemma lem7232091 (h1 : term472) : False.
Proof. exact (EQ_MP (@lem7232090) (@lem7232037 h1)). Qed.
Lemma lem7232092 (h1 : term477) : False.
Proof. exact (or_elim (@lem7231981 h1) (fun h0 : term472 => @lem7232036 h0) (fun h0 : term472 => @lem7232091 h0)). Qed.
Lemma lem7232094 (h1 : term477) : term477.
Proof. exact (h1). Qed.
Lemma lem7232095 (h1 : term477) : term477 = False.
Proof. exact (prop_ext (fun h2 : term477 => @lem7232092 h1) (fun h2 : False => @lem7232094 h1)). Qed.
Lemma lem7232096 (h1 : term477) : False.
Proof. exact (EQ_MP (@lem7232095 h1) (@lem7232094 h1)). Qed.
Lemma lem7232097 (g : nat -> real) (f : nat -> real) (n : nat) (h1 : term847 g f n) : term847 g f n.
Proof. exact (h1). Qed.
Lemma lem7232098 (g : nat -> real) (f : nat -> real) (n : nat) (h1 : term847 g f n) : term477.
Proof. exact (EQ_MP (@lem7231971 g f n) (@lem7232097 g f n h1)). Qed.
Lemma lem7232099 (g : nat -> real) (f : nat -> real) (n : nat) (h1 : term847 g f n) : term477 = False.
Proof. exact (prop_ext (fun h2 : term477 => @lem7232096 h2) (fun h2 : False => @lem7232098 g f n h1)). Qed.
Lemma lem7232100 (g : nat -> real) (f : nat -> real) (n : nat) (h1 : term847 g f n) : False.
Proof. exact (EQ_MP (@lem7232099 g f n h1) (@lem7232098 g f n h1)). Qed.
Lemma lem7232101 (g : nat -> real) (f : nat -> real) (n : nat) : term924 g f n.
Proof. exact (fun h0 : term847 g f n => @lem7232100 g f n h0). Qed.
Lemma lem7232102 (g : nat -> real) (f : nat -> real) (n : nat) : term925 g f n.
Proof. exact (@lem1386578 ((term805 f g n) = (term819 g f n))). Qed.
Lemma lem7232105 (g : nat -> real) (f : nat -> real) (n : nat) : (term805 f g n) = (term819 g f n).
Proof. exact (@lem7232102 g f n (@lem7232101 g f n)). Qed.
Lemma lem7232116 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term926 m g f n) = (term927 m g f n).
Proof. exact (@lem1988318 (term839 m f g n) (term846 m g f n)). Qed.
Lemma lem7232122 (f : nat -> real) (n : nat) : (term802 f n) = (term849 f n).
Proof. exact (@lem1982792 (term797 f n) (term800 f n)). Qed.
Lemma lem7232127 (f : nat -> real) (n : nat) : (term849 f n) = (term850 f n).
Proof. exact (@lem1982761 (term851 f n) (term797 f n)). Qed.
Lemma lem7232129 (f : nat -> real) (n : nat) : (term802 f n) = (term850 f n).
Proof. exact (TRANS (@lem7232122 f n) (@lem7232127 f n)). Qed.
Lemma lem7232132 (g : nat -> real) (n : nat) : (term808 g n) = (term808 g n).
Proof. exact (eq_refl (term808 g n)). Qed.
Lemma lem7232133 (g : nat -> real) (f : nat -> real) (n : nat) : (term817 g f n) = (term852 g f n).
Proof. exact (MK_COMB (@lem7232132 g n) (@lem7232129 f n)). Qed.
Lemma lem7232134 (g : nat -> real) (f : nat -> real) (n : nat) : (term852 g f n) = (term853 g f n).
Proof. exact (@lem1982781 (term851 f n) (term797 g n) (term797 f n)). Qed.
Lemma lem7232135 (f : nat -> real) (g : nat -> real) (n : nat) : (term810 g f n) = (term810 f g n).
Proof. exact (@lem1982747 (term797 f n) (term797 g n)). Qed.
Lemma lem7232136 (g : nat -> real) (f : nat -> real) (n : nat) : (term854 g f n) = (term855 g f n).
Proof. exact (@lem1982751 term62 (term797 g n) (term800 f n)). Qed.
Lemma lem7232137 (f : nat -> real) (g : nat -> real) (n : nat) : (term856 g f n) = (term857 f g n).
Proof. exact (@lem1982747 (term800 f n) (term797 g n)). Qed.
Lemma lem7232138 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem7232139 (f : nat -> real) (g : nat -> real) (n : nat) : (term855 g f n) = (term858 f g n).
Proof. exact (MK_COMB (@lem7232138) (@lem7232137 f g n)). Qed.
Lemma lem7232140 (f : nat -> real) (g : nat -> real) (n : nat) : (term854 g f n) = (term858 f g n).
Proof. exact (TRANS (@lem7232136 g f n) (@lem7232139 f g n)). Qed.
Lemma lem7232141 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232142 (f : nat -> real) (g : nat -> real) (n : nat) : (term859 g f n) = (term860 f g n).
Proof. exact (MK_COMB (@lem7232141) (@lem7232140 f g n)). Qed.
Lemma lem7232143 (f : nat -> real) (g : nat -> real) (n : nat) : (term853 g f n) = (term861 f g n).
Proof. exact (MK_COMB (@lem7232142 f g n) (@lem7232135 f g n)). Qed.
Lemma lem7232144 (f : nat -> real) (g : nat -> real) (n : nat) : (term852 g f n) = (term861 f g n).
Proof. exact (TRANS (@lem7232134 g f n) (@lem7232143 f g n)). Qed.
Lemma lem7232145 (f : nat -> real) (g : nat -> real) (n : nat) : (term817 g f n) = (term861 f g n).
Proof. exact (TRANS (@lem7232133 g f n) (@lem7232144 f g n)). Qed.
Lemma lem7232148 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term844 m n g f) = (term844 m n g f).
Proof. exact (eq_refl (term844 m n g f)). Qed.
Lemma lem7232149 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term845 m g f n) = (term928 m f g n).
Proof. exact (MK_COMB (@lem7232148 m n g f) (@lem7232145 f g n)). Qed.
Lemma lem7232150 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term928 m f g n) = (term929 m f g n).
Proof. exact (@lem1982757 (term858 f g n) (term836 m n g f) (term810 f g n)). Qed.
Lemma lem7232151 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term930 m f g n) = (term931 m n g f).
Proof. exact (@lem1982761 (term810 f g n) (term836 m n g f)). Qed.
Lemma lem7232152 (f : nat -> real) (g : nat -> real) (n : nat) : (term860 f g n) = (term860 f g n).
Proof. exact (eq_refl (term860 f g n)). Qed.
Lemma lem7232153 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term929 m f g n) = (term932 m n g f).
Proof. exact (MK_COMB (@lem7232152 f g n) (@lem7232151 m n g f)). Qed.
Lemma lem7232154 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term928 m f g n) = (term932 m n g f).
Proof. exact (TRANS (@lem7232150 m f g n) (@lem7232153 m n g f)). Qed.
Lemma lem7232155 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term845 m g f n) = (term932 m n g f).
Proof. exact (TRANS (@lem7232149 m f g n) (@lem7232154 m n g f)). Qed.
Lemma lem7232173 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term842 n f g m) = (term933 n f g m).
Proof. exact (@lem1982792 (term810 f g n) (term374 f g m)). Qed.
Lemma lem7232178 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term933 n f g m) = (term934 m f g n).
Proof. exact (@lem1982761 (term592 f g m) (term810 f g n)). Qed.
Lemma lem7232180 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term842 n f g m) = (term934 m f g n).
Proof. exact (TRANS (@lem7232173 n f g m) (@lem7232178 m f g n)). Qed.
Lemma lem7232181 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7232182 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term843 n f g m) = (term935 m f g n).
Proof. exact (MK_COMB (@lem7232181) (@lem7232180 m f g n)). Qed.
Lemma lem7232183 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term846 m g f n) = (term936 m n g f).
Proof. exact (MK_COMB (@lem7232182 m f g n) (@lem7232155 m n g f)). Qed.
Lemma lem7232184 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term936 m n g f) = (term937 m n g f).
Proof. exact (@lem1982792 (term934 m f g n) (term932 m n g f)). Qed.
Lemma lem7232185 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term938 m n g f) = (term939 m n g f).
Proof. exact (@lem1982781 (term858 f g n) term62 (term931 m n g f)). Qed.
Lemma lem7232192 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term940 m n g f) = (term941 m n g f).
Proof. exact (@lem1982781 (term810 f g n) term62 (term836 m n g f)). Qed.
Lemma lem7232193 (f : nat -> real) (g : nat -> real) (n : nat) : (term872 f g n) = (term873 f g n).
Proof. exact (@lem1982749 term62 term62 (term857 f g n)). Qed.
Lemma lem7232195 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232196 : term62 = term63.
Proof. exact (@lem7232195 term13). Qed.
Lemma lem7232198 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232199 : term62 = term63.
Proof. exact (@lem7232198 term13). Qed.
Lemma lem7232200 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232201 : term64 = term65.
Proof. exact (MK_COMB (@lem7232200) (@lem7232199)). Qed.
Lemma lem7232202 : term415 = term416.
Proof. exact (MK_COMB (@lem7232201) (@lem7232196)). Qed.
Lemma lem7232203 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7232205 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232206 : term71 = term72.
Proof. exact (@lem7232205 term13 term13). Qed.
Lemma lem7232207 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232208 : term74 = term13.
Proof. exact (EQ_MP (@lem7232207) (@lem940073)). Qed.
Lemma lem7232209 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232210 : term72 = term44.
Proof. exact (MK_COMB (@lem7232209) (@lem7232208)). Qed.
Lemma lem7232211 : term71 = term44.
Proof. exact (TRANS (@lem7232206) (@lem7232210)). Qed.
Lemma lem7232213 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7232214 : term415 = term72.
Proof. exact (@lem7232213 term13 term13). Qed.
Lemma lem7232215 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232216 : term74 = term13.
Proof. exact (EQ_MP (@lem7232215) (@lem940073)). Qed.
Lemma lem7232217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232218 : term72 = term44.
Proof. exact (MK_COMB (@lem7232217) (@lem7232216)). Qed.
Lemma lem7232219 : term415 = term44.
Proof. exact (TRANS (@lem7232214) (@lem7232218)). Qed.
Lemma lem7232220 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7232221 : term419 = term420.
Proof. exact (MK_COMB (@lem7232220) (@lem7232219)). Qed.
Lemma lem7232222 : term417 = term88.
Proof. exact (MK_COMB (@lem7232221) (@lem7232211)). Qed.
Lemma lem7232223 : term416 = term88.
Proof. exact (TRANS (@lem7232203) (@lem7232222)). Qed.
Lemma lem7232224 : term415 = term88.
Proof. exact (TRANS (@lem7232202) (@lem7232223)). Qed.
Lemma lem7232226 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7232227 : term88 = term44.
Proof. exact (@lem7232226 term44). Qed.
Lemma lem7232228 : term415 = term44.
Proof. exact (TRANS (@lem7232224) (@lem7232227)). Qed.
Lemma lem7232229 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232230 : term421 = term422.
Proof. exact (MK_COMB (@lem7232229) (@lem7232228)). Qed.
Lemma lem7232231 (f : nat -> real) (g : nat -> real) (n : nat) : (term857 f g n) = (term857 f g n).
Proof. exact (eq_refl (term857 f g n)). Qed.
Lemma lem7232232 (f : nat -> real) (g : nat -> real) (n : nat) : (term873 f g n) = (term874 f g n).
Proof. exact (MK_COMB (@lem7232230) (@lem7232231 f g n)). Qed.
Lemma lem7232233 (f : nat -> real) (g : nat -> real) (n : nat) : (term872 f g n) = (term874 f g n).
Proof. exact (TRANS (@lem7232193 f g n) (@lem7232232 f g n)). Qed.
Lemma lem7232234 (f : nat -> real) (g : nat -> real) (n : nat) : (term874 f g n) = (term857 f g n).
Proof. exact (@lem1982709 (term857 f g n)). Qed.
Lemma lem7232235 (f : nat -> real) (g : nat -> real) (n : nat) : (term872 f g n) = (term857 f g n).
Proof. exact (TRANS (@lem7232233 f g n) (@lem7232234 f g n)). Qed.
Lemma lem7232236 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232237 (f : nat -> real) (g : nat -> real) (n : nat) : (term875 f g n) = (term876 f g n).
Proof. exact (MK_COMB (@lem7232236) (@lem7232235 f g n)). Qed.
Lemma lem7232238 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term939 m n g f) = (term942 m n g f).
Proof. exact (MK_COMB (@lem7232237 f g n) (@lem7232192 m n g f)). Qed.
Lemma lem7232239 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term938 m n g f) = (term942 m n g f).
Proof. exact (TRANS (@lem7232185 m n g f) (@lem7232238 m n g f)). Qed.
Lemma lem7232240 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term943 m f g n) = (term943 m f g n).
Proof. exact (eq_refl (term943 m f g n)). Qed.
Lemma lem7232241 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term937 m n g f) = (term944 m n g f).
Proof. exact (MK_COMB (@lem7232240 m f g n) (@lem7232239 m n g f)). Qed.
Lemma lem7232242 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term944 m n g f) = (term945 m n g f).
Proof. exact (@lem1982755 (term592 f g m) (term810 f g n) (term942 m n g f)). Qed.
Lemma lem7232243 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term946 m n g f) = (term947 m n g f).
Proof. exact (@lem1982757 (term857 f g n) (term810 f g n) (term941 m n g f)). Qed.
Lemma lem7232244 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term948 m n g f) = (term949 m n g f).
Proof. exact (@lem1982763 (term810 f g n) (term871 f g n) (term950 m n g f)). Qed.
Lemma lem7232245 (f : nat -> real) (g : nat -> real) (n : nat) : (term883 f g n) = (term884 f g n).
Proof. exact (@lem1982715 term62 (term810 f g n)). Qed.
Lemma lem7232247 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7232248 : term44 = term88.
Proof. exact (@lem7232247 term13). Qed.
Lemma lem7232250 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232251 : term62 = term63.
Proof. exact (@lem7232250 term13). Qed.
Lemma lem7232252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232253 : term104 = term105.
Proof. exact (MK_COMB (@lem7232252) (@lem7232251)). Qed.
Lemma lem7232254 : term106 = term107.
Proof. exact (MK_COMB (@lem7232253) (@lem7232248)). Qed.
Lemma lem7232255 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7232257 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232258 : term110 = term111.
Proof. exact (@lem7232257 (NUMERAL 0) term13). Qed.
Lemma lem7232259 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232260 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232261 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232260 h1) (fun h1 : term111 = True => @lem7232259)). Qed.
Lemma lem7232262 : term111 = True.
Proof. exact (EQ_MP (@lem7232261) (@lem7232259)). Qed.
Lemma lem7232263 : term110 = True.
Proof. exact (TRANS (@lem7232258) (@lem7232262)). Qed.
Lemma lem7232264 : True = term110.
Proof. exact (SYM (@lem7232263)). Qed.
Lemma lem7232265 : term110.
Proof. exact (EQ_MP (@lem7232264) (@lem0)). Qed.
Lemma lem7232266 : term113.
Proof. exact (@lem7232255 (@lem7232265)). Qed.
Lemma lem7232268 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232269 : term110 = term111.
Proof. exact (@lem7232268 (NUMERAL 0) term13). Qed.
Lemma lem7232270 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232271 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232272 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232271 h1) (fun h1 : term111 = True => @lem7232270)). Qed.
Lemma lem7232273 : term111 = True.
Proof. exact (EQ_MP (@lem7232272) (@lem7232270)). Qed.
Lemma lem7232274 : term110 = True.
Proof. exact (TRANS (@lem7232269) (@lem7232273)). Qed.
Lemma lem7232275 : True = term110.
Proof. exact (SYM (@lem7232274)). Qed.
Lemma lem7232276 : term110.
Proof. exact (EQ_MP (@lem7232275) (@lem0)). Qed.
Lemma lem7232277 : term114.
Proof. exact (@lem7232266 (@lem7232276)). Qed.
Lemma lem7232279 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232280 : term110 = term111.
Proof. exact (@lem7232279 (NUMERAL 0) term13). Qed.
Lemma lem7232281 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232282 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232283 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232282 h1) (fun h1 : term111 = True => @lem7232281)). Qed.
Lemma lem7232284 : term111 = True.
Proof. exact (EQ_MP (@lem7232283) (@lem7232281)). Qed.
Lemma lem7232285 : term110 = True.
Proof. exact (TRANS (@lem7232280) (@lem7232284)). Qed.
Lemma lem7232286 : True = term110.
Proof. exact (SYM (@lem7232285)). Qed.
Lemma lem7232287 : term110.
Proof. exact (EQ_MP (@lem7232286) (@lem0)). Qed.
Lemma lem7232288 : term115.
Proof. exact (@lem7232277 (@lem7232287)). Qed.
Lemma lem7232290 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232291 : term71 = term72.
Proof. exact (@lem7232290 term13 term13). Qed.
Lemma lem7232292 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232293 : term74 = term13.
Proof. exact (EQ_MP (@lem7232292) (@lem940073)). Qed.
Lemma lem7232294 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232295 : term72 = term44.
Proof. exact (MK_COMB (@lem7232294) (@lem7232293)). Qed.
Lemma lem7232296 : term71 = term44.
Proof. exact (TRANS (@lem7232291) (@lem7232295)). Qed.
Lemma lem7232298 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7232299 : term89 = term94.
Proof. exact (@lem7232298 term13 term13). Qed.
Lemma lem7232300 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232301 : term74 = term13.
Proof. exact (EQ_MP (@lem7232300) (@lem940073)). Qed.
Lemma lem7232302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232303 : term72 = term44.
Proof. exact (MK_COMB (@lem7232302) (@lem7232301)). Qed.
Lemma lem7232304 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7232305 : term94 = term62.
Proof. exact (MK_COMB (@lem7232304) (@lem7232303)). Qed.
Lemma lem7232306 : term89 = term62.
Proof. exact (TRANS (@lem7232299) (@lem7232305)). Qed.
Lemma lem7232307 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232308 : term116 = term104.
Proof. exact (MK_COMB (@lem7232307) (@lem7232306)). Qed.
Lemma lem7232309 : term117 = term106.
Proof. exact (MK_COMB (@lem7232308) (@lem7232296)). Qed.
Lemma lem7232311 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7232312 : term106 = term29.
Proof. exact (@lem7232311 term13). Qed.
Lemma lem7232313 : term117 = term29.
Proof. exact (TRANS (@lem7232309) (@lem7232312)). Qed.
Lemma lem7232314 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232315 : term119 = term120.
Proof. exact (MK_COMB (@lem7232314) (@lem7232313)). Qed.
Lemma lem7232316 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7232317 : term121 = term122.
Proof. exact (MK_COMB (@lem7232315) (@lem7232316)). Qed.
Lemma lem7232319 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232320 : term122 = term29.
Proof. exact (@lem7232319 term13). Qed.
Lemma lem7232321 : term121 = term29.
Proof. exact (TRANS (@lem7232317) (@lem7232320)). Qed.
Lemma lem7232323 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232324 : term71 = term72.
Proof. exact (@lem7232323 term13 term13). Qed.
Lemma lem7232325 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232326 : term74 = term13.
Proof. exact (EQ_MP (@lem7232325) (@lem940073)). Qed.
Lemma lem7232327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232328 : term72 = term44.
Proof. exact (MK_COMB (@lem7232327) (@lem7232326)). Qed.
Lemma lem7232329 : term71 = term44.
Proof. exact (TRANS (@lem7232324) (@lem7232328)). Qed.
Lemma lem7232330 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7232331 : term124 = term122.
Proof. exact (MK_COMB (@lem7232330) (@lem7232329)). Qed.
Lemma lem7232333 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232334 : term122 = term29.
Proof. exact (@lem7232333 term13). Qed.
Lemma lem7232335 : term124 = term29.
Proof. exact (TRANS (@lem7232331) (@lem7232334)). Qed.
Lemma lem7232336 : term29 = term124.
Proof. exact (SYM (@lem7232335)). Qed.
Lemma lem7232337 : term121 = term124.
Proof. exact (TRANS (@lem7232321) (@lem7232336)). Qed.
Lemma lem7232338 : term107 = term59.
Proof. exact (@lem7232288 (@lem7232337)). Qed.
Lemma lem7232339 : term106 = term59.
Proof. exact (TRANS (@lem7232254) (@lem7232338)). Qed.
Lemma lem7232341 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7232342 : term59 = term29.
Proof. exact (@lem7232341 term29). Qed.
Lemma lem7232343 : term106 = term29.
Proof. exact (TRANS (@lem7232339) (@lem7232342)). Qed.
Lemma lem7232344 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232345 : term125 = term120.
Proof. exact (MK_COMB (@lem7232344) (@lem7232343)). Qed.
Lemma lem7232346 (f : nat -> real) (g : nat -> real) (n : nat) : (term810 f g n) = (term810 f g n).
Proof. exact (eq_refl (term810 f g n)). Qed.
Lemma lem7232347 (f : nat -> real) (g : nat -> real) (n : nat) : (term884 f g n) = (term885 f g n).
Proof. exact (MK_COMB (@lem7232345) (@lem7232346 f g n)). Qed.
Lemma lem7232348 (f : nat -> real) (g : nat -> real) (n : nat) : (term883 f g n) = (term885 f g n).
Proof. exact (TRANS (@lem7232245 f g n) (@lem7232347 f g n)). Qed.
Lemma lem7232349 (f : nat -> real) (g : nat -> real) (n : nat) : (term885 f g n) = term29.
Proof. exact (@lem1982719 (term810 f g n)). Qed.
Lemma lem7232350 (f : nat -> real) (g : nat -> real) (n : nat) : (term883 f g n) = term29.
Proof. exact (TRANS (@lem7232348 f g n) (@lem7232349 f g n)). Qed.
Lemma lem7232351 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232352 (f : nat -> real) (g : nat -> real) (n : nat) : (term951 f g n) = term128.
Proof. exact (MK_COMB (@lem7232351) (@lem7232350 f g n)). Qed.
Lemma lem7232353 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term950 m n g f) = (term950 m n g f).
Proof. exact (eq_refl (term950 m n g f)). Qed.
Lemma lem7232354 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term949 m n g f) = (term952 m n g f).
Proof. exact (MK_COMB (@lem7232352 f g n) (@lem7232353 m n g f)). Qed.
Lemma lem7232355 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term948 m n g f) = (term952 m n g f).
Proof. exact (TRANS (@lem7232244 m n g f) (@lem7232354 m n g f)). Qed.
Lemma lem7232356 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term952 m n g f) = (term950 m n g f).
Proof. exact (@lem1982721 (term950 m n g f)). Qed.
Lemma lem7232357 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term948 m n g f) = (term950 m n g f).
Proof. exact (TRANS (@lem7232355 m n g f) (@lem7232356 m n g f)). Qed.
Lemma lem7232358 (f : nat -> real) (g : nat -> real) (n : nat) : (term876 f g n) = (term876 f g n).
Proof. exact (eq_refl (term876 f g n)). Qed.
Lemma lem7232359 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term947 m n g f) = (term953 m n g f).
Proof. exact (MK_COMB (@lem7232358 f g n) (@lem7232357 m n g f)). Qed.
Lemma lem7232360 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term946 m n g f) = (term953 m n g f).
Proof. exact (TRANS (@lem7232243 m n g f) (@lem7232359 m n g f)). Qed.
Lemma lem7232361 (f : nat -> real) (g : nat -> real) (m : nat) : (term619 f g m) = (term619 f g m).
Proof. exact (eq_refl (term619 f g m)). Qed.
Lemma lem7232362 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term945 m n g f) = (term954 m n g f).
Proof. exact (MK_COMB (@lem7232361 f g m) (@lem7232360 m n g f)). Qed.
Lemma lem7232363 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term944 m n g f) = (term954 m n g f).
Proof. exact (TRANS (@lem7232242 m n g f) (@lem7232362 m n g f)). Qed.
Lemma lem7232364 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term937 m n g f) = (term954 m n g f).
Proof. exact (TRANS (@lem7232241 m n g f) (@lem7232363 m n g f)). Qed.
Lemma lem7232365 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term936 m n g f) = (term954 m n g f).
Proof. exact (TRANS (@lem7232184 m n g f) (@lem7232364 m n g f)). Qed.
Lemma lem7232366 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term846 m g f n) = (term954 m n g f).
Proof. exact (TRANS (@lem7232183 m n g f) (@lem7232365 m n g f)). Qed.
Lemma lem7232372 (g : nat -> real) (n : nat) : (term802 g n) = (term849 g n).
Proof. exact (@lem1982792 (term797 g n) (term800 g n)). Qed.
Lemma lem7232377 (g : nat -> real) (n : nat) : (term849 g n) = (term850 g n).
Proof. exact (@lem1982761 (term851 g n) (term797 g n)). Qed.
Lemma lem7232379 (g : nat -> real) (n : nat) : (term802 g n) = (term850 g n).
Proof. exact (TRANS (@lem7232372 g n) (@lem7232377 g n)). Qed.
Lemma lem7232382 (f : nat -> real) (n : nat) : (term803 f n) = (term803 f n).
Proof. exact (eq_refl (term803 f n)). Qed.
Lemma lem7232383 (f : nat -> real) (g : nat -> real) (n : nat) : (term804 f g n) = (term889 f g n).
Proof. exact (MK_COMB (@lem7232382 f n) (@lem7232379 g n)). Qed.
Lemma lem7232384 (f : nat -> real) (g : nat -> real) (n : nat) : (term889 f g n) = (term890 f g n).
Proof. exact (@lem1982781 (term851 g n) (term800 f n) (term797 g n)). Qed.
Lemma lem7232385 (f : nat -> real) (g : nat -> real) (n : nat) : (term857 f g n) = (term857 f g n).
Proof. exact (eq_refl (term857 f g n)). Qed.
Lemma lem7232390 (f : nat -> real) (g : nat -> real) (n : nat) : (term891 f g n) = (term865 f g n).
Proof. exact (@lem1982751 term62 (term800 f n) (term800 g n)). Qed.
Lemma lem7232391 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232392 (f : nat -> real) (g : nat -> real) (n : nat) : (term892 f g n) = (term887 f g n).
Proof. exact (MK_COMB (@lem7232391) (@lem7232390 f g n)). Qed.
Lemma lem7232393 (f : nat -> real) (g : nat -> real) (n : nat) : (term890 f g n) = (term888 f g n).
Proof. exact (MK_COMB (@lem7232392 f g n) (@lem7232385 f g n)). Qed.
Lemma lem7232394 (f : nat -> real) (g : nat -> real) (n : nat) : (term889 f g n) = (term888 f g n).
Proof. exact (TRANS (@lem7232384 f g n) (@lem7232393 f g n)). Qed.
Lemma lem7232395 (f : nat -> real) (g : nat -> real) (n : nat) : (term804 f g n) = (term888 f g n).
Proof. exact (TRANS (@lem7232383 f g n) (@lem7232394 f g n)). Qed.
Lemma lem7232396 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term836 m n g f) = (term836 m n g f).
Proof. exact (eq_refl (term836 m n g f)). Qed.
Lemma lem7232414 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term826 n f g m) = (term955 n f g m).
Proof. exact (@lem1982792 (term813 f g n) (term374 f g m)). Qed.
Lemma lem7232419 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term955 n f g m) = (term956 m f g n).
Proof. exact (@lem1982761 (term592 f g m) (term813 f g n)). Qed.
Lemma lem7232421 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term826 n f g m) = (term956 m f g n).
Proof. exact (TRANS (@lem7232414 n f g m) (@lem7232419 m f g n)). Qed.
Lemma lem7232422 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7232423 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term828 n f g m) = (term957 m f g n).
Proof. exact (MK_COMB (@lem7232422) (@lem7232421 m f g n)). Qed.
Lemma lem7232424 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term837 m n g f) = (term958 m n g f).
Proof. exact (MK_COMB (@lem7232423 m f g n) (@lem7232396 m n g f)). Qed.
Lemma lem7232425 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term958 m n g f) = (term959 m n g f).
Proof. exact (@lem1982792 (term956 m f g n) (term836 m n g f)). Qed.
Lemma lem7232434 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term959 m n g f) = (term960 m n g f).
Proof. exact (@lem1982755 (term592 f g m) (term813 f g n) (term950 m n g f)). Qed.
Lemma lem7232435 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term958 m n g f) = (term960 m n g f).
Proof. exact (TRANS (@lem7232425 m n g f) (@lem7232434 m n g f)). Qed.
Lemma lem7232436 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term837 m n g f) = (term960 m n g f).
Proof. exact (TRANS (@lem7232424 m n g f) (@lem7232435 m n g f)). Qed.
Lemma lem7232437 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232438 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term838 m n g f) = (term961 m n g f).
Proof. exact (MK_COMB (@lem7232437) (@lem7232436 m n g f)). Qed.
Lemma lem7232439 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term839 m f g n) = (term962 m f g n).
Proof. exact (MK_COMB (@lem7232438 m n g f) (@lem7232395 f g n)). Qed.
Lemma lem7232440 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term962 m f g n) = (term963 m f g n).
Proof. exact (@lem1982755 (term592 f g m) (term964 m n g f) (term888 f g n)). Qed.
Lemma lem7232441 (m : nat) (f : nat -> real) (g : nat -> real) (n : nat) : (term965 m f g n) = (term966 m f g n).
Proof. exact (@lem1982753 (term813 f g n) (term865 f g n) (term950 m n g f) (term857 f g n)). Qed.
Lemma lem7232442 (f : nat -> real) (g : nat -> real) (n : nat) : (term967 f g n) = (term911 f g n).
Proof. exact (@lem1982715 term62 (term813 f g n)). Qed.
Lemma lem7232444 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7232445 : term44 = term88.
Proof. exact (@lem7232444 term13). Qed.
Lemma lem7232447 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232448 : term62 = term63.
Proof. exact (@lem7232447 term13). Qed.
Lemma lem7232449 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232450 : term104 = term105.
Proof. exact (MK_COMB (@lem7232449) (@lem7232448)). Qed.
Lemma lem7232451 : term106 = term107.
Proof. exact (MK_COMB (@lem7232450) (@lem7232445)). Qed.
Lemma lem7232452 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7232454 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232455 : term110 = term111.
Proof. exact (@lem7232454 (NUMERAL 0) term13). Qed.
Lemma lem7232456 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232457 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232458 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232457 h1) (fun h1 : term111 = True => @lem7232456)). Qed.
Lemma lem7232459 : term111 = True.
Proof. exact (EQ_MP (@lem7232458) (@lem7232456)). Qed.
Lemma lem7232460 : term110 = True.
Proof. exact (TRANS (@lem7232455) (@lem7232459)). Qed.
Lemma lem7232461 : True = term110.
Proof. exact (SYM (@lem7232460)). Qed.
Lemma lem7232462 : term110.
Proof. exact (EQ_MP (@lem7232461) (@lem0)). Qed.
Lemma lem7232463 : term113.
Proof. exact (@lem7232452 (@lem7232462)). Qed.
Lemma lem7232465 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232466 : term110 = term111.
Proof. exact (@lem7232465 (NUMERAL 0) term13). Qed.
Lemma lem7232467 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232468 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232469 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232468 h1) (fun h1 : term111 = True => @lem7232467)). Qed.
Lemma lem7232470 : term111 = True.
Proof. exact (EQ_MP (@lem7232469) (@lem7232467)). Qed.
Lemma lem7232471 : term110 = True.
Proof. exact (TRANS (@lem7232466) (@lem7232470)). Qed.
Lemma lem7232472 : True = term110.
Proof. exact (SYM (@lem7232471)). Qed.
Lemma lem7232473 : term110.
Proof. exact (EQ_MP (@lem7232472) (@lem0)). Qed.
Lemma lem7232474 : term114.
Proof. exact (@lem7232463 (@lem7232473)). Qed.
Lemma lem7232476 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232477 : term110 = term111.
Proof. exact (@lem7232476 (NUMERAL 0) term13). Qed.
Lemma lem7232478 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232479 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232480 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232479 h1) (fun h1 : term111 = True => @lem7232478)). Qed.
Lemma lem7232481 : term111 = True.
Proof. exact (EQ_MP (@lem7232480) (@lem7232478)). Qed.
Lemma lem7232482 : term110 = True.
Proof. exact (TRANS (@lem7232477) (@lem7232481)). Qed.
Lemma lem7232483 : True = term110.
Proof. exact (SYM (@lem7232482)). Qed.
Lemma lem7232484 : term110.
Proof. exact (EQ_MP (@lem7232483) (@lem0)). Qed.
Lemma lem7232485 : term115.
Proof. exact (@lem7232474 (@lem7232484)). Qed.
Lemma lem7232487 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232488 : term71 = term72.
Proof. exact (@lem7232487 term13 term13). Qed.
Lemma lem7232489 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232490 : term74 = term13.
Proof. exact (EQ_MP (@lem7232489) (@lem940073)). Qed.
Lemma lem7232491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232492 : term72 = term44.
Proof. exact (MK_COMB (@lem7232491) (@lem7232490)). Qed.
Lemma lem7232493 : term71 = term44.
Proof. exact (TRANS (@lem7232488) (@lem7232492)). Qed.
Lemma lem7232495 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7232496 : term89 = term94.
Proof. exact (@lem7232495 term13 term13). Qed.
Lemma lem7232497 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232498 : term74 = term13.
Proof. exact (EQ_MP (@lem7232497) (@lem940073)). Qed.
Lemma lem7232499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232500 : term72 = term44.
Proof. exact (MK_COMB (@lem7232499) (@lem7232498)). Qed.
Lemma lem7232501 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7232502 : term94 = term62.
Proof. exact (MK_COMB (@lem7232501) (@lem7232500)). Qed.
Lemma lem7232503 : term89 = term62.
Proof. exact (TRANS (@lem7232496) (@lem7232502)). Qed.
Lemma lem7232504 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232505 : term116 = term104.
Proof. exact (MK_COMB (@lem7232504) (@lem7232503)). Qed.
Lemma lem7232506 : term117 = term106.
Proof. exact (MK_COMB (@lem7232505) (@lem7232493)). Qed.
Lemma lem7232508 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7232509 : term106 = term29.
Proof. exact (@lem7232508 term13). Qed.
Lemma lem7232510 : term117 = term29.
Proof. exact (TRANS (@lem7232506) (@lem7232509)). Qed.
Lemma lem7232511 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232512 : term119 = term120.
Proof. exact (MK_COMB (@lem7232511) (@lem7232510)). Qed.
Lemma lem7232513 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7232514 : term121 = term122.
Proof. exact (MK_COMB (@lem7232512) (@lem7232513)). Qed.
Lemma lem7232516 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232517 : term122 = term29.
Proof. exact (@lem7232516 term13). Qed.
Lemma lem7232518 : term121 = term29.
Proof. exact (TRANS (@lem7232514) (@lem7232517)). Qed.
Lemma lem7232520 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232521 : term71 = term72.
Proof. exact (@lem7232520 term13 term13). Qed.
Lemma lem7232522 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232523 : term74 = term13.
Proof. exact (EQ_MP (@lem7232522) (@lem940073)). Qed.
Lemma lem7232524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232525 : term72 = term44.
Proof. exact (MK_COMB (@lem7232524) (@lem7232523)). Qed.
Lemma lem7232526 : term71 = term44.
Proof. exact (TRANS (@lem7232521) (@lem7232525)). Qed.
Lemma lem7232527 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7232528 : term124 = term122.
Proof. exact (MK_COMB (@lem7232527) (@lem7232526)). Qed.
Lemma lem7232530 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232531 : term122 = term29.
Proof. exact (@lem7232530 term13). Qed.
Lemma lem7232532 : term124 = term29.
Proof. exact (TRANS (@lem7232528) (@lem7232531)). Qed.
Lemma lem7232533 : term29 = term124.
Proof. exact (SYM (@lem7232532)). Qed.
Lemma lem7232534 : term121 = term124.
Proof. exact (TRANS (@lem7232518) (@lem7232533)). Qed.
Lemma lem7232535 : term107 = term59.
Proof. exact (@lem7232485 (@lem7232534)). Qed.
Lemma lem7232536 : term106 = term59.
Proof. exact (TRANS (@lem7232451) (@lem7232535)). Qed.
Lemma lem7232538 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7232539 : term59 = term29.
Proof. exact (@lem7232538 term29). Qed.
Lemma lem7232540 : term106 = term29.
Proof. exact (TRANS (@lem7232536) (@lem7232539)). Qed.
Lemma lem7232541 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232542 : term125 = term120.
Proof. exact (MK_COMB (@lem7232541) (@lem7232540)). Qed.
Lemma lem7232543 (f : nat -> real) (g : nat -> real) (n : nat) : (term813 f g n) = (term813 f g n).
Proof. exact (eq_refl (term813 f g n)). Qed.
Lemma lem7232544 (f : nat -> real) (g : nat -> real) (n : nat) : (term911 f g n) = (term912 f g n).
Proof. exact (MK_COMB (@lem7232542) (@lem7232543 f g n)). Qed.
Lemma lem7232545 (f : nat -> real) (g : nat -> real) (n : nat) : (term967 f g n) = (term912 f g n).
Proof. exact (TRANS (@lem7232442 f g n) (@lem7232544 f g n)). Qed.
Lemma lem7232546 (f : nat -> real) (g : nat -> real) (n : nat) : (term912 f g n) = term29.
Proof. exact (@lem1982719 (term813 f g n)). Qed.
Lemma lem7232547 (f : nat -> real) (g : nat -> real) (n : nat) : (term967 f g n) = term29.
Proof. exact (TRANS (@lem7232545 f g n) (@lem7232546 f g n)). Qed.
Lemma lem7232548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232549 (f : nat -> real) (g : nat -> real) (n : nat) : (term968 f g n) = term128.
Proof. exact (MK_COMB (@lem7232548) (@lem7232547 f g n)). Qed.
Lemma lem7232550 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term969 m f g n) = (term953 m n g f).
Proof. exact (@lem1982761 (term857 f g n) (term950 m n g f)). Qed.
Lemma lem7232551 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term966 m f g n) = (term970 m n g f).
Proof. exact (MK_COMB (@lem7232549 f g n) (@lem7232550 m n g f)). Qed.
Lemma lem7232552 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term965 m f g n) = (term970 m n g f).
Proof. exact (TRANS (@lem7232441 m f g n) (@lem7232551 m n g f)). Qed.
Lemma lem7232553 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term970 m n g f) = (term953 m n g f).
Proof. exact (@lem1982721 (term953 m n g f)). Qed.
Lemma lem7232554 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term965 m f g n) = (term953 m n g f).
Proof. exact (TRANS (@lem7232552 m n g f) (@lem7232553 m n g f)). Qed.
Lemma lem7232555 (f : nat -> real) (g : nat -> real) (m : nat) : (term619 f g m) = (term619 f g m).
Proof. exact (eq_refl (term619 f g m)). Qed.
Lemma lem7232556 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term963 m f g n) = (term954 m n g f).
Proof. exact (MK_COMB (@lem7232555 f g m) (@lem7232554 m n g f)). Qed.
Lemma lem7232557 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term962 m f g n) = (term954 m n g f).
Proof. exact (TRANS (@lem7232440 m f g n) (@lem7232556 m n g f)). Qed.
Lemma lem7232558 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term839 m f g n) = (term954 m n g f).
Proof. exact (TRANS (@lem7232439 m f g n) (@lem7232557 m n g f)). Qed.
Lemma lem7232559 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7232560 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term971 m f g n) = (term972 m n g f).
Proof. exact (MK_COMB (@lem7232559) (@lem7232558 m n g f)). Qed.
Lemma lem7232561 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term973 m g f n) = (term974 m n g f).
Proof. exact (MK_COMB (@lem7232560 m n g f) (@lem7232366 m n g f)). Qed.
Lemma lem7232562 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term974 m n g f) = (term975 m n g f).
Proof. exact (@lem1982792 (term954 m n g f) (term954 m n g f)). Qed.
Lemma lem7232563 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term976 m n g f) = (term977 m n g f).
Proof. exact (@lem1982781 (term592 f g m) term62 (term953 m n g f)). Qed.
Lemma lem7232564 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term978 m n g f) = (term979 m n g f).
Proof. exact (@lem1982781 (term857 f g n) term62 (term950 m n g f)). Qed.
Lemma lem7232565 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term980 m n g f) = (term981 m n g f).
Proof. exact (@lem1982749 term62 term62 (term836 m n g f)). Qed.
Lemma lem7232567 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232568 : term62 = term63.
Proof. exact (@lem7232567 term13). Qed.
Lemma lem7232570 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232571 : term62 = term63.
Proof. exact (@lem7232570 term13). Qed.
Lemma lem7232572 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232573 : term64 = term65.
Proof. exact (MK_COMB (@lem7232572) (@lem7232571)). Qed.
Lemma lem7232574 : term415 = term416.
Proof. exact (MK_COMB (@lem7232573) (@lem7232568)). Qed.
Lemma lem7232575 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7232577 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232578 : term71 = term72.
Proof. exact (@lem7232577 term13 term13). Qed.
Lemma lem7232579 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232580 : term74 = term13.
Proof. exact (EQ_MP (@lem7232579) (@lem940073)). Qed.
Lemma lem7232581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232582 : term72 = term44.
Proof. exact (MK_COMB (@lem7232581) (@lem7232580)). Qed.
Lemma lem7232583 : term71 = term44.
Proof. exact (TRANS (@lem7232578) (@lem7232582)). Qed.
Lemma lem7232585 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7232586 : term415 = term72.
Proof. exact (@lem7232585 term13 term13). Qed.
Lemma lem7232587 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232588 : term74 = term13.
Proof. exact (EQ_MP (@lem7232587) (@lem940073)). Qed.
Lemma lem7232589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232590 : term72 = term44.
Proof. exact (MK_COMB (@lem7232589) (@lem7232588)). Qed.
Lemma lem7232591 : term415 = term44.
Proof. exact (TRANS (@lem7232586) (@lem7232590)). Qed.
Lemma lem7232592 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7232593 : term419 = term420.
Proof. exact (MK_COMB (@lem7232592) (@lem7232591)). Qed.
Lemma lem7232594 : term417 = term88.
Proof. exact (MK_COMB (@lem7232593) (@lem7232583)). Qed.
Lemma lem7232595 : term416 = term88.
Proof. exact (TRANS (@lem7232575) (@lem7232594)). Qed.
Lemma lem7232596 : term415 = term88.
Proof. exact (TRANS (@lem7232574) (@lem7232595)). Qed.
Lemma lem7232598 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7232599 : term88 = term44.
Proof. exact (@lem7232598 term44). Qed.
Lemma lem7232600 : term415 = term44.
Proof. exact (TRANS (@lem7232596) (@lem7232599)). Qed.
Lemma lem7232601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232602 : term421 = term422.
Proof. exact (MK_COMB (@lem7232601) (@lem7232600)). Qed.
Lemma lem7232603 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term836 m n g f) = (term836 m n g f).
Proof. exact (eq_refl (term836 m n g f)). Qed.
Lemma lem7232604 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term981 m n g f) = (term982 m n g f).
Proof. exact (MK_COMB (@lem7232602) (@lem7232603 m n g f)). Qed.
Lemma lem7232605 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term980 m n g f) = (term982 m n g f).
Proof. exact (TRANS (@lem7232565 m n g f) (@lem7232604 m n g f)). Qed.
Lemma lem7232606 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term982 m n g f) = (term836 m n g f).
Proof. exact (@lem1982709 (term836 m n g f)). Qed.
Lemma lem7232607 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term980 m n g f) = (term836 m n g f).
Proof. exact (TRANS (@lem7232605 m n g f) (@lem7232606 m n g f)). Qed.
Lemma lem7232610 (f : nat -> real) (g : nat -> real) (n : nat) : (term860 f g n) = (term860 f g n).
Proof. exact (eq_refl (term860 f g n)). Qed.
Lemma lem7232611 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term979 m n g f) = (term983 m n g f).
Proof. exact (MK_COMB (@lem7232610 f g n) (@lem7232607 m n g f)). Qed.
Lemma lem7232612 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term978 m n g f) = (term983 m n g f).
Proof. exact (TRANS (@lem7232564 m n g f) (@lem7232611 m n g f)). Qed.
Lemma lem7232613 (f : nat -> real) (g : nat -> real) (m : nat) : (term605 f g m) = (term606 f g m).
Proof. exact (@lem1982749 term62 term62 (term374 f g m)). Qed.
Lemma lem7232615 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232616 : term62 = term63.
Proof. exact (@lem7232615 term13). Qed.
Lemma lem7232618 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232619 : term62 = term63.
Proof. exact (@lem7232618 term13). Qed.
Lemma lem7232620 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232621 : term64 = term65.
Proof. exact (MK_COMB (@lem7232620) (@lem7232619)). Qed.
Lemma lem7232622 : term415 = term416.
Proof. exact (MK_COMB (@lem7232621) (@lem7232616)). Qed.
Lemma lem7232623 : term416 = term417.
Proof. exact (@lem1981613 term62 term62 term44 term44). Qed.
Lemma lem7232625 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232626 : term71 = term72.
Proof. exact (@lem7232625 term13 term13). Qed.
Lemma lem7232627 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232628 : term74 = term13.
Proof. exact (EQ_MP (@lem7232627) (@lem940073)). Qed.
Lemma lem7232629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232630 : term72 = term44.
Proof. exact (MK_COMB (@lem7232629) (@lem7232628)). Qed.
Lemma lem7232631 : term71 = term44.
Proof. exact (TRANS (@lem7232626) (@lem7232630)). Qed.
Lemma lem7232633 (m : nat) (n : nat) : (term418 m n) = (term70 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7232634 : term415 = term72.
Proof. exact (@lem7232633 term13 term13). Qed.
Lemma lem7232635 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232636 : term74 = term13.
Proof. exact (EQ_MP (@lem7232635) (@lem940073)). Qed.
Lemma lem7232637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232638 : term72 = term44.
Proof. exact (MK_COMB (@lem7232637) (@lem7232636)). Qed.
Lemma lem7232639 : term415 = term44.
Proof. exact (TRANS (@lem7232634) (@lem7232638)). Qed.
Lemma lem7232640 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7232641 : term419 = term420.
Proof. exact (MK_COMB (@lem7232640) (@lem7232639)). Qed.
Lemma lem7232642 : term417 = term88.
Proof. exact (MK_COMB (@lem7232641) (@lem7232631)). Qed.
Lemma lem7232643 : term416 = term88.
Proof. exact (TRANS (@lem7232623) (@lem7232642)). Qed.
Lemma lem7232644 : term415 = term88.
Proof. exact (TRANS (@lem7232622) (@lem7232643)). Qed.
Lemma lem7232646 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7232647 : term88 = term44.
Proof. exact (@lem7232646 term44). Qed.
Lemma lem7232648 : term415 = term44.
Proof. exact (TRANS (@lem7232644) (@lem7232647)). Qed.
Lemma lem7232649 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232650 : term421 = term422.
Proof. exact (MK_COMB (@lem7232649) (@lem7232648)). Qed.
Lemma lem7232651 (f : nat -> real) (g : nat -> real) (m : nat) : (term374 f g m) = (term374 f g m).
Proof. exact (eq_refl (term374 f g m)). Qed.
Lemma lem7232652 (f : nat -> real) (g : nat -> real) (m : nat) : (term606 f g m) = (term607 f g m).
Proof. exact (MK_COMB (@lem7232650) (@lem7232651 f g m)). Qed.
Lemma lem7232653 (f : nat -> real) (g : nat -> real) (m : nat) : (term605 f g m) = (term607 f g m).
Proof. exact (TRANS (@lem7232613 f g m) (@lem7232652 f g m)). Qed.
Lemma lem7232654 (f : nat -> real) (g : nat -> real) (m : nat) : (term607 f g m) = (term374 f g m).
Proof. exact (@lem1982709 (term374 f g m)). Qed.
Lemma lem7232655 (f : nat -> real) (g : nat -> real) (m : nat) : (term605 f g m) = (term374 f g m).
Proof. exact (TRANS (@lem7232653 f g m) (@lem7232654 f g m)). Qed.
Lemma lem7232656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232657 (f : nat -> real) (g : nat -> real) (m : nat) : (term608 f g m) = (term609 f g m).
Proof. exact (MK_COMB (@lem7232656) (@lem7232655 f g m)). Qed.
Lemma lem7232658 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term977 m n g f) = (term984 m n g f).
Proof. exact (MK_COMB (@lem7232657 f g m) (@lem7232612 m n g f)). Qed.
Lemma lem7232659 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term976 m n g f) = (term984 m n g f).
Proof. exact (TRANS (@lem7232563 m n g f) (@lem7232658 m n g f)). Qed.
Lemma lem7232660 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term985 m n g f) = (term985 m n g f).
Proof. exact (eq_refl (term985 m n g f)). Qed.
Lemma lem7232661 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term975 m n g f) = (term986 m n g f).
Proof. exact (MK_COMB (@lem7232660 m n g f) (@lem7232659 m n g f)). Qed.
Lemma lem7232662 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term986 m n g f) = (term987 m n g f).
Proof. exact (@lem1982753 (term592 f g m) (term374 f g m) (term953 m n g f) (term983 m n g f)). Qed.
Lemma lem7232663 (f : nat -> real) (g : nat -> real) (m : nat) : (term988 f g m) = (term989 f g m).
Proof. exact (@lem1982713 term62 (term374 f g m)). Qed.
Lemma lem7232665 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7232666 : term44 = term88.
Proof. exact (@lem7232665 term13). Qed.
Lemma lem7232668 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232669 : term62 = term63.
Proof. exact (@lem7232668 term13). Qed.
Lemma lem7232670 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232671 : term104 = term105.
Proof. exact (MK_COMB (@lem7232670) (@lem7232669)). Qed.
Lemma lem7232672 : term106 = term107.
Proof. exact (MK_COMB (@lem7232671) (@lem7232666)). Qed.
Lemma lem7232673 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7232675 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232676 : term110 = term111.
Proof. exact (@lem7232675 (NUMERAL 0) term13). Qed.
Lemma lem7232677 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232678 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232679 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232678 h1) (fun h1 : term111 = True => @lem7232677)). Qed.
Lemma lem7232680 : term111 = True.
Proof. exact (EQ_MP (@lem7232679) (@lem7232677)). Qed.
Lemma lem7232681 : term110 = True.
Proof. exact (TRANS (@lem7232676) (@lem7232680)). Qed.
Lemma lem7232682 : True = term110.
Proof. exact (SYM (@lem7232681)). Qed.
Lemma lem7232683 : term110.
Proof. exact (EQ_MP (@lem7232682) (@lem0)). Qed.
Lemma lem7232684 : term113.
Proof. exact (@lem7232673 (@lem7232683)). Qed.
Lemma lem7232686 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232687 : term110 = term111.
Proof. exact (@lem7232686 (NUMERAL 0) term13). Qed.
Lemma lem7232688 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232689 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232690 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232689 h1) (fun h1 : term111 = True => @lem7232688)). Qed.
Lemma lem7232691 : term111 = True.
Proof. exact (EQ_MP (@lem7232690) (@lem7232688)). Qed.
Lemma lem7232692 : term110 = True.
Proof. exact (TRANS (@lem7232687) (@lem7232691)). Qed.
Lemma lem7232693 : True = term110.
Proof. exact (SYM (@lem7232692)). Qed.
Lemma lem7232694 : term110.
Proof. exact (EQ_MP (@lem7232693) (@lem0)). Qed.
Lemma lem7232695 : term114.
Proof. exact (@lem7232684 (@lem7232694)). Qed.
Lemma lem7232697 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232698 : term110 = term111.
Proof. exact (@lem7232697 (NUMERAL 0) term13). Qed.
Lemma lem7232699 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232700 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232701 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232700 h1) (fun h1 : term111 = True => @lem7232699)). Qed.
Lemma lem7232702 : term111 = True.
Proof. exact (EQ_MP (@lem7232701) (@lem7232699)). Qed.
Lemma lem7232703 : term110 = True.
Proof. exact (TRANS (@lem7232698) (@lem7232702)). Qed.
Lemma lem7232704 : True = term110.
Proof. exact (SYM (@lem7232703)). Qed.
Lemma lem7232705 : term110.
Proof. exact (EQ_MP (@lem7232704) (@lem0)). Qed.
Lemma lem7232706 : term115.
Proof. exact (@lem7232695 (@lem7232705)). Qed.
Lemma lem7232708 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232709 : term71 = term72.
Proof. exact (@lem7232708 term13 term13). Qed.
Lemma lem7232710 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232711 : term74 = term13.
Proof. exact (EQ_MP (@lem7232710) (@lem940073)). Qed.
Lemma lem7232712 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232713 : term72 = term44.
Proof. exact (MK_COMB (@lem7232712) (@lem7232711)). Qed.
Lemma lem7232714 : term71 = term44.
Proof. exact (TRANS (@lem7232709) (@lem7232713)). Qed.
Lemma lem7232716 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7232717 : term89 = term94.
Proof. exact (@lem7232716 term13 term13). Qed.
Lemma lem7232718 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232719 : term74 = term13.
Proof. exact (EQ_MP (@lem7232718) (@lem940073)). Qed.
Lemma lem7232720 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232721 : term72 = term44.
Proof. exact (MK_COMB (@lem7232720) (@lem7232719)). Qed.
Lemma lem7232722 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7232723 : term94 = term62.
Proof. exact (MK_COMB (@lem7232722) (@lem7232721)). Qed.
Lemma lem7232724 : term89 = term62.
Proof. exact (TRANS (@lem7232717) (@lem7232723)). Qed.
Lemma lem7232725 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232726 : term116 = term104.
Proof. exact (MK_COMB (@lem7232725) (@lem7232724)). Qed.
Lemma lem7232727 : term117 = term106.
Proof. exact (MK_COMB (@lem7232726) (@lem7232714)). Qed.
Lemma lem7232729 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7232730 : term106 = term29.
Proof. exact (@lem7232729 term13). Qed.
Lemma lem7232731 : term117 = term29.
Proof. exact (TRANS (@lem7232727) (@lem7232730)). Qed.
Lemma lem7232732 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232733 : term119 = term120.
Proof. exact (MK_COMB (@lem7232732) (@lem7232731)). Qed.
Lemma lem7232734 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7232735 : term121 = term122.
Proof. exact (MK_COMB (@lem7232733) (@lem7232734)). Qed.
Lemma lem7232737 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232738 : term122 = term29.
Proof. exact (@lem7232737 term13). Qed.
Lemma lem7232739 : term121 = term29.
Proof. exact (TRANS (@lem7232735) (@lem7232738)). Qed.
Lemma lem7232741 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232742 : term71 = term72.
Proof. exact (@lem7232741 term13 term13). Qed.
Lemma lem7232743 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232744 : term74 = term13.
Proof. exact (EQ_MP (@lem7232743) (@lem940073)). Qed.
Lemma lem7232745 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232746 : term72 = term44.
Proof. exact (MK_COMB (@lem7232745) (@lem7232744)). Qed.
Lemma lem7232747 : term71 = term44.
Proof. exact (TRANS (@lem7232742) (@lem7232746)). Qed.
Lemma lem7232748 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7232749 : term124 = term122.
Proof. exact (MK_COMB (@lem7232748) (@lem7232747)). Qed.
Lemma lem7232751 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232752 : term122 = term29.
Proof. exact (@lem7232751 term13). Qed.
Lemma lem7232753 : term124 = term29.
Proof. exact (TRANS (@lem7232749) (@lem7232752)). Qed.
Lemma lem7232754 : term29 = term124.
Proof. exact (SYM (@lem7232753)). Qed.
Lemma lem7232755 : term121 = term124.
Proof. exact (TRANS (@lem7232739) (@lem7232754)). Qed.
Lemma lem7232756 : term107 = term59.
Proof. exact (@lem7232706 (@lem7232755)). Qed.
Lemma lem7232757 : term106 = term59.
Proof. exact (TRANS (@lem7232672) (@lem7232756)). Qed.
Lemma lem7232759 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7232760 : term59 = term29.
Proof. exact (@lem7232759 term29). Qed.
Lemma lem7232761 : term106 = term29.
Proof. exact (TRANS (@lem7232757) (@lem7232760)). Qed.
Lemma lem7232762 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232763 : term125 = term120.
Proof. exact (MK_COMB (@lem7232762) (@lem7232761)). Qed.
Lemma lem7232764 (f : nat -> real) (g : nat -> real) (m : nat) : (term374 f g m) = (term374 f g m).
Proof. exact (eq_refl (term374 f g m)). Qed.
Lemma lem7232765 (f : nat -> real) (g : nat -> real) (m : nat) : (term989 f g m) = (term990 f g m).
Proof. exact (MK_COMB (@lem7232763) (@lem7232764 f g m)). Qed.
Lemma lem7232766 (f : nat -> real) (g : nat -> real) (m : nat) : (term988 f g m) = (term990 f g m).
Proof. exact (TRANS (@lem7232663 f g m) (@lem7232765 f g m)). Qed.
Lemma lem7232767 (f : nat -> real) (g : nat -> real) (m : nat) : (term990 f g m) = term29.
Proof. exact (@lem1982719 (term374 f g m)). Qed.
Lemma lem7232768 (f : nat -> real) (g : nat -> real) (m : nat) : (term988 f g m) = term29.
Proof. exact (TRANS (@lem7232766 f g m) (@lem7232767 f g m)). Qed.
Lemma lem7232769 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232770 (f : nat -> real) (g : nat -> real) (m : nat) : (term991 f g m) = term128.
Proof. exact (MK_COMB (@lem7232769) (@lem7232768 f g m)). Qed.
Lemma lem7232771 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term992 m n g f) = (term993 m n g f).
Proof. exact (@lem1982753 (term857 f g n) (term858 f g n) (term950 m n g f) (term836 m n g f)). Qed.
Lemma lem7232772 (f : nat -> real) (g : nat -> real) (n : nat) : (term914 f g n) = (term915 f g n).
Proof. exact (@lem1982715 term62 (term857 f g n)). Qed.
Lemma lem7232774 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7232775 : term44 = term88.
Proof. exact (@lem7232774 term13). Qed.
Lemma lem7232777 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232778 : term62 = term63.
Proof. exact (@lem7232777 term13). Qed.
Lemma lem7232779 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232780 : term104 = term105.
Proof. exact (MK_COMB (@lem7232779) (@lem7232778)). Qed.
Lemma lem7232781 : term106 = term107.
Proof. exact (MK_COMB (@lem7232780) (@lem7232775)). Qed.
Lemma lem7232782 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7232784 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232785 : term110 = term111.
Proof. exact (@lem7232784 (NUMERAL 0) term13). Qed.
Lemma lem7232786 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232787 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232788 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232787 h1) (fun h1 : term111 = True => @lem7232786)). Qed.
Lemma lem7232789 : term111 = True.
Proof. exact (EQ_MP (@lem7232788) (@lem7232786)). Qed.
Lemma lem7232790 : term110 = True.
Proof. exact (TRANS (@lem7232785) (@lem7232789)). Qed.
Lemma lem7232791 : True = term110.
Proof. exact (SYM (@lem7232790)). Qed.
Lemma lem7232792 : term110.
Proof. exact (EQ_MP (@lem7232791) (@lem0)). Qed.
Lemma lem7232793 : term113.
Proof. exact (@lem7232782 (@lem7232792)). Qed.
Lemma lem7232795 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232796 : term110 = term111.
Proof. exact (@lem7232795 (NUMERAL 0) term13). Qed.
Lemma lem7232797 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232798 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232799 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232798 h1) (fun h1 : term111 = True => @lem7232797)). Qed.
Lemma lem7232800 : term111 = True.
Proof. exact (EQ_MP (@lem7232799) (@lem7232797)). Qed.
Lemma lem7232801 : term110 = True.
Proof. exact (TRANS (@lem7232796) (@lem7232800)). Qed.
Lemma lem7232802 : True = term110.
Proof. exact (SYM (@lem7232801)). Qed.
Lemma lem7232803 : term110.
Proof. exact (EQ_MP (@lem7232802) (@lem0)). Qed.
Lemma lem7232804 : term114.
Proof. exact (@lem7232793 (@lem7232803)). Qed.
Lemma lem7232806 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232807 : term110 = term111.
Proof. exact (@lem7232806 (NUMERAL 0) term13). Qed.
Lemma lem7232808 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232809 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232810 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232809 h1) (fun h1 : term111 = True => @lem7232808)). Qed.
Lemma lem7232811 : term111 = True.
Proof. exact (EQ_MP (@lem7232810) (@lem7232808)). Qed.
Lemma lem7232812 : term110 = True.
Proof. exact (TRANS (@lem7232807) (@lem7232811)). Qed.
Lemma lem7232813 : True = term110.
Proof. exact (SYM (@lem7232812)). Qed.
Lemma lem7232814 : term110.
Proof. exact (EQ_MP (@lem7232813) (@lem0)). Qed.
Lemma lem7232815 : term115.
Proof. exact (@lem7232804 (@lem7232814)). Qed.
Lemma lem7232817 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232818 : term71 = term72.
Proof. exact (@lem7232817 term13 term13). Qed.
Lemma lem7232819 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232820 : term74 = term13.
Proof. exact (EQ_MP (@lem7232819) (@lem940073)). Qed.
Lemma lem7232821 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232822 : term72 = term44.
Proof. exact (MK_COMB (@lem7232821) (@lem7232820)). Qed.
Lemma lem7232823 : term71 = term44.
Proof. exact (TRANS (@lem7232818) (@lem7232822)). Qed.
Lemma lem7232825 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7232826 : term89 = term94.
Proof. exact (@lem7232825 term13 term13). Qed.
Lemma lem7232827 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232828 : term74 = term13.
Proof. exact (EQ_MP (@lem7232827) (@lem940073)). Qed.
Lemma lem7232829 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232830 : term72 = term44.
Proof. exact (MK_COMB (@lem7232829) (@lem7232828)). Qed.
Lemma lem7232831 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7232832 : term94 = term62.
Proof. exact (MK_COMB (@lem7232831) (@lem7232830)). Qed.
Lemma lem7232833 : term89 = term62.
Proof. exact (TRANS (@lem7232826) (@lem7232832)). Qed.
Lemma lem7232834 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232835 : term116 = term104.
Proof. exact (MK_COMB (@lem7232834) (@lem7232833)). Qed.
Lemma lem7232836 : term117 = term106.
Proof. exact (MK_COMB (@lem7232835) (@lem7232823)). Qed.
Lemma lem7232838 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7232839 : term106 = term29.
Proof. exact (@lem7232838 term13). Qed.
Lemma lem7232840 : term117 = term29.
Proof. exact (TRANS (@lem7232836) (@lem7232839)). Qed.
Lemma lem7232841 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232842 : term119 = term120.
Proof. exact (MK_COMB (@lem7232841) (@lem7232840)). Qed.
Lemma lem7232843 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7232844 : term121 = term122.
Proof. exact (MK_COMB (@lem7232842) (@lem7232843)). Qed.
Lemma lem7232846 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232847 : term122 = term29.
Proof. exact (@lem7232846 term13). Qed.
Lemma lem7232848 : term121 = term29.
Proof. exact (TRANS (@lem7232844) (@lem7232847)). Qed.
Lemma lem7232850 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232851 : term71 = term72.
Proof. exact (@lem7232850 term13 term13). Qed.
Lemma lem7232852 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232853 : term74 = term13.
Proof. exact (EQ_MP (@lem7232852) (@lem940073)). Qed.
Lemma lem7232854 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232855 : term72 = term44.
Proof. exact (MK_COMB (@lem7232854) (@lem7232853)). Qed.
Lemma lem7232856 : term71 = term44.
Proof. exact (TRANS (@lem7232851) (@lem7232855)). Qed.
Lemma lem7232857 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7232858 : term124 = term122.
Proof. exact (MK_COMB (@lem7232857) (@lem7232856)). Qed.
Lemma lem7232860 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232861 : term122 = term29.
Proof. exact (@lem7232860 term13). Qed.
Lemma lem7232862 : term124 = term29.
Proof. exact (TRANS (@lem7232858) (@lem7232861)). Qed.
Lemma lem7232863 : term29 = term124.
Proof. exact (SYM (@lem7232862)). Qed.
Lemma lem7232864 : term121 = term124.
Proof. exact (TRANS (@lem7232848) (@lem7232863)). Qed.
Lemma lem7232865 : term107 = term59.
Proof. exact (@lem7232815 (@lem7232864)). Qed.
Lemma lem7232866 : term106 = term59.
Proof. exact (TRANS (@lem7232781) (@lem7232865)). Qed.
Lemma lem7232868 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7232869 : term59 = term29.
Proof. exact (@lem7232868 term29). Qed.
Lemma lem7232870 : term106 = term29.
Proof. exact (TRANS (@lem7232866) (@lem7232869)). Qed.
Lemma lem7232871 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232872 : term125 = term120.
Proof. exact (MK_COMB (@lem7232871) (@lem7232870)). Qed.
Lemma lem7232873 (f : nat -> real) (g : nat -> real) (n : nat) : (term857 f g n) = (term857 f g n).
Proof. exact (eq_refl (term857 f g n)). Qed.
Lemma lem7232874 (f : nat -> real) (g : nat -> real) (n : nat) : (term915 f g n) = (term916 f g n).
Proof. exact (MK_COMB (@lem7232872) (@lem7232873 f g n)). Qed.
Lemma lem7232875 (f : nat -> real) (g : nat -> real) (n : nat) : (term914 f g n) = (term916 f g n).
Proof. exact (TRANS (@lem7232772 f g n) (@lem7232874 f g n)). Qed.
Lemma lem7232876 (f : nat -> real) (g : nat -> real) (n : nat) : (term916 f g n) = term29.
Proof. exact (@lem1982719 (term857 f g n)). Qed.
Lemma lem7232877 (f : nat -> real) (g : nat -> real) (n : nat) : (term914 f g n) = term29.
Proof. exact (TRANS (@lem7232875 f g n) (@lem7232876 f g n)). Qed.
Lemma lem7232878 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232879 (f : nat -> real) (g : nat -> real) (n : nat) : (term994 f g n) = term128.
Proof. exact (MK_COMB (@lem7232878) (@lem7232877 f g n)). Qed.
Lemma lem7232880 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term995 m n g f) = (term996 m n g f).
Proof. exact (@lem1982713 term62 (term836 m n g f)). Qed.
Lemma lem7232882 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7232883 : term44 = term88.
Proof. exact (@lem7232882 term13). Qed.
Lemma lem7232885 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7232886 : term62 = term63.
Proof. exact (@lem7232885 term13). Qed.
Lemma lem7232887 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232888 : term104 = term105.
Proof. exact (MK_COMB (@lem7232887) (@lem7232886)). Qed.
Lemma lem7232889 : term106 = term107.
Proof. exact (MK_COMB (@lem7232888) (@lem7232883)). Qed.
Lemma lem7232890 : term108.
Proof. exact (@lem1981473 term62 term44 term44 term44 term29 term44). Qed.
Lemma lem7232892 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232893 : term110 = term111.
Proof. exact (@lem7232892 (NUMERAL 0) term13). Qed.
Lemma lem7232894 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232895 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232896 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232895 h1) (fun h1 : term111 = True => @lem7232894)). Qed.
Lemma lem7232897 : term111 = True.
Proof. exact (EQ_MP (@lem7232896) (@lem7232894)). Qed.
Lemma lem7232898 : term110 = True.
Proof. exact (TRANS (@lem7232893) (@lem7232897)). Qed.
Lemma lem7232899 : True = term110.
Proof. exact (SYM (@lem7232898)). Qed.
Lemma lem7232900 : term110.
Proof. exact (EQ_MP (@lem7232899) (@lem0)). Qed.
Lemma lem7232901 : term113.
Proof. exact (@lem7232890 (@lem7232900)). Qed.
Lemma lem7232903 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232904 : term110 = term111.
Proof. exact (@lem7232903 (NUMERAL 0) term13). Qed.
Lemma lem7232905 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232906 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232907 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232906 h1) (fun h1 : term111 = True => @lem7232905)). Qed.
Lemma lem7232908 : term111 = True.
Proof. exact (EQ_MP (@lem7232907) (@lem7232905)). Qed.
Lemma lem7232909 : term110 = True.
Proof. exact (TRANS (@lem7232904) (@lem7232908)). Qed.
Lemma lem7232910 : True = term110.
Proof. exact (SYM (@lem7232909)). Qed.
Lemma lem7232911 : term110.
Proof. exact (EQ_MP (@lem7232910) (@lem0)). Qed.
Lemma lem7232912 : term114.
Proof. exact (@lem7232901 (@lem7232911)). Qed.
Lemma lem7232914 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7232915 : term110 = term111.
Proof. exact (@lem7232914 (NUMERAL 0) term13). Qed.
Lemma lem7232916 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7232917 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7232918 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7232917 h1) (fun h1 : term111 = True => @lem7232916)). Qed.
Lemma lem7232919 : term111 = True.
Proof. exact (EQ_MP (@lem7232918) (@lem7232916)). Qed.
Lemma lem7232920 : term110 = True.
Proof. exact (TRANS (@lem7232915) (@lem7232919)). Qed.
Lemma lem7232921 : True = term110.
Proof. exact (SYM (@lem7232920)). Qed.
Lemma lem7232922 : term110.
Proof. exact (EQ_MP (@lem7232921) (@lem0)). Qed.
Lemma lem7232923 : term115.
Proof. exact (@lem7232912 (@lem7232922)). Qed.
Lemma lem7232925 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232926 : term71 = term72.
Proof. exact (@lem7232925 term13 term13). Qed.
Lemma lem7232927 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232928 : term74 = term13.
Proof. exact (EQ_MP (@lem7232927) (@lem940073)). Qed.
Lemma lem7232929 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232930 : term72 = term44.
Proof. exact (MK_COMB (@lem7232929) (@lem7232928)). Qed.
Lemma lem7232931 : term71 = term44.
Proof. exact (TRANS (@lem7232926) (@lem7232930)). Qed.
Lemma lem7232933 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7232934 : term89 = term94.
Proof. exact (@lem7232933 term13 term13). Qed.
Lemma lem7232935 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232936 : term74 = term13.
Proof. exact (EQ_MP (@lem7232935) (@lem940073)). Qed.
Lemma lem7232937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232938 : term72 = term44.
Proof. exact (MK_COMB (@lem7232937) (@lem7232936)). Qed.
Lemma lem7232939 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7232940 : term94 = term62.
Proof. exact (MK_COMB (@lem7232939) (@lem7232938)). Qed.
Lemma lem7232941 : term89 = term62.
Proof. exact (TRANS (@lem7232934) (@lem7232940)). Qed.
Lemma lem7232942 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7232943 : term116 = term104.
Proof. exact (MK_COMB (@lem7232942) (@lem7232941)). Qed.
Lemma lem7232944 : term117 = term106.
Proof. exact (MK_COMB (@lem7232943) (@lem7232931)). Qed.
Lemma lem7232946 (m : nat) : (term118 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7232947 : term106 = term29.
Proof. exact (@lem7232946 term13). Qed.
Lemma lem7232948 : term117 = term29.
Proof. exact (TRANS (@lem7232944) (@lem7232947)). Qed.
Lemma lem7232949 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232950 : term119 = term120.
Proof. exact (MK_COMB (@lem7232949) (@lem7232948)). Qed.
Lemma lem7232951 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem7232952 : term121 = term122.
Proof. exact (MK_COMB (@lem7232950) (@lem7232951)). Qed.
Lemma lem7232954 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232955 : term122 = term29.
Proof. exact (@lem7232954 term13). Qed.
Lemma lem7232956 : term121 = term29.
Proof. exact (TRANS (@lem7232952) (@lem7232955)). Qed.
Lemma lem7232958 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7232959 : term71 = term72.
Proof. exact (@lem7232958 term13 term13). Qed.
Lemma lem7232960 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7232961 : term74 = term13.
Proof. exact (EQ_MP (@lem7232960) (@lem940073)). Qed.
Lemma lem7232962 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7232963 : term72 = term44.
Proof. exact (MK_COMB (@lem7232962) (@lem7232961)). Qed.
Lemma lem7232964 : term71 = term44.
Proof. exact (TRANS (@lem7232959) (@lem7232963)). Qed.
Lemma lem7232965 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7232966 : term124 = term122.
Proof. exact (MK_COMB (@lem7232965) (@lem7232964)). Qed.
Lemma lem7232968 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7232969 : term122 = term29.
Proof. exact (@lem7232968 term13). Qed.
Lemma lem7232970 : term124 = term29.
Proof. exact (TRANS (@lem7232966) (@lem7232969)). Qed.
Lemma lem7232971 : term29 = term124.
Proof. exact (SYM (@lem7232970)). Qed.
Lemma lem7232972 : term121 = term124.
Proof. exact (TRANS (@lem7232956) (@lem7232971)). Qed.
Lemma lem7232973 : term107 = term59.
Proof. exact (@lem7232923 (@lem7232972)). Qed.
Lemma lem7232974 : term106 = term59.
Proof. exact (TRANS (@lem7232889) (@lem7232973)). Qed.
Lemma lem7232976 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7232977 : term59 = term29.
Proof. exact (@lem7232976 term29). Qed.
Lemma lem7232978 : term106 = term29.
Proof. exact (TRANS (@lem7232974) (@lem7232977)). Qed.
Lemma lem7232979 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7232980 : term125 = term120.
Proof. exact (MK_COMB (@lem7232979) (@lem7232978)). Qed.
Lemma lem7232981 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term836 m n g f) = (term836 m n g f).
Proof. exact (eq_refl (term836 m n g f)). Qed.
Lemma lem7232982 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term996 m n g f) = (term997 m n g f).
Proof. exact (MK_COMB (@lem7232980) (@lem7232981 m n g f)). Qed.
Lemma lem7232983 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term995 m n g f) = (term997 m n g f).
Proof. exact (TRANS (@lem7232880 m n g f) (@lem7232982 m n g f)). Qed.
Lemma lem7232984 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term997 m n g f) = term29.
Proof. exact (@lem1982719 (term836 m n g f)). Qed.
Lemma lem7232985 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term995 m n g f) = term29.
Proof. exact (TRANS (@lem7232983 m n g f) (@lem7232984 m n g f)). Qed.
Lemma lem7232986 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term993 m n g f) = term465.
Proof. exact (MK_COMB (@lem7232879 f g n) (@lem7232985 m n g f)). Qed.
Lemma lem7232987 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term992 m n g f) = term465.
Proof. exact (TRANS (@lem7232771 m n g f) (@lem7232986 m n g f)). Qed.
Lemma lem7232988 : term465 = term29.
Proof. exact (@lem1982721 term29). Qed.
Lemma lem7232989 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term992 m n g f) = term29.
Proof. exact (TRANS (@lem7232987 m n g f) (@lem7232988)). Qed.
Lemma lem7232990 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term987 m n g f) = term465.
Proof. exact (MK_COMB (@lem7232770 f g m) (@lem7232989 m n g f)). Qed.
Lemma lem7232991 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term986 m n g f) = term465.
Proof. exact (TRANS (@lem7232662 m n g f) (@lem7232990 m n g f)). Qed.
Lemma lem7232992 : term465 = term29.
Proof. exact (@lem1982721 term29). Qed.
Lemma lem7232993 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term986 m n g f) = term29.
Proof. exact (TRANS (@lem7232991 m n g f) (@lem7232992)). Qed.
Lemma lem7232994 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term975 m n g f) = term29.
Proof. exact (TRANS (@lem7232661 m n g f) (@lem7232993 m n g f)). Qed.
Lemma lem7232995 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term974 m n g f) = term29.
Proof. exact (TRANS (@lem7232562 m n g f) (@lem7232994 m n g f)). Qed.
Lemma lem7232996 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term973 m g f n) = term29.
Proof. exact (TRANS (@lem7232561 m n g f) (@lem7232995 m n g f)). Qed.
Lemma lem7232997 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7232998 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term998 m g f n) = term467.
Proof. exact (MK_COMB (@lem7232997) (@lem7232996 m g f n)). Qed.
Lemma lem7232999 : term467 = term66.
Proof. exact (@lem1982785 term29). Qed.
Lemma lem7233001 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233002 : term29 = term59.
Proof. exact (@lem7233001 (NUMERAL 0)). Qed.
Lemma lem7233004 (x : nat) : (term60 x) = (term61 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7233005 : term62 = term63.
Proof. exact (@lem7233004 term13). Qed.
Lemma lem7233006 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233007 : term64 = term65.
Proof. exact (MK_COMB (@lem7233006) (@lem7233005)). Qed.
Lemma lem7233008 : term66 = term67.
Proof. exact (MK_COMB (@lem7233007) (@lem7233002)). Qed.
Lemma lem7233009 : term67 = term68.
Proof. exact (@lem1981613 term62 term29 term44 term44). Qed.
Lemma lem7233011 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7233012 : term71 = term72.
Proof. exact (@lem7233011 term13 term13). Qed.
Lemma lem7233013 : (term73 = (BIT1 0)) = (term74 = term13).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7233014 : term74 = term13.
Proof. exact (EQ_MP (@lem7233013) (@lem940073)). Qed.
Lemma lem7233015 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7233016 : term72 = term44.
Proof. exact (MK_COMB (@lem7233015) (@lem7233014)). Qed.
Lemma lem7233017 : term71 = term44.
Proof. exact (TRANS (@lem7233012) (@lem7233016)). Qed.
Lemma lem7233019 (x : nat) : (term75 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7233020 : term66 = term29.
Proof. exact (@lem7233019 term13). Qed.
Lemma lem7233021 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7233022 : term76 = term77.
Proof. exact (MK_COMB (@lem7233021) (@lem7233020)). Qed.
Lemma lem7233023 : term68 = term59.
Proof. exact (MK_COMB (@lem7233022) (@lem7233017)). Qed.
Lemma lem7233024 : term67 = term59.
Proof. exact (TRANS (@lem7233009) (@lem7233023)). Qed.
Lemma lem7233025 : term66 = term59.
Proof. exact (TRANS (@lem7233008) (@lem7233024)). Qed.
Lemma lem7233027 (x : real) : (term78 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7233028 : term59 = term29.
Proof. exact (@lem7233027 term29). Qed.
Lemma lem7233029 : term66 = term29.
Proof. exact (TRANS (@lem7233025) (@lem7233028)). Qed.
Lemma lem7233030 : term467 = term29.
Proof. exact (TRANS (@lem7232999) (@lem7233029)). Qed.
Lemma lem7233031 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term999 m g f n) = (term999 m g f n).
Proof. exact (eq_refl (term999 m g f n)). Qed.
Lemma lem7233032 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : ((term998 m g f n) = term467) = ((term998 m g f n) = term29).
Proof. exact (MK_COMB (@lem7233031 m g f n) (@lem7233030)). Qed.
Lemma lem7233033 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term998 m g f n) = term29.
Proof. exact (EQ_MP (@lem7233032 m g f n) (@lem7232998 m g f n)). Qed.
Lemma lem7233034 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7233035 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term1000 m g f n) = term470.
Proof. exact (MK_COMB (@lem7233034) (@lem7233033 m g f n)). Qed.
Lemma lem7233036 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7233037 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term1001 m g f n) = term472.
Proof. exact (MK_COMB (@lem7233035 m g f n) (@lem7233036)). Qed.
Lemma lem7233038 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7233039 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term1002 m g f n) = term470.
Proof. exact (MK_COMB (@lem7233038) (@lem7232996 m g f n)). Qed.
Lemma lem7233040 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem7233041 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term1003 m g f n) = term472.
Proof. exact (MK_COMB (@lem7233039 m g f n) (@lem7233040)). Qed.
Lemma lem7233042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7233043 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term1004 m g f n) = term476.
Proof. exact (MK_COMB (@lem7233042) (@lem7233041 m g f n)). Qed.
Lemma lem7233044 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term927 m g f n) = term477.
Proof. exact (MK_COMB (@lem7233043 m g f n) (@lem7233037 m g f n)). Qed.
Lemma lem7233058 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term926 m g f n) = term477.
Proof. exact (TRANS (@lem7232116 m g f n) (@lem7233044 m g f n)). Qed.
Lemma lem7233068 (h1 : term477) : term477.
Proof. exact (h1). Qed.
Lemma lem7233069 (h1 : term472) : term472.
Proof. exact (h1). Qed.
Lemma lem7233071 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7233072 : term472 = term478.
Proof. exact (@lem7233071 term29 term29). Qed.
Lemma lem7233074 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233075 : term29 = term59.
Proof. exact (@lem7233074 (NUMERAL 0)). Qed.
Lemma lem7233077 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233078 : term29 = term59.
Proof. exact (@lem7233077 (NUMERAL 0)). Qed.
Lemma lem7233079 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7233080 : term479 = term480.
Proof. exact (MK_COMB (@lem7233079) (@lem7233078)). Qed.
Lemma lem7233081 : term478 = term481.
Proof. exact (MK_COMB (@lem7233080) (@lem7233075)). Qed.
Lemma lem7233082 : term482.
Proof. exact (@lem1980255 term29 term44 term29 term44). Qed.
Lemma lem7233084 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233085 : term110 = term111.
Proof. exact (@lem7233084 (NUMERAL 0) term13). Qed.
Lemma lem7233086 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233087 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233088 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7233087 h1) (fun h1 : term111 = True => @lem7233086)). Qed.
Lemma lem7233089 : term111 = True.
Proof. exact (EQ_MP (@lem7233088) (@lem7233086)). Qed.
Lemma lem7233090 : term110 = True.
Proof. exact (TRANS (@lem7233085) (@lem7233089)). Qed.
Lemma lem7233091 : True = term110.
Proof. exact (SYM (@lem7233090)). Qed.
Lemma lem7233092 : term110.
Proof. exact (EQ_MP (@lem7233091) (@lem0)). Qed.
Lemma lem7233093 : term483.
Proof. exact (@lem7233082 (@lem7233092)). Qed.
Lemma lem7233095 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233096 : term110 = term111.
Proof. exact (@lem7233095 (NUMERAL 0) term13). Qed.
Lemma lem7233097 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233098 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233099 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7233098 h1) (fun h1 : term111 = True => @lem7233097)). Qed.
Lemma lem7233100 : term111 = True.
Proof. exact (EQ_MP (@lem7233099) (@lem7233097)). Qed.
Lemma lem7233101 : term110 = True.
Proof. exact (TRANS (@lem7233096) (@lem7233100)). Qed.
Lemma lem7233102 : True = term110.
Proof. exact (SYM (@lem7233101)). Qed.
Lemma lem7233103 : term110.
Proof. exact (EQ_MP (@lem7233102) (@lem0)). Qed.
Lemma lem7233104 : term481 = term484.
Proof. exact (@lem7233093 (@lem7233103)). Qed.
Lemma lem7233106 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233107 : term122 = term29.
Proof. exact (@lem7233106 term13). Qed.
Lemma lem7233109 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233110 : term122 = term29.
Proof. exact (@lem7233109 term13). Qed.
Lemma lem7233111 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7233112 : term485 = term479.
Proof. exact (MK_COMB (@lem7233111) (@lem7233110)). Qed.
Lemma lem7233113 : term484 = term478.
Proof. exact (MK_COMB (@lem7233112) (@lem7233107)). Qed.
Lemma lem7233115 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233116 : term478 = term486.
Proof. exact (@lem7233115 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7233117 : term486 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7233118 : term478 = False.
Proof. exact (TRANS (@lem7233116) (@lem7233117)). Qed.
Lemma lem7233119 : term484 = False.
Proof. exact (TRANS (@lem7233113) (@lem7233118)). Qed.
Lemma lem7233120 : term481 = False.
Proof. exact (TRANS (@lem7233104) (@lem7233119)). Qed.
Lemma lem7233121 : term478 = False.
Proof. exact (TRANS (@lem7233081) (@lem7233120)). Qed.
Lemma lem7233122 : term472 = False.
Proof. exact (TRANS (@lem7233072) (@lem7233121)). Qed.
Lemma lem7233123 (h1 : term472) : False.
Proof. exact (EQ_MP (@lem7233122) (@lem7233069 h1)). Qed.
Lemma lem7233124 (h1 : term472) : term472.
Proof. exact (h1). Qed.
Lemma lem7233126 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7233127 : term472 = term478.
Proof. exact (@lem7233126 term29 term29). Qed.
Lemma lem7233129 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233130 : term29 = term59.
Proof. exact (@lem7233129 (NUMERAL 0)). Qed.
Lemma lem7233132 (x : nat) : (real_of_num x) = (term58 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7233133 : term29 = term59.
Proof. exact (@lem7233132 (NUMERAL 0)). Qed.
Lemma lem7233134 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7233135 : term479 = term480.
Proof. exact (MK_COMB (@lem7233134) (@lem7233133)). Qed.
Lemma lem7233136 : term478 = term481.
Proof. exact (MK_COMB (@lem7233135) (@lem7233130)). Qed.
Lemma lem7233137 : term482.
Proof. exact (@lem1980255 term29 term44 term29 term44). Qed.
Lemma lem7233139 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233140 : term110 = term111.
Proof. exact (@lem7233139 (NUMERAL 0) term13). Qed.
Lemma lem7233141 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233142 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233143 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7233142 h1) (fun h1 : term111 = True => @lem7233141)). Qed.
Lemma lem7233144 : term111 = True.
Proof. exact (EQ_MP (@lem7233143) (@lem7233141)). Qed.
Lemma lem7233145 : term110 = True.
Proof. exact (TRANS (@lem7233140) (@lem7233144)). Qed.
Lemma lem7233146 : True = term110.
Proof. exact (SYM (@lem7233145)). Qed.
Lemma lem7233147 : term110.
Proof. exact (EQ_MP (@lem7233146) (@lem0)). Qed.
Lemma lem7233148 : term483.
Proof. exact (@lem7233137 (@lem7233147)). Qed.
Lemma lem7233150 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233151 : term110 = term111.
Proof. exact (@lem7233150 (NUMERAL 0) term13). Qed.
Lemma lem7233152 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7233153 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7233154 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem7233153 h1) (fun h1 : term111 = True => @lem7233152)). Qed.
Lemma lem7233155 : term111 = True.
Proof. exact (EQ_MP (@lem7233154) (@lem7233152)). Qed.
Lemma lem7233156 : term110 = True.
Proof. exact (TRANS (@lem7233151) (@lem7233155)). Qed.
Lemma lem7233157 : True = term110.
Proof. exact (SYM (@lem7233156)). Qed.
Lemma lem7233158 : term110.
Proof. exact (EQ_MP (@lem7233157) (@lem0)). Qed.
Lemma lem7233159 : term481 = term484.
Proof. exact (@lem7233148 (@lem7233158)). Qed.
Lemma lem7233161 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233162 : term122 = term29.
Proof. exact (@lem7233161 term13). Qed.
Lemma lem7233164 (x : nat) : (term123 x) = term29.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7233165 : term122 = term29.
Proof. exact (@lem7233164 term13). Qed.
Lemma lem7233166 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7233167 : term485 = term479.
Proof. exact (MK_COMB (@lem7233166) (@lem7233165)). Qed.
Lemma lem7233168 : term484 = term478.
Proof. exact (MK_COMB (@lem7233167) (@lem7233162)). Qed.
Lemma lem7233170 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7233171 : term478 = term486.
Proof. exact (@lem7233170 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7233172 : term486 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7233173 : term478 = False.
Proof. exact (TRANS (@lem7233171) (@lem7233172)). Qed.
Lemma lem7233174 : term484 = False.
Proof. exact (TRANS (@lem7233168) (@lem7233173)). Qed.
Lemma lem7233175 : term481 = False.
Proof. exact (TRANS (@lem7233159) (@lem7233174)). Qed.
Lemma lem7233176 : term478 = False.
Proof. exact (TRANS (@lem7233136) (@lem7233175)). Qed.
Lemma lem7233177 : term472 = False.
Proof. exact (TRANS (@lem7233127) (@lem7233176)). Qed.
Lemma lem7233178 (h1 : term472) : False.
Proof. exact (EQ_MP (@lem7233177) (@lem7233124 h1)). Qed.
Lemma lem7233179 (h1 : term477) : False.
Proof. exact (or_elim (@lem7233068 h1) (fun h0 : term472 => @lem7233123 h0) (fun h0 : term472 => @lem7233178 h0)). Qed.
Lemma lem7233181 (h1 : term477) : term477.
Proof. exact (h1). Qed.
Lemma lem7233182 (h1 : term477) : term477 = False.
Proof. exact (prop_ext (fun h2 : term477 => @lem7233179 h1) (fun h2 : False => @lem7233181 h1)). Qed.
Lemma lem7233183 (h1 : term477) : False.
Proof. exact (EQ_MP (@lem7233182 h1) (@lem7233181 h1)). Qed.
Lemma lem7233184 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) (h1 : term926 m g f n) : term926 m g f n.
Proof. exact (h1). Qed.
Lemma lem7233185 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) (h1 : term926 m g f n) : term477.
Proof. exact (EQ_MP (@lem7233058 m g f n) (@lem7233184 m g f n h1)). Qed.
Lemma lem7233186 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) (h1 : term926 m g f n) : term477 = False.
Proof. exact (prop_ext (fun h2 : term477 => @lem7233183 h2) (fun h2 : False => @lem7233185 m g f n h1)). Qed.
Lemma lem7233187 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) (h1 : term926 m g f n) : False.
Proof. exact (EQ_MP (@lem7233186 m g f n h1) (@lem7233185 m g f n h1)). Qed.
Lemma lem7233188 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : term1005 m g f n.
Proof. exact (fun h0 : term926 m g f n => @lem7233187 m g f n h0). Qed.
Lemma lem7233189 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : term1006 m g f n.
Proof. exact (@lem1386578 ((term839 m f g n) = (term846 m g f n))). Qed.
Lemma lem7233192 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term839 m f g n) = (term846 m g f n).
Proof. exact (@lem7233189 m g f n (@lem7233188 m g f n)). Qed.
Lemma lem7233193 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : (term782 m f g n) = (term338 m g f n).
Proof. exact (EQ_MP (@lem7231352 m g f n) (@lem7233192 m g f n)). Qed.
Lemma lem7233194 (g : nat -> real) (f : nat -> real) (n : nat) : (term757 f g n) = (term764 g f n).
Proof. exact (EQ_MP (@lem7231171 g f n) (@lem7232105 g f n)). Qed.
Lemma lem7233195 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term318 m f g n) = (term338 m g f n).
Proof. exact (EQ_MP (@lem7231054 g f m n h1) (@lem7233193 m g f n)). Qed.
Lemma lem7233196 (g : nat -> real) (f : nat -> real) (n : nat) : (term722 f g n) = (term723 g f n).
Proof. exact (EQ_MP (@lem7230934 g f n) (@lem7233194 g f n)). Qed.
Lemma lem7233197 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = ((term318 m f g n) = (term338 m g f n)).
Proof. exact (prop_ext (fun h2 : Peano.le m n => @lem7233195 g f m n h1) (fun h2 : (term318 m f g n) = (term338 m g f n) => @lem7230799 m n h1)). Qed.
Lemma lem7233198 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term318 m f g n) = (term338 m g f n).
Proof. exact (EQ_MP (@lem7233197 g f m n h1) (@lem7230799 m n h1)). Qed.
Lemma lem7233199 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : m = (S n)) : (term318 m f g n) = (term338 m g f n).
Proof. exact (EQ_MP (@lem7230812 g f m n h1) (@lem7233196 g f n)). Qed.
Lemma lem7233200 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : term164 m n) : (term318 m f g n) = (term338 m g f n).
Proof. exact (or_elim (@lem7230797 m n h1) (fun h0 : m = (S n) => @lem7233199 g f m n h0) (fun h0 : Peano.le m n => @lem7233198 g f m n h0)). Qed.
Lemma lem7233201 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : term1007 m g f n.
Proof. exact (fun h0 : term164 m n => @lem7233200 g f m n h0). Qed.
Lemma lem7233202 (g : nat -> real) (f : nat -> real) (m : nat) (n : nat) (h1 : term163 m n) : (term318 m f g n) = (term338 m g f n).
Proof. exact (@lem7233201 m g f n (@lem7230796 m n h1)). Qed.
Lemma lem7233207 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term246 m n) : (term188 m n f g) = term29.
Proof. exact (EQ_MP (@lem7227500 f g m n h1) (@lem0)). Qed.
Lemma lem7233208 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term246 m n) : (term246 m n) = ((term188 m n f g) = term29).
Proof. exact (prop_ext (fun h2 : term246 m n => @lem7233207 f g m n h1) (fun h2 : (term188 m n f g) = term29 => @lem7227261 m n h1)). Qed.
Lemma lem7233209 (f : nat -> real) (g : nat -> real) (m : nat) (n : nat) (h1 : term246 m n) : (term188 m n f g) = term29.
Proof. exact (EQ_MP (@lem7233208 f g m n h1) (@lem7227261 m n h1)). Qed.
Lemma lem7233210 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : term236 m n f g.
Proof. exact (fun h0 : term246 m n => @lem7233209 f g m n h0). Qed.
Lemma lem7233211 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : (term188 m n f g) = (term232 m n g f).
Proof. exact (EQ_MP (@lem7227667 m n g f h1 h2) (@lem7233202 g f m n h1)). Qed.
Lemma lem7233212 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : (term163 m n) = ((term188 m n f g) = (term232 m n g f)).
Proof. exact (prop_ext (fun h3 : term163 m n => @lem7233211 m n g f h1 h2) (fun h3 : (term188 m n f g) = (term232 m n g f) => @lem7227244 m n h1)). Qed.
Lemma lem7233213 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : term163 m n) (h2 : (term183 m n f g) = (term184 m n g f)) : (term188 m n f g) = (term232 m n g f).
Proof. exact (EQ_MP (@lem7233212 m n g f h1 h2) (@lem7227244 m n h1)). Qed.
Lemma lem7233214 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : (term183 m n f g) = (term184 m n g f)) : term240 m n g f.
Proof. exact (fun h0 : term163 m n => @lem7233213 m n g f h0 h1). Qed.
Lemma lem7233215 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : (term183 m n f g) = (term184 m n g f)) : term243 m n f g.
Proof. exact (conj (@lem7233214 m n g f h1) (@lem7233210 m n f g)). Qed.
Lemma lem7233216 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) (h1 : (term183 m n f g) = (term184 m n g f)) : (term188 m n f g) = (term189 m n g f).
Proof. exact (EQ_MP (@lem7227243 m n g f) (@lem7233215 m n g f h1)). Qed.
Lemma lem7233217 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term226 m) : (term178 m f g) = term29.
Proof. exact (EQ_MP (@lem7227388 f g m h1) (@lem0)). Qed.
Lemma lem7233218 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term226 m) : (term226 m) = ((term178 m f g) = term29).
Proof. exact (prop_ext (fun h2 : term226 m => @lem7233217 f g m h1) (fun h2 : (term178 m f g) = term29 => @lem7227209 m h1)). Qed.
Lemma lem7233219 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term226 m) : (term178 m f g) = term29.
Proof. exact (EQ_MP (@lem7233218 f g m h1) (@lem7227209 m h1)). Qed.
Lemma lem7233220 (m : nat) (f : nat -> real) (g : nat -> real) : term216 m f g.
Proof. exact (fun h0 : term226 m => @lem7233219 f g m h0). Qed.
Lemma lem7233221 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term212 m) : (term178 m f g) = (term211 m g f).
Proof. exact (EQ_MP (@lem7227578 m g f) (@lem7230793 g f m h1)). Qed.
Lemma lem7233222 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term212 m) : (term212 m) = ((term178 m f g) = (term211 m g f)).
Proof. exact (prop_ext (fun h2 : term212 m => @lem7233221 g f m h1) (fun h2 : (term178 m f g) = (term211 m g f) => @lem7227192 m h1)). Qed.
Lemma lem7233223 (g : nat -> real) (f : nat -> real) (m : nat) (h1 : term212 m) : (term178 m f g) = (term211 m g f).
Proof. exact (EQ_MP (@lem7233222 g f m h1) (@lem7227192 m h1)). Qed.
Lemma lem7233224 (m : nat) (g : nat -> real) (f : nat -> real) : term220 m g f.
Proof. exact (fun h0 : term212 m => @lem7233223 g f m h0). Qed.
Lemma lem7233225 (m : nat) (f : nat -> real) (g : nat -> real) : term223 m f g.
Proof. exact (conj (@lem7233224 m g f) (@lem7233220 m f g)). Qed.
Lemma lem7233226 (m : nat) (g : nat -> real) (f : nat -> real) : (term178 m f g) = (term179 m g f).
Proof. exact (EQ_MP (@lem7227191 m g f) (@lem7233225 m f g)). Qed.
Lemma lem7233227 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : term191 m n g f.
Proof. exact (fun h0 : (term183 m n f g) = (term184 m n g f) => @lem7233216 m n g f h0). Qed.
Lemma lem7233232 (m : nat) (g : nat -> real) (f : nat -> real) : term195 m g f.
Proof. exact (fun n : nat => @lem7233227 m n g f). Qed.
Lemma lem7233233 (m : nat) (g : nat -> real) (f : nat -> real) : term197 m g f.
Proof. exact (conj (@lem7233226 m g f) (@lem7233232 m g f)). Qed.
Lemma lem7233234 (m : nat) (g : nat -> real) (f : nat -> real) : term202 m g f.
Proof. exact (@lem7227172 m g f (@lem7233233 m g f)). Qed.
Lemma lem7233239 (g : nat -> real) (f : nat -> real) : term1008 g f.
Proof. exact (fun m : nat => @lem7233234 m g f). Qed.
Lemma lem7233244 (f : nat -> real) : term1009 f.
Proof. exact (fun g : nat -> real => @lem7233239 g f). Qed.
Lemma lem7233249 : term1010.
Proof. exact (fun f : nat -> real => @lem7233244 f). Qed.
