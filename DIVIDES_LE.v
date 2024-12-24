Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_POS_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import MULT_EQ_0_spec.
Require Import divides_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032072_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Require Import thm16474_spec.
Require Import thm16496_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem3074636 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = (term2 m n).
Proof. exact (@lem17500 (term0 m n) (term1 m n)). Qed.
Lemma lem3074643 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem3074650 (m : nat) : (term3 m) = m.
Proof. exact (@lem1032072 m). Qed.
Lemma lem3074651 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem3074652 (m : nat) : (term4 m) = (Peano.le m).
Proof. exact (MK_COMB (@lem3074651) (@lem3074650 m)). Qed.
Lemma lem3074653 (m : nat) (n : nat) : (term1 m n) = (term0 m n).
Proof. exact (MK_COMB (@lem3074652 m) (@lem3074643 m n)). Qed.
Lemma lem3074654 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3074655 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (MK_COMB (@lem3074654) (@lem3074653 m n)). Qed.
Lemma lem3074670 (m : nat) (n : nat) : (term7 m n) = (term7 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem3074671 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem3074670 m n) (@lem3074655 m n)). Qed.
Lemma lem3074678 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem3074685 (m : nat) : (term3 m) = m.
Proof. exact (@lem1032072 m). Qed.
Lemma lem3074686 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem3074687 (m : nat) : (term4 m) = (Peano.le m).
Proof. exact (MK_COMB (@lem3074686) (@lem3074685 m)). Qed.
Lemma lem3074688 (m : nat) (n : nat) : (term1 m n) = (term0 m n).
Proof. exact (MK_COMB (@lem3074687 m) (@lem3074678 m n)). Qed.
Lemma lem3074701 (m : nat) (n : nat) : (term10 m n) = (term10 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem3074702 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem3074701 m n) (@lem3074688 m n)). Qed.
Lemma lem3074703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3074704 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem3074703) (@lem3074702 m n)). Qed.
Lemma lem3074705 (m : nat) (n : nat) : (term2 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem3074704 m n) (@lem3074671 m n)). Qed.
Lemma lem3074708 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = (term15 m n).
Proof. exact (TRANS (@lem3074636 m n) (@lem3074705 m n)). Qed.
Lemma lem3074710 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3074711 (m : nat) (n : nat) : (term0 m n) = (term17 m n).
Proof. exact (@lem3074710 m (Nat.mul m n)). Qed.
Lemma lem3074712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3074713 (m : nat) (n : nat) : (term10 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem3074712) (@lem3074711 m n)). Qed.
Lemma lem3074715 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3074716 (m : nat) (n : nat) : (term0 m n) = (term17 m n).
Proof. exact (@lem3074715 m (Nat.mul m n)). Qed.
Lemma lem3074717 (m : nat) (n : nat) : (term12 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem3074713 m n) (@lem3074716 m n)). Qed.
Lemma lem3074718 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3074719 (m : nat) (n : nat) : (term14 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem3074718) (@lem3074717 m n)). Qed.
Lemma lem3074721 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3074722 (m : nat) (n : nat) : (term0 m n) = (term17 m n).
Proof. exact (@lem3074721 m (Nat.mul m n)). Qed.
Lemma lem3074723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3074724 (m : nat) (n : nat) : (term6 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem3074723) (@lem3074722 m n)). Qed.
Lemma lem3074725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3074726 (m : nat) (n : nat) : (term7 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem3074725) (@lem3074724 m n)). Qed.
Lemma lem3074728 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3074729 (m : nat) (n : nat) : (term0 m n) = (term17 m n).
Proof. exact (@lem3074728 m (Nat.mul m n)). Qed.
Lemma lem3074730 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3074731 (m : nat) (n : nat) : (term6 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem3074730) (@lem3074729 m n)). Qed.
Lemma lem3074732 (m : nat) (n : nat) : (term9 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem3074726 m n) (@lem3074731 m n)). Qed.
Lemma lem3074733 (m : nat) (n : nat) : (term15 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem3074719 m n) (@lem3074732 m n)). Qed.
Lemma lem3074734 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = (term24 m n).
Proof. exact (TRANS (@lem3074708 m n) (@lem3074733 m n)). Qed.
Lemma lem3074735 (m : nat) : term25 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem3074736 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem3074737 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem3074736 m) (@lem3074735 m)). Qed.
Lemma lem3074738 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem2307535 (Nat.mul m n)). Qed.
Lemma lem3074739 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem3074740 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem3074739 m n) (@lem3074738 m n)). Qed.
Lemma lem3074741 (_32032 : int) (_32033 : int) : (term29 _32032 _32033) = (term30 _32032 _32033).
Proof. exact (@lem2318604 (term30 _32032 _32033)). Qed.
Lemma lem3074750 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem16496 t)). Qed.
Lemma lem3074751 (_32032 : int) (_32033 : int) : (term31 _32032 _32033) = (int_le _32032 _32033).
Proof. exact (@lem3074750 (int_le _32032 _32033)). Qed.
Lemma lem3074752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3074753 (_32032 : int) (_32033 : int) : (term32 _32032 _32033) = (term33 _32032 _32033).
Proof. exact (MK_COMB (@lem3074752) (@lem3074751 _32032 _32033)). Qed.
Lemma lem3074755 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem16496 t)). Qed.
Lemma lem3074756 (_32032 : int) (_32033 : int) : (term34 _32032 _32033) = (term35 _32032 _32033).
Proof. exact (@lem3074755 (term35 _32032 _32033)). Qed.
Lemma lem3074757 (_32032 : int) (_32033 : int) : (term36 _32032 _32033) = (term37 _32032 _32033).
Proof. exact (MK_COMB (@lem3074753 _32032 _32033) (@lem3074756 _32032 _32033)). Qed.
Lemma lem3074760 (_32033 : int) : (term38 _32033) = (term38 _32033).
Proof. exact (eq_refl (term38 _32033)). Qed.
Lemma lem3074761 (_32032 : int) (_32033 : int) : (term39 _32032 _32033) = (term40 _32032 _32033).
Proof. exact (MK_COMB (@lem3074760 _32033) (@lem3074757 _32032 _32033)). Qed.
Lemma lem3074764 (_32032 : int) : (term38 _32032) = (term38 _32032).
Proof. exact (eq_refl (term38 _32032)). Qed.
Lemma lem3074765 (_32032 : int) (_32033 : int) : (term30 _32032 _32033) = (term41 _32032 _32033).
Proof. exact (MK_COMB (@lem3074764 _32032) (@lem3074761 _32032 _32033)). Qed.
Lemma lem3074768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3074772 (_32032 : int) (_32033 : int) : (term42 _32032 _32033) = (term43 _32032 _32033).
Proof. exact (MK_COMB (@lem3074768) (@lem3074765 _32032 _32033)). Qed.
Lemma lem3074778 (_32032 : int) (_32033 : int) : (term44 _32032 _32033) = (int_le _32032 _32033).
Proof. exact (@lem16933 (int_le _32032 _32033)). Qed.
Lemma lem3074780 (_32032 : int) (_32033 : int) : (term45 _32032 _32033) = (term45 _32032 _32033).
Proof. exact (eq_refl (term45 _32032 _32033)). Qed.
Lemma lem3074781 (_32032 : int) (_32033 : int) : (term46 _32032 _32033) = (term47 _32032 _32033).
Proof. exact (MK_COMB (@lem3074780 _32032 _32033) (@lem3074778 _32032 _32033)). Qed.
Lemma lem3074782 (_32032 : int) (_32033 : int) : (term48 _32032 _32033) = (term46 _32032 _32033).
Proof. exact (@lem17160 (int_le _32032 _32033) (term35 _32032 _32033)). Qed.
Lemma lem3074783 (_32032 : int) (_32033 : int) : (term48 _32032 _32033) = (term47 _32032 _32033).
Proof. exact (TRANS (@lem3074782 _32032 _32033) (@lem3074781 _32032 _32033)). Qed.
Lemma lem3074785 (_32033 : int) : (term49 _32033) = (term49 _32033).
Proof. exact (eq_refl (term49 _32033)). Qed.
Lemma lem3074786 (_32032 : int) (_32033 : int) : (term50 _32032 _32033) = (term51 _32032 _32033).
Proof. exact (MK_COMB (@lem3074785 _32033) (@lem3074783 _32032 _32033)). Qed.
Lemma lem3074787 (_32032 : int) (_32033 : int) : (term52 _32032 _32033) = (term50 _32032 _32033).
Proof. exact (@lem17362 (term53 _32033) (term37 _32032 _32033)). Qed.
Lemma lem3074788 (_32032 : int) (_32033 : int) : (term52 _32032 _32033) = (term51 _32032 _32033).
Proof. exact (TRANS (@lem3074787 _32032 _32033) (@lem3074786 _32032 _32033)). Qed.
Lemma lem3074790 (_32032 : int) : (term49 _32032) = (term49 _32032).
Proof. exact (eq_refl (term49 _32032)). Qed.
Lemma lem3074791 (_32032 : int) (_32033 : int) : (term54 _32032 _32033) = (term55 _32032 _32033).
Proof. exact (MK_COMB (@lem3074790 _32032) (@lem3074788 _32032 _32033)). Qed.
Lemma lem3074792 (_32032 : int) (_32033 : int) : (term43 _32032 _32033) = (term54 _32032 _32033).
Proof. exact (@lem17362 (term53 _32032) (term40 _32032 _32033)). Qed.
Lemma lem3074793 (_32032 : int) (_32033 : int) : (term43 _32032 _32033) = (term55 _32032 _32033).
Proof. exact (TRANS (@lem3074792 _32032 _32033) (@lem3074791 _32032 _32033)). Qed.
Lemma lem3074810 (_32032 : int) (_32033 : int) : (term42 _32032 _32033) = (term55 _32032 _32033).
Proof. exact (TRANS (@lem3074772 _32032 _32033) (@lem3074793 _32032 _32033)). Qed.
Lemma lem3074813 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3074814 (_32032 : int) : (term53 _32032) = (term57 _32032).
Proof. exact (@lem3074813 term58 _32032). Qed.
Lemma lem3074816 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3074817 : term60 = term61.
Proof. exact (@lem3074816 (NUMERAL 0)). Qed.
Lemma lem3074818 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3074819 : term62 = term63.
Proof. exact (MK_COMB (@lem3074818) (@lem3074817)). Qed.
Lemma lem3074820 (_32032 : int) : (real_of_int _32032) = (real_of_int _32032).
Proof. exact (eq_refl (real_of_int _32032)). Qed.
Lemma lem3074821 (_32032 : int) : (term57 _32032) = (term64 _32032).
Proof. exact (MK_COMB (@lem3074819) (@lem3074820 _32032)). Qed.
Lemma lem3074823 (_32032 : int) : (term53 _32032) = (term64 _32032).
Proof. exact (TRANS (@lem3074814 _32032) (@lem3074821 _32032)). Qed.
Lemma lem3074826 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3074827 (_32033 : int) : (term53 _32033) = (term57 _32033).
Proof. exact (@lem3074826 term58 _32033). Qed.
Lemma lem3074829 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3074830 : term60 = term61.
Proof. exact (@lem3074829 (NUMERAL 0)). Qed.
Lemma lem3074831 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3074832 : term62 = term63.
Proof. exact (MK_COMB (@lem3074831) (@lem3074830)). Qed.
Lemma lem3074833 (_32033 : int) : (real_of_int _32033) = (real_of_int _32033).
Proof. exact (eq_refl (real_of_int _32033)). Qed.
Lemma lem3074834 (_32033 : int) : (term57 _32033) = (term64 _32033).
Proof. exact (MK_COMB (@lem3074832) (@lem3074833 _32033)). Qed.
Lemma lem3074836 (_32033 : int) : (term53 _32033) = (term64 _32033).
Proof. exact (TRANS (@lem3074827 _32033) (@lem3074834 _32033)). Qed.
Lemma lem3074838 (y : int) (x : int) : (term35 x y) = (term65 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem3074839 (_32033 : int) (_32032 : int) : (term35 _32032 _32033) = (term65 _32033 _32032).
Proof. exact (@lem3074838 _32033 _32032). Qed.
Lemma lem3074841 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3074842 (_32033 : int) (_32032 : int) : (term65 _32033 _32032) = (term66 _32033 _32032).
Proof. exact (@lem3074841 (term67 _32033) _32032). Qed.
Lemma lem3074844 (x : int) (y : int) : (term68 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3074845 (_32033 : int) : (term70 _32033) = (term71 _32033).
Proof. exact (@lem3074844 _32033 term72). Qed.
Lemma lem3074847 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3074848 : term73 = term74.
Proof. exact (@lem3074847 term75). Qed.
Lemma lem3074849 (_32033 : int) : (term76 _32033) = (term76 _32033).
Proof. exact (eq_refl (term76 _32033)). Qed.
Lemma lem3074850 (_32033 : int) : (term71 _32033) = (term77 _32033).
Proof. exact (MK_COMB (@lem3074849 _32033) (@lem3074848)). Qed.
Lemma lem3074851 (_32033 : int) : (term70 _32033) = (term77 _32033).
Proof. exact (TRANS (@lem3074845 _32033) (@lem3074850 _32033)). Qed.
Lemma lem3074852 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3074853 (_32033 : int) : (term78 _32033) = (term79 _32033).
Proof. exact (MK_COMB (@lem3074852) (@lem3074851 _32033)). Qed.
Lemma lem3074854 (_32032 : int) : (real_of_int _32032) = (real_of_int _32032).
Proof. exact (eq_refl (real_of_int _32032)). Qed.
Lemma lem3074855 (_32033 : int) (_32032 : int) : (term66 _32033 _32032) = (term80 _32033 _32032).
Proof. exact (MK_COMB (@lem3074853 _32033) (@lem3074854 _32032)). Qed.
Lemma lem3074856 (_32033 : int) (_32032 : int) : (term65 _32033 _32032) = (term80 _32033 _32032).
Proof. exact (TRANS (@lem3074842 _32033 _32032) (@lem3074855 _32033 _32032)). Qed.
Lemma lem3074857 (_32033 : int) (_32032 : int) : (term35 _32032 _32033) = (term80 _32033 _32032).
Proof. exact (TRANS (@lem3074839 _32033 _32032) (@lem3074856 _32033 _32032)). Qed.
Lemma lem3074860 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3074862 (_32032 : int) (_32033 : int) : (int_le _32032 _32033) = (term56 _32032 _32033).
Proof. exact (@lem3074860 _32032 _32033). Qed.
Lemma lem3074863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3074864 (_32033 : int) (_32032 : int) : (term45 _32032 _32033) = (term81 _32033 _32032).
Proof. exact (MK_COMB (@lem3074863) (@lem3074857 _32033 _32032)). Qed.
Lemma lem3074865 (_32032 : int) (_32033 : int) : (term47 _32032 _32033) = (term82 _32032 _32033).
Proof. exact (MK_COMB (@lem3074864 _32033 _32032) (@lem3074862 _32032 _32033)). Qed.
Lemma lem3074866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3074867 (_32033 : int) : (term49 _32033) = (term83 _32033).
Proof. exact (MK_COMB (@lem3074866) (@lem3074836 _32033)). Qed.
Lemma lem3074868 (_32032 : int) (_32033 : int) : (term51 _32032 _32033) = (term84 _32032 _32033).
Proof. exact (MK_COMB (@lem3074867 _32033) (@lem3074865 _32032 _32033)). Qed.
Lemma lem3074869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3074870 (_32032 : int) : (term49 _32032) = (term83 _32032).
Proof. exact (MK_COMB (@lem3074869) (@lem3074823 _32032)). Qed.
Lemma lem3074871 (_32032 : int) (_32033 : int) : (term55 _32032 _32033) = (term85 _32032 _32033).
Proof. exact (MK_COMB (@lem3074870 _32032) (@lem3074868 _32032 _32033)). Qed.
Lemma lem3074872 (_32032 : int) (_32033 : int) : (term42 _32032 _32033) = (term85 _32032 _32033).
Proof. exact (TRANS (@lem3074810 _32032 _32033) (@lem3074871 _32032 _32033)). Qed.
Lemma lem3074876 (t : Prop) : (term86 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3074912 (_32032 : int) (_32033 : int) : (term87 _32032 _32033) = (term85 _32032 _32033).
Proof. exact (@lem3074876 (term85 _32032 _32033)). Qed.
Lemma lem3074913 (_32032 : int) : (term64 _32032) = (term88 _32032).
Proof. exact (@lem1988287 (real_of_int _32032) term61). Qed.
Lemma lem3074919 (_32032 : int) : (term89 _32032) = (term90 _32032).
Proof. exact (@lem1982792 (real_of_int _32032) term61). Qed.
Lemma lem3074921 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3074922 : term61 = term92.
Proof. exact (@lem3074921 (NUMERAL 0)). Qed.
Lemma lem3074924 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3074925 : term95 = term96.
Proof. exact (@lem3074924 term75). Qed.
Lemma lem3074926 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3074927 : term97 = term98.
Proof. exact (MK_COMB (@lem3074926) (@lem3074925)). Qed.
Lemma lem3074928 : term99 = term100.
Proof. exact (MK_COMB (@lem3074927) (@lem3074922)). Qed.
Lemma lem3074929 : term100 = term101.
Proof. exact (@lem1981613 term95 term61 term74 term74). Qed.
Lemma lem3074931 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3074932 : term104 = term105.
Proof. exact (@lem3074931 term75 term75). Qed.
Lemma lem3074933 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3074934 : term107 = term75.
Proof. exact (EQ_MP (@lem3074933) (@lem940073)). Qed.
Lemma lem3074935 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3074936 : term105 = term74.
Proof. exact (MK_COMB (@lem3074935) (@lem3074934)). Qed.
Lemma lem3074937 : term104 = term74.
Proof. exact (TRANS (@lem3074932) (@lem3074936)). Qed.
Lemma lem3074939 (x : nat) : (term108 x) = term61.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3074940 : term99 = term61.
Proof. exact (@lem3074939 term75). Qed.
Lemma lem3074941 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3074942 : term109 = term110.
Proof. exact (MK_COMB (@lem3074941) (@lem3074940)). Qed.
Lemma lem3074943 : term101 = term92.
Proof. exact (MK_COMB (@lem3074942) (@lem3074937)). Qed.
Lemma lem3074944 : term100 = term92.
Proof. exact (TRANS (@lem3074929) (@lem3074943)). Qed.
Lemma lem3074945 : term99 = term92.
Proof. exact (TRANS (@lem3074928) (@lem3074944)). Qed.
Lemma lem3074947 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3074948 : term92 = term61.
Proof. exact (@lem3074947 term61). Qed.
Lemma lem3074949 : term99 = term61.
Proof. exact (TRANS (@lem3074945) (@lem3074948)). Qed.
Lemma lem3074950 (_32032 : int) : (term76 _32032) = (term76 _32032).
Proof. exact (eq_refl (term76 _32032)). Qed.
Lemma lem3074951 (_32032 : int) : (term90 _32032) = (term112 _32032).
Proof. exact (MK_COMB (@lem3074950 _32032) (@lem3074949)). Qed.
Lemma lem3074952 (_32032 : int) : (term112 _32032) = (real_of_int _32032).
Proof. exact (@lem1982723 (real_of_int _32032)). Qed.
Lemma lem3074953 (_32032 : int) : (term90 _32032) = (real_of_int _32032).
Proof. exact (TRANS (@lem3074951 _32032) (@lem3074952 _32032)). Qed.
Lemma lem3074955 (_32032 : int) : (term89 _32032) = (real_of_int _32032).
Proof. exact (TRANS (@lem3074919 _32032) (@lem3074953 _32032)). Qed.
Lemma lem3074956 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3074957 (_32032 : int) : (term113 _32032) = (term114 _32032).
Proof. exact (MK_COMB (@lem3074956) (@lem3074955 _32032)). Qed.
Lemma lem3074958 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3074959 (_32032 : int) : (term88 _32032) = (term115 _32032).
Proof. exact (MK_COMB (@lem3074957 _32032) (@lem3074958)). Qed.
Lemma lem3074960 (_32032 : int) : (term64 _32032) = (term115 _32032).
Proof. exact (TRANS (@lem3074913 _32032) (@lem3074959 _32032)). Qed.
Lemma lem3074961 (_32033 : int) : (term64 _32033) = (term88 _32033).
Proof. exact (@lem1988287 (real_of_int _32033) term61). Qed.
Lemma lem3074967 (_32033 : int) : (term89 _32033) = (term90 _32033).
Proof. exact (@lem1982792 (real_of_int _32033) term61). Qed.
Lemma lem3074969 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3074970 : term61 = term92.
Proof. exact (@lem3074969 (NUMERAL 0)). Qed.
Lemma lem3074972 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3074973 : term95 = term96.
Proof. exact (@lem3074972 term75). Qed.
Lemma lem3074974 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3074975 : term97 = term98.
Proof. exact (MK_COMB (@lem3074974) (@lem3074973)). Qed.
Lemma lem3074976 : term99 = term100.
Proof. exact (MK_COMB (@lem3074975) (@lem3074970)). Qed.
Lemma lem3074977 : term100 = term101.
Proof. exact (@lem1981613 term95 term61 term74 term74). Qed.
Lemma lem3074979 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3074980 : term104 = term105.
Proof. exact (@lem3074979 term75 term75). Qed.
Lemma lem3074981 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3074982 : term107 = term75.
Proof. exact (EQ_MP (@lem3074981) (@lem940073)). Qed.
Lemma lem3074983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3074984 : term105 = term74.
Proof. exact (MK_COMB (@lem3074983) (@lem3074982)). Qed.
Lemma lem3074985 : term104 = term74.
Proof. exact (TRANS (@lem3074980) (@lem3074984)). Qed.
Lemma lem3074987 (x : nat) : (term108 x) = term61.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3074988 : term99 = term61.
Proof. exact (@lem3074987 term75). Qed.
Lemma lem3074989 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3074990 : term109 = term110.
Proof. exact (MK_COMB (@lem3074989) (@lem3074988)). Qed.
Lemma lem3074991 : term101 = term92.
Proof. exact (MK_COMB (@lem3074990) (@lem3074985)). Qed.
Lemma lem3074992 : term100 = term92.
Proof. exact (TRANS (@lem3074977) (@lem3074991)). Qed.
Lemma lem3074993 : term99 = term92.
Proof. exact (TRANS (@lem3074976) (@lem3074992)). Qed.
Lemma lem3074995 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3074996 : term92 = term61.
Proof. exact (@lem3074995 term61). Qed.
Lemma lem3074997 : term99 = term61.
Proof. exact (TRANS (@lem3074993) (@lem3074996)). Qed.
Lemma lem3074998 (_32033 : int) : (term76 _32033) = (term76 _32033).
Proof. exact (eq_refl (term76 _32033)). Qed.
Lemma lem3074999 (_32033 : int) : (term90 _32033) = (term112 _32033).
Proof. exact (MK_COMB (@lem3074998 _32033) (@lem3074997)). Qed.
Lemma lem3075000 (_32033 : int) : (term112 _32033) = (real_of_int _32033).
Proof. exact (@lem1982723 (real_of_int _32033)). Qed.
Lemma lem3075001 (_32033 : int) : (term90 _32033) = (real_of_int _32033).
Proof. exact (TRANS (@lem3074999 _32033) (@lem3075000 _32033)). Qed.
Lemma lem3075003 (_32033 : int) : (term89 _32033) = (real_of_int _32033).
Proof. exact (TRANS (@lem3074967 _32033) (@lem3075001 _32033)). Qed.
Lemma lem3075004 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3075005 (_32033 : int) : (term113 _32033) = (term114 _32033).
Proof. exact (MK_COMB (@lem3075004) (@lem3075003 _32033)). Qed.
Lemma lem3075006 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3075007 (_32033 : int) : (term88 _32033) = (term115 _32033).
Proof. exact (MK_COMB (@lem3075005 _32033) (@lem3075006)). Qed.
Lemma lem3075008 (_32033 : int) : (term64 _32033) = (term115 _32033).
Proof. exact (TRANS (@lem3074961 _32033) (@lem3075007 _32033)). Qed.
Lemma lem3075009 (_32032 : int) (_32033 : int) : (term80 _32033 _32032) = (term116 _32032 _32033).
Proof. exact (@lem1988287 (real_of_int _32032) (term77 _32033)). Qed.
Lemma lem3075021 (_32032 : int) (_32033 : int) : (term117 _32032 _32033) = (term118 _32032 _32033).
Proof. exact (@lem1982792 (real_of_int _32032) (term77 _32033)). Qed.
Lemma lem3075022 (_32033 : int) : (term119 _32033) = (term120 _32033).
Proof. exact (@lem1982781 (real_of_int _32033) term95 term74). Qed.
Lemma lem3075024 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3075025 : term74 = term121.
Proof. exact (@lem3075024 term75). Qed.
Lemma lem3075027 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3075028 : term95 = term96.
Proof. exact (@lem3075027 term75). Qed.
Lemma lem3075029 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3075030 : term97 = term98.
Proof. exact (MK_COMB (@lem3075029) (@lem3075028)). Qed.
Lemma lem3075031 : term122 = term123.
Proof. exact (MK_COMB (@lem3075030) (@lem3075025)). Qed.
Lemma lem3075032 : term123 = term124.
Proof. exact (@lem1981613 term95 term74 term74 term74). Qed.
Lemma lem3075034 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3075035 : term104 = term105.
Proof. exact (@lem3075034 term75 term75). Qed.
Lemma lem3075036 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075037 : term107 = term75.
Proof. exact (EQ_MP (@lem3075036) (@lem940073)). Qed.
Lemma lem3075038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075039 : term105 = term74.
Proof. exact (MK_COMB (@lem3075038) (@lem3075037)). Qed.
Lemma lem3075040 : term104 = term74.
Proof. exact (TRANS (@lem3075035) (@lem3075039)). Qed.
Lemma lem3075042 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3075043 : term122 = term127.
Proof. exact (@lem3075042 term75 term75). Qed.
Lemma lem3075044 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075045 : term107 = term75.
Proof. exact (EQ_MP (@lem3075044) (@lem940073)). Qed.
Lemma lem3075046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075047 : term105 = term74.
Proof. exact (MK_COMB (@lem3075046) (@lem3075045)). Qed.
Lemma lem3075048 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3075049 : term127 = term95.
Proof. exact (MK_COMB (@lem3075048) (@lem3075047)). Qed.
Lemma lem3075050 : term122 = term95.
Proof. exact (TRANS (@lem3075043) (@lem3075049)). Qed.
Lemma lem3075051 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3075052 : term128 = term129.
Proof. exact (MK_COMB (@lem3075051) (@lem3075050)). Qed.
Lemma lem3075053 : term124 = term96.
Proof. exact (MK_COMB (@lem3075052) (@lem3075040)). Qed.
Lemma lem3075054 : term123 = term96.
Proof. exact (TRANS (@lem3075032) (@lem3075053)). Qed.
Lemma lem3075055 : term122 = term96.
Proof. exact (TRANS (@lem3075031) (@lem3075054)). Qed.
Lemma lem3075057 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3075058 : term96 = term95.
Proof. exact (@lem3075057 term95). Qed.
Lemma lem3075059 : term122 = term95.
Proof. exact (TRANS (@lem3075055) (@lem3075058)). Qed.
Lemma lem3075062 (_32033 : int) : (term130 _32033) = (term130 _32033).
Proof. exact (eq_refl (term130 _32033)). Qed.
Lemma lem3075063 (_32033 : int) : (term120 _32033) = (term131 _32033).
Proof. exact (MK_COMB (@lem3075062 _32033) (@lem3075059)). Qed.
Lemma lem3075064 (_32033 : int) : (term119 _32033) = (term131 _32033).
Proof. exact (TRANS (@lem3075022 _32033) (@lem3075063 _32033)). Qed.
Lemma lem3075065 (_32032 : int) : (term76 _32032) = (term76 _32032).
Proof. exact (eq_refl (term76 _32032)). Qed.
Lemma lem3075068 (_32032 : int) (_32033 : int) : (term118 _32032 _32033) = (term132 _32032 _32033).
Proof. exact (MK_COMB (@lem3075065 _32032) (@lem3075064 _32033)). Qed.
Lemma lem3075070 (_32032 : int) (_32033 : int) : (term117 _32032 _32033) = (term132 _32032 _32033).
Proof. exact (TRANS (@lem3075021 _32032 _32033) (@lem3075068 _32032 _32033)). Qed.
Lemma lem3075071 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3075072 (_32032 : int) (_32033 : int) : (term133 _32032 _32033) = (term134 _32032 _32033).
Proof. exact (MK_COMB (@lem3075071) (@lem3075070 _32032 _32033)). Qed.
Lemma lem3075073 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3075074 (_32032 : int) (_32033 : int) : (term116 _32032 _32033) = (term135 _32032 _32033).
Proof. exact (MK_COMB (@lem3075072 _32032 _32033) (@lem3075073)). Qed.
Lemma lem3075075 (_32032 : int) (_32033 : int) : (term80 _32033 _32032) = (term135 _32032 _32033).
Proof. exact (TRANS (@lem3075009 _32032 _32033) (@lem3075074 _32032 _32033)). Qed.
Lemma lem3075076 (_32033 : int) (_32032 : int) : (term56 _32032 _32033) = (term136 _32033 _32032).
Proof. exact (@lem1988287 (real_of_int _32033) (real_of_int _32032)). Qed.
Lemma lem3075082 (_32033 : int) (_32032 : int) : (term137 _32033 _32032) = (term138 _32033 _32032).
Proof. exact (@lem1982792 (real_of_int _32033) (real_of_int _32032)). Qed.
Lemma lem3075087 (_32032 : int) (_32033 : int) : (term138 _32033 _32032) = (term139 _32032 _32033).
Proof. exact (@lem1982761 (term140 _32032) (real_of_int _32033)). Qed.
Lemma lem3075089 (_32032 : int) (_32033 : int) : (term137 _32033 _32032) = (term139 _32032 _32033).
Proof. exact (TRANS (@lem3075082 _32033 _32032) (@lem3075087 _32032 _32033)). Qed.
Lemma lem3075090 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3075091 (_32032 : int) (_32033 : int) : (term141 _32033 _32032) = (term142 _32032 _32033).
Proof. exact (MK_COMB (@lem3075090) (@lem3075089 _32032 _32033)). Qed.
Lemma lem3075092 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3075093 (_32032 : int) (_32033 : int) : (term136 _32033 _32032) = (term143 _32032 _32033).
Proof. exact (MK_COMB (@lem3075091 _32032 _32033) (@lem3075092)). Qed.
Lemma lem3075094 (_32032 : int) (_32033 : int) : (term56 _32032 _32033) = (term143 _32032 _32033).
Proof. exact (TRANS (@lem3075076 _32033 _32032) (@lem3075093 _32032 _32033)). Qed.
Lemma lem3075095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3075096 (_32032 : int) (_32033 : int) : (term81 _32033 _32032) = (term144 _32032 _32033).
Proof. exact (MK_COMB (@lem3075095) (@lem3075075 _32032 _32033)). Qed.
Lemma lem3075097 (_32032 : int) (_32033 : int) : (term82 _32032 _32033) = (term145 _32032 _32033).
Proof. exact (MK_COMB (@lem3075096 _32032 _32033) (@lem3075094 _32032 _32033)). Qed.
Lemma lem3075098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3075099 (_32033 : int) : (term83 _32033) = (term146 _32033).
Proof. exact (MK_COMB (@lem3075098) (@lem3075008 _32033)). Qed.
Lemma lem3075100 (_32032 : int) (_32033 : int) : (term84 _32032 _32033) = (term147 _32032 _32033).
Proof. exact (MK_COMB (@lem3075099 _32033) (@lem3075097 _32032 _32033)). Qed.
Lemma lem3075101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3075102 (_32032 : int) : (term83 _32032) = (term146 _32032).
Proof. exact (MK_COMB (@lem3075101) (@lem3074960 _32032)). Qed.
Lemma lem3075103 (_32032 : int) (_32033 : int) : (term85 _32032 _32033) = (term148 _32032 _32033).
Proof. exact (MK_COMB (@lem3075102 _32032) (@lem3075100 _32032 _32033)). Qed.
Lemma lem3075130 (_32032 : int) (_32033 : int) : (term87 _32032 _32033) = (term148 _32032 _32033).
Proof. exact (TRANS (@lem3074912 _32032 _32033) (@lem3075103 _32032 _32033)). Qed.
Lemma lem3075134 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term148 _32032 _32033.
Proof. exact (h1). Qed.
Lemma lem3075135 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term147 _32032 _32033.
Proof. exact (proj2 (@lem3075134 _32032 _32033 h1)). Qed.
Lemma lem3075137 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term145 _32032 _32033.
Proof. exact (proj2 (@lem3075135 _32032 _32033 h1)). Qed.
Lemma lem3075139 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term143 _32032 _32033.
Proof. exact (proj2 (@lem3075137 _32032 _32033 h1)). Qed.
Lemma lem3075140 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term135 _32032 _32033.
Proof. exact (proj1 (@lem3075137 _32032 _32033 h1)). Qed.
Lemma lem3075142 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3075143 : term149 = term150.
Proof. exact (@lem3075142 term61 term74). Qed.
Lemma lem3075145 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3075146 : term74 = term121.
Proof. exact (@lem3075145 term75). Qed.
Lemma lem3075148 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3075149 : term61 = term92.
Proof. exact (@lem3075148 (NUMERAL 0)). Qed.
Lemma lem3075150 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3075151 : term151 = term152.
Proof. exact (MK_COMB (@lem3075150) (@lem3075149)). Qed.
Lemma lem3075152 : term150 = term153.
Proof. exact (MK_COMB (@lem3075151) (@lem3075146)). Qed.
Lemma lem3075153 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3075155 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075156 : term150 = term156.
Proof. exact (@lem3075155 (NUMERAL 0) term75). Qed.
Lemma lem3075157 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075158 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075159 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075158 h1) (fun h1 : term156 = True => @lem3075157)). Qed.
Lemma lem3075160 : term156 = True.
Proof. exact (EQ_MP (@lem3075159) (@lem3075157)). Qed.
Lemma lem3075161 : term150 = True.
Proof. exact (TRANS (@lem3075156) (@lem3075160)). Qed.
Lemma lem3075162 : True = term150.
Proof. exact (SYM (@lem3075161)). Qed.
Lemma lem3075163 : term150.
Proof. exact (EQ_MP (@lem3075162) (@lem0)). Qed.
Lemma lem3075164 : term158.
Proof. exact (@lem3075153 (@lem3075163)). Qed.
Lemma lem3075166 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075167 : term150 = term156.
Proof. exact (@lem3075166 (NUMERAL 0) term75). Qed.
Lemma lem3075168 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075169 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075170 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075169 h1) (fun h1 : term156 = True => @lem3075168)). Qed.
Lemma lem3075171 : term156 = True.
Proof. exact (EQ_MP (@lem3075170) (@lem3075168)). Qed.
Lemma lem3075172 : term150 = True.
Proof. exact (TRANS (@lem3075167) (@lem3075171)). Qed.
Lemma lem3075173 : True = term150.
Proof. exact (SYM (@lem3075172)). Qed.
Lemma lem3075174 : term150.
Proof. exact (EQ_MP (@lem3075173) (@lem0)). Qed.
Lemma lem3075175 : term153 = term159.
Proof. exact (@lem3075164 (@lem3075174)). Qed.
Lemma lem3075177 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3075178 : term104 = term105.
Proof. exact (@lem3075177 term75 term75). Qed.
Lemma lem3075179 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075180 : term107 = term75.
Proof. exact (EQ_MP (@lem3075179) (@lem940073)). Qed.
Lemma lem3075181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075182 : term105 = term74.
Proof. exact (MK_COMB (@lem3075181) (@lem3075180)). Qed.
Lemma lem3075183 : term104 = term74.
Proof. exact (TRANS (@lem3075178) (@lem3075182)). Qed.
Lemma lem3075185 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3075186 : term161 = term61.
Proof. exact (@lem3075185 term75). Qed.
Lemma lem3075187 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3075188 : term162 = term151.
Proof. exact (MK_COMB (@lem3075187) (@lem3075186)). Qed.
Lemma lem3075189 : term159 = term150.
Proof. exact (MK_COMB (@lem3075188) (@lem3075183)). Qed.
Lemma lem3075191 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075192 : term150 = term156.
Proof. exact (@lem3075191 (NUMERAL 0) term75). Qed.
Lemma lem3075193 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075194 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075195 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075194 h1) (fun h1 : term156 = True => @lem3075193)). Qed.
Lemma lem3075196 : term156 = True.
Proof. exact (EQ_MP (@lem3075195) (@lem3075193)). Qed.
Lemma lem3075197 : term150 = True.
Proof. exact (TRANS (@lem3075192) (@lem3075196)). Qed.
Lemma lem3075198 : term159 = True.
Proof. exact (TRANS (@lem3075189) (@lem3075197)). Qed.
Lemma lem3075199 : term153 = True.
Proof. exact (TRANS (@lem3075175) (@lem3075198)). Qed.
Lemma lem3075200 : term150 = True.
Proof. exact (TRANS (@lem3075152) (@lem3075199)). Qed.
Lemma lem3075201 : term149 = True.
Proof. exact (TRANS (@lem3075143) (@lem3075200)). Qed.
Lemma lem3075202 : True = term149.
Proof. exact (SYM (@lem3075201)). Qed.
Lemma lem3075203 : term149.
Proof. exact (EQ_MP (@lem3075202) (@lem0)). Qed.
Lemma lem3075204 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term163 _32032 _32033.
Proof. exact (conj (@lem3075203) (@lem3075140 _32032 _32033 h1)). Qed.
Lemma lem3075206 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3075207 (_32032 : int) (_32033 : int) : term165 _32032 _32033.
Proof. exact (@lem3075206 term74 (term132 _32032 _32033)). Qed.
Lemma lem3075208 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term166 _32032 _32033.
Proof. exact (@lem3075207 _32032 _32033 (@lem3075204 _32032 _32033 h1)). Qed.
Lemma lem3075209 (_32032 : int) (_32033 : int) : (term167 _32032 _32033) = (term132 _32032 _32033).
Proof. exact (@lem1982733 (term132 _32032 _32033)). Qed.
Lemma lem3075210 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3075211 (_32032 : int) (_32033 : int) : (term168 _32032 _32033) = (term134 _32032 _32033).
Proof. exact (MK_COMB (@lem3075210) (@lem3075209 _32032 _32033)). Qed.
Lemma lem3075212 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3075213 (_32032 : int) (_32033 : int) : (term166 _32032 _32033) = (term135 _32032 _32033).
Proof. exact (MK_COMB (@lem3075211 _32032 _32033) (@lem3075212)). Qed.
Lemma lem3075214 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term135 _32032 _32033.
Proof. exact (EQ_MP (@lem3075213 _32032 _32033) (@lem3075208 _32032 _32033 h1)). Qed.
Lemma lem3075216 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3075217 : term149 = term150.
Proof. exact (@lem3075216 term61 term74). Qed.
Lemma lem3075219 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3075220 : term74 = term121.
Proof. exact (@lem3075219 term75). Qed.
Lemma lem3075222 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3075223 : term61 = term92.
Proof. exact (@lem3075222 (NUMERAL 0)). Qed.
Lemma lem3075224 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3075225 : term151 = term152.
Proof. exact (MK_COMB (@lem3075224) (@lem3075223)). Qed.
Lemma lem3075226 : term150 = term153.
Proof. exact (MK_COMB (@lem3075225) (@lem3075220)). Qed.
Lemma lem3075227 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3075229 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075230 : term150 = term156.
Proof. exact (@lem3075229 (NUMERAL 0) term75). Qed.
Lemma lem3075231 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075232 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075233 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075232 h1) (fun h1 : term156 = True => @lem3075231)). Qed.
Lemma lem3075234 : term156 = True.
Proof. exact (EQ_MP (@lem3075233) (@lem3075231)). Qed.
Lemma lem3075235 : term150 = True.
Proof. exact (TRANS (@lem3075230) (@lem3075234)). Qed.
Lemma lem3075236 : True = term150.
Proof. exact (SYM (@lem3075235)). Qed.
Lemma lem3075237 : term150.
Proof. exact (EQ_MP (@lem3075236) (@lem0)). Qed.
Lemma lem3075238 : term158.
Proof. exact (@lem3075227 (@lem3075237)). Qed.
Lemma lem3075240 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075241 : term150 = term156.
Proof. exact (@lem3075240 (NUMERAL 0) term75). Qed.
Lemma lem3075242 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075243 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075244 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075243 h1) (fun h1 : term156 = True => @lem3075242)). Qed.
Lemma lem3075245 : term156 = True.
Proof. exact (EQ_MP (@lem3075244) (@lem3075242)). Qed.
Lemma lem3075246 : term150 = True.
Proof. exact (TRANS (@lem3075241) (@lem3075245)). Qed.
Lemma lem3075247 : True = term150.
Proof. exact (SYM (@lem3075246)). Qed.
Lemma lem3075248 : term150.
Proof. exact (EQ_MP (@lem3075247) (@lem0)). Qed.
Lemma lem3075249 : term153 = term159.
Proof. exact (@lem3075238 (@lem3075248)). Qed.
Lemma lem3075251 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3075252 : term104 = term105.
Proof. exact (@lem3075251 term75 term75). Qed.
Lemma lem3075253 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075254 : term107 = term75.
Proof. exact (EQ_MP (@lem3075253) (@lem940073)). Qed.
Lemma lem3075255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075256 : term105 = term74.
Proof. exact (MK_COMB (@lem3075255) (@lem3075254)). Qed.
Lemma lem3075257 : term104 = term74.
Proof. exact (TRANS (@lem3075252) (@lem3075256)). Qed.
Lemma lem3075259 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3075260 : term161 = term61.
Proof. exact (@lem3075259 term75). Qed.
Lemma lem3075261 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3075262 : term162 = term151.
Proof. exact (MK_COMB (@lem3075261) (@lem3075260)). Qed.
Lemma lem3075263 : term159 = term150.
Proof. exact (MK_COMB (@lem3075262) (@lem3075257)). Qed.
Lemma lem3075265 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075266 : term150 = term156.
Proof. exact (@lem3075265 (NUMERAL 0) term75). Qed.
Lemma lem3075267 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075268 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075269 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075268 h1) (fun h1 : term156 = True => @lem3075267)). Qed.
Lemma lem3075270 : term156 = True.
Proof. exact (EQ_MP (@lem3075269) (@lem3075267)). Qed.
Lemma lem3075271 : term150 = True.
Proof. exact (TRANS (@lem3075266) (@lem3075270)). Qed.
Lemma lem3075272 : term159 = True.
Proof. exact (TRANS (@lem3075263) (@lem3075271)). Qed.
Lemma lem3075273 : term153 = True.
Proof. exact (TRANS (@lem3075249) (@lem3075272)). Qed.
Lemma lem3075274 : term150 = True.
Proof. exact (TRANS (@lem3075226) (@lem3075273)). Qed.
Lemma lem3075275 : term149 = True.
Proof. exact (TRANS (@lem3075217) (@lem3075274)). Qed.
Lemma lem3075276 : True = term149.
Proof. exact (SYM (@lem3075275)). Qed.
Lemma lem3075277 : term149.
Proof. exact (EQ_MP (@lem3075276) (@lem0)). Qed.
Lemma lem3075278 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term169 _32032 _32033.
Proof. exact (conj (@lem3075277) (@lem3075139 _32032 _32033 h1)). Qed.
Lemma lem3075280 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3075281 (_32032 : int) (_32033 : int) : term170 _32032 _32033.
Proof. exact (@lem3075280 term74 (term139 _32032 _32033)). Qed.
Lemma lem3075282 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term171 _32032 _32033.
Proof. exact (@lem3075281 _32032 _32033 (@lem3075278 _32032 _32033 h1)). Qed.
Lemma lem3075283 (_32032 : int) (_32033 : int) : (term172 _32032 _32033) = (term139 _32032 _32033).
Proof. exact (@lem1982733 (term139 _32032 _32033)). Qed.
Lemma lem3075284 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3075285 (_32032 : int) (_32033 : int) : (term173 _32032 _32033) = (term142 _32032 _32033).
Proof. exact (MK_COMB (@lem3075284) (@lem3075283 _32032 _32033)). Qed.
Lemma lem3075286 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3075287 (_32032 : int) (_32033 : int) : (term171 _32032 _32033) = (term143 _32032 _32033).
Proof. exact (MK_COMB (@lem3075285 _32032 _32033) (@lem3075286)). Qed.
Lemma lem3075288 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term143 _32032 _32033.
Proof. exact (EQ_MP (@lem3075287 _32032 _32033) (@lem3075282 _32032 _32033 h1)). Qed.
Lemma lem3075289 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term174 _32032 _32033.
Proof. exact (conj (@lem3075288 _32032 _32033 h1) (@lem3075214 _32032 _32033 h1)). Qed.
Lemma lem3075291 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3075292 (_32032 : int) (_32033 : int) : term176 _32032 _32033.
Proof. exact (@lem3075291 (term139 _32032 _32033) (term132 _32032 _32033)). Qed.
Lemma lem3075293 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term177 _32032 _32033.
Proof. exact (@lem3075292 _32032 _32033 (@lem3075289 _32032 _32033 h1)). Qed.
Lemma lem3075294 (_32032 : int) (_32033 : int) : (term178 _32032 _32033) = (term179 _32032 _32033).
Proof. exact (@lem1982753 (term140 _32032) (real_of_int _32032) (real_of_int _32033) (term131 _32033)). Qed.
Lemma lem3075295 (_32032 : int) : (term180 _32032) = (term181 _32032).
Proof. exact (@lem1982713 term95 (real_of_int _32032)). Qed.
Lemma lem3075297 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3075298 : term74 = term121.
Proof. exact (@lem3075297 term75). Qed.
Lemma lem3075300 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3075301 : term95 = term96.
Proof. exact (@lem3075300 term75). Qed.
Lemma lem3075302 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3075303 : term182 = term183.
Proof. exact (MK_COMB (@lem3075302) (@lem3075301)). Qed.
Lemma lem3075304 : term184 = term185.
Proof. exact (MK_COMB (@lem3075303) (@lem3075298)). Qed.
Lemma lem3075305 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3075307 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075308 : term150 = term156.
Proof. exact (@lem3075307 (NUMERAL 0) term75). Qed.
Lemma lem3075309 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075310 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075311 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075310 h1) (fun h1 : term156 = True => @lem3075309)). Qed.
Lemma lem3075312 : term156 = True.
Proof. exact (EQ_MP (@lem3075311) (@lem3075309)). Qed.
Lemma lem3075313 : term150 = True.
Proof. exact (TRANS (@lem3075308) (@lem3075312)). Qed.
Lemma lem3075314 : True = term150.
Proof. exact (SYM (@lem3075313)). Qed.
Lemma lem3075315 : term150.
Proof. exact (EQ_MP (@lem3075314) (@lem0)). Qed.
Lemma lem3075316 : term187.
Proof. exact (@lem3075305 (@lem3075315)). Qed.
Lemma lem3075318 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075319 : term150 = term156.
Proof. exact (@lem3075318 (NUMERAL 0) term75). Qed.
Lemma lem3075320 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075321 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075322 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075321 h1) (fun h1 : term156 = True => @lem3075320)). Qed.
Lemma lem3075323 : term156 = True.
Proof. exact (EQ_MP (@lem3075322) (@lem3075320)). Qed.
Lemma lem3075324 : term150 = True.
Proof. exact (TRANS (@lem3075319) (@lem3075323)). Qed.
Lemma lem3075325 : True = term150.
Proof. exact (SYM (@lem3075324)). Qed.
Lemma lem3075326 : term150.
Proof. exact (EQ_MP (@lem3075325) (@lem0)). Qed.
Lemma lem3075327 : term188.
Proof. exact (@lem3075316 (@lem3075326)). Qed.
Lemma lem3075329 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075330 : term150 = term156.
Proof. exact (@lem3075329 (NUMERAL 0) term75). Qed.
Lemma lem3075331 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075332 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075333 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075332 h1) (fun h1 : term156 = True => @lem3075331)). Qed.
Lemma lem3075334 : term156 = True.
Proof. exact (EQ_MP (@lem3075333) (@lem3075331)). Qed.
Lemma lem3075335 : term150 = True.
Proof. exact (TRANS (@lem3075330) (@lem3075334)). Qed.
Lemma lem3075336 : True = term150.
Proof. exact (SYM (@lem3075335)). Qed.
Lemma lem3075337 : term150.
Proof. exact (EQ_MP (@lem3075336) (@lem0)). Qed.
Lemma lem3075338 : term189.
Proof. exact (@lem3075327 (@lem3075337)). Qed.
Lemma lem3075340 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3075341 : term104 = term105.
Proof. exact (@lem3075340 term75 term75). Qed.
Lemma lem3075342 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075343 : term107 = term75.
Proof. exact (EQ_MP (@lem3075342) (@lem940073)). Qed.
Lemma lem3075344 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075345 : term105 = term74.
Proof. exact (MK_COMB (@lem3075344) (@lem3075343)). Qed.
Lemma lem3075346 : term104 = term74.
Proof. exact (TRANS (@lem3075341) (@lem3075345)). Qed.
Lemma lem3075348 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3075349 : term122 = term127.
Proof. exact (@lem3075348 term75 term75). Qed.
Lemma lem3075350 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075351 : term107 = term75.
Proof. exact (EQ_MP (@lem3075350) (@lem940073)). Qed.
Lemma lem3075352 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075353 : term105 = term74.
Proof. exact (MK_COMB (@lem3075352) (@lem3075351)). Qed.
Lemma lem3075354 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3075355 : term127 = term95.
Proof. exact (MK_COMB (@lem3075354) (@lem3075353)). Qed.
Lemma lem3075356 : term122 = term95.
Proof. exact (TRANS (@lem3075349) (@lem3075355)). Qed.
Lemma lem3075357 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3075358 : term190 = term182.
Proof. exact (MK_COMB (@lem3075357) (@lem3075356)). Qed.
Lemma lem3075359 : term191 = term184.
Proof. exact (MK_COMB (@lem3075358) (@lem3075346)). Qed.
Lemma lem3075361 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3075362 : term184 = term61.
Proof. exact (@lem3075361 term75). Qed.
Lemma lem3075363 : term191 = term61.
Proof. exact (TRANS (@lem3075359) (@lem3075362)). Qed.
Lemma lem3075364 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3075365 : term193 = term194.
Proof. exact (MK_COMB (@lem3075364) (@lem3075363)). Qed.
Lemma lem3075366 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3075367 : term195 = term161.
Proof. exact (MK_COMB (@lem3075365) (@lem3075366)). Qed.
Lemma lem3075369 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3075370 : term161 = term61.
Proof. exact (@lem3075369 term75). Qed.
Lemma lem3075371 : term195 = term61.
Proof. exact (TRANS (@lem3075367) (@lem3075370)). Qed.
Lemma lem3075373 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3075374 : term104 = term105.
Proof. exact (@lem3075373 term75 term75). Qed.
Lemma lem3075375 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075376 : term107 = term75.
Proof. exact (EQ_MP (@lem3075375) (@lem940073)). Qed.
Lemma lem3075377 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075378 : term105 = term74.
Proof. exact (MK_COMB (@lem3075377) (@lem3075376)). Qed.
Lemma lem3075379 : term104 = term74.
Proof. exact (TRANS (@lem3075374) (@lem3075378)). Qed.
Lemma lem3075380 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3075381 : term196 = term161.
Proof. exact (MK_COMB (@lem3075380) (@lem3075379)). Qed.
Lemma lem3075383 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3075384 : term161 = term61.
Proof. exact (@lem3075383 term75). Qed.
Lemma lem3075385 : term196 = term61.
Proof. exact (TRANS (@lem3075381) (@lem3075384)). Qed.
Lemma lem3075386 : term61 = term196.
Proof. exact (SYM (@lem3075385)). Qed.
Lemma lem3075387 : term195 = term196.
Proof. exact (TRANS (@lem3075371) (@lem3075386)). Qed.
Lemma lem3075388 : term185 = term92.
Proof. exact (@lem3075338 (@lem3075387)). Qed.
Lemma lem3075389 : term184 = term92.
Proof. exact (TRANS (@lem3075304) (@lem3075388)). Qed.
Lemma lem3075391 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3075392 : term92 = term61.
Proof. exact (@lem3075391 term61). Qed.
Lemma lem3075393 : term184 = term61.
Proof. exact (TRANS (@lem3075389) (@lem3075392)). Qed.
Lemma lem3075394 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3075395 : term197 = term194.
Proof. exact (MK_COMB (@lem3075394) (@lem3075393)). Qed.
Lemma lem3075396 (_32032 : int) : (real_of_int _32032) = (real_of_int _32032).
Proof. exact (eq_refl (real_of_int _32032)). Qed.
Lemma lem3075397 (_32032 : int) : (term181 _32032) = (term198 _32032).
Proof. exact (MK_COMB (@lem3075395) (@lem3075396 _32032)). Qed.
Lemma lem3075398 (_32032 : int) : (term180 _32032) = (term198 _32032).
Proof. exact (TRANS (@lem3075295 _32032) (@lem3075397 _32032)). Qed.
Lemma lem3075399 (_32032 : int) : (term198 _32032) = term61.
Proof. exact (@lem1982719 (real_of_int _32032)). Qed.
Lemma lem3075400 (_32032 : int) : (term180 _32032) = term61.
Proof. exact (TRANS (@lem3075398 _32032) (@lem3075399 _32032)). Qed.
Lemma lem3075401 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3075402 (_32032 : int) : (term199 _32032) = term200.
Proof. exact (MK_COMB (@lem3075401) (@lem3075400 _32032)). Qed.
Lemma lem3075403 (_32033 : int) : (term201 _32033) = (term202 _32033).
Proof. exact (@lem1982763 (real_of_int _32033) (term140 _32033) term95). Qed.
Lemma lem3075404 (_32033 : int) : (term203 _32033) = (term181 _32033).
Proof. exact (@lem1982715 term95 (real_of_int _32033)). Qed.
Lemma lem3075406 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3075407 : term74 = term121.
Proof. exact (@lem3075406 term75). Qed.
Lemma lem3075409 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3075410 : term95 = term96.
Proof. exact (@lem3075409 term75). Qed.
Lemma lem3075411 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3075412 : term182 = term183.
Proof. exact (MK_COMB (@lem3075411) (@lem3075410)). Qed.
Lemma lem3075413 : term184 = term185.
Proof. exact (MK_COMB (@lem3075412) (@lem3075407)). Qed.
Lemma lem3075414 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3075416 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075417 : term150 = term156.
Proof. exact (@lem3075416 (NUMERAL 0) term75). Qed.
Lemma lem3075418 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075419 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075420 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075419 h1) (fun h1 : term156 = True => @lem3075418)). Qed.
Lemma lem3075421 : term156 = True.
Proof. exact (EQ_MP (@lem3075420) (@lem3075418)). Qed.
Lemma lem3075422 : term150 = True.
Proof. exact (TRANS (@lem3075417) (@lem3075421)). Qed.
Lemma lem3075423 : True = term150.
Proof. exact (SYM (@lem3075422)). Qed.
Lemma lem3075424 : term150.
Proof. exact (EQ_MP (@lem3075423) (@lem0)). Qed.
Lemma lem3075425 : term187.
Proof. exact (@lem3075414 (@lem3075424)). Qed.
Lemma lem3075427 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075428 : term150 = term156.
Proof. exact (@lem3075427 (NUMERAL 0) term75). Qed.
Lemma lem3075429 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075430 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075431 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075430 h1) (fun h1 : term156 = True => @lem3075429)). Qed.
Lemma lem3075432 : term156 = True.
Proof. exact (EQ_MP (@lem3075431) (@lem3075429)). Qed.
Lemma lem3075433 : term150 = True.
Proof. exact (TRANS (@lem3075428) (@lem3075432)). Qed.
Lemma lem3075434 : True = term150.
Proof. exact (SYM (@lem3075433)). Qed.
Lemma lem3075435 : term150.
Proof. exact (EQ_MP (@lem3075434) (@lem0)). Qed.
Lemma lem3075436 : term188.
Proof. exact (@lem3075425 (@lem3075435)). Qed.
Lemma lem3075438 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075439 : term150 = term156.
Proof. exact (@lem3075438 (NUMERAL 0) term75). Qed.
Lemma lem3075440 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075441 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075442 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075441 h1) (fun h1 : term156 = True => @lem3075440)). Qed.
Lemma lem3075443 : term156 = True.
Proof. exact (EQ_MP (@lem3075442) (@lem3075440)). Qed.
Lemma lem3075444 : term150 = True.
Proof. exact (TRANS (@lem3075439) (@lem3075443)). Qed.
Lemma lem3075445 : True = term150.
Proof. exact (SYM (@lem3075444)). Qed.
Lemma lem3075446 : term150.
Proof. exact (EQ_MP (@lem3075445) (@lem0)). Qed.
Lemma lem3075447 : term189.
Proof. exact (@lem3075436 (@lem3075446)). Qed.
Lemma lem3075449 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3075450 : term104 = term105.
Proof. exact (@lem3075449 term75 term75). Qed.
Lemma lem3075451 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075452 : term107 = term75.
Proof. exact (EQ_MP (@lem3075451) (@lem940073)). Qed.
Lemma lem3075453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075454 : term105 = term74.
Proof. exact (MK_COMB (@lem3075453) (@lem3075452)). Qed.
Lemma lem3075455 : term104 = term74.
Proof. exact (TRANS (@lem3075450) (@lem3075454)). Qed.
Lemma lem3075457 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3075458 : term122 = term127.
Proof. exact (@lem3075457 term75 term75). Qed.
Lemma lem3075459 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075460 : term107 = term75.
Proof. exact (EQ_MP (@lem3075459) (@lem940073)). Qed.
Lemma lem3075461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075462 : term105 = term74.
Proof. exact (MK_COMB (@lem3075461) (@lem3075460)). Qed.
Lemma lem3075463 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3075464 : term127 = term95.
Proof. exact (MK_COMB (@lem3075463) (@lem3075462)). Qed.
Lemma lem3075465 : term122 = term95.
Proof. exact (TRANS (@lem3075458) (@lem3075464)). Qed.
Lemma lem3075466 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3075467 : term190 = term182.
Proof. exact (MK_COMB (@lem3075466) (@lem3075465)). Qed.
Lemma lem3075468 : term191 = term184.
Proof. exact (MK_COMB (@lem3075467) (@lem3075455)). Qed.
Lemma lem3075470 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3075471 : term184 = term61.
Proof. exact (@lem3075470 term75). Qed.
Lemma lem3075472 : term191 = term61.
Proof. exact (TRANS (@lem3075468) (@lem3075471)). Qed.
Lemma lem3075473 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3075474 : term193 = term194.
Proof. exact (MK_COMB (@lem3075473) (@lem3075472)). Qed.
Lemma lem3075475 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3075476 : term195 = term161.
Proof. exact (MK_COMB (@lem3075474) (@lem3075475)). Qed.
Lemma lem3075478 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3075479 : term161 = term61.
Proof. exact (@lem3075478 term75). Qed.
Lemma lem3075480 : term195 = term61.
Proof. exact (TRANS (@lem3075476) (@lem3075479)). Qed.
Lemma lem3075482 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3075483 : term104 = term105.
Proof. exact (@lem3075482 term75 term75). Qed.
Lemma lem3075484 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075485 : term107 = term75.
Proof. exact (EQ_MP (@lem3075484) (@lem940073)). Qed.
Lemma lem3075486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075487 : term105 = term74.
Proof. exact (MK_COMB (@lem3075486) (@lem3075485)). Qed.
Lemma lem3075488 : term104 = term74.
Proof. exact (TRANS (@lem3075483) (@lem3075487)). Qed.
Lemma lem3075489 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3075490 : term196 = term161.
Proof. exact (MK_COMB (@lem3075489) (@lem3075488)). Qed.
Lemma lem3075492 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3075493 : term161 = term61.
Proof. exact (@lem3075492 term75). Qed.
Lemma lem3075494 : term196 = term61.
Proof. exact (TRANS (@lem3075490) (@lem3075493)). Qed.
Lemma lem3075495 : term61 = term196.
Proof. exact (SYM (@lem3075494)). Qed.
Lemma lem3075496 : term195 = term196.
Proof. exact (TRANS (@lem3075480) (@lem3075495)). Qed.
Lemma lem3075497 : term185 = term92.
Proof. exact (@lem3075447 (@lem3075496)). Qed.
Lemma lem3075498 : term184 = term92.
Proof. exact (TRANS (@lem3075413) (@lem3075497)). Qed.
Lemma lem3075500 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3075501 : term92 = term61.
Proof. exact (@lem3075500 term61). Qed.
Lemma lem3075502 : term184 = term61.
Proof. exact (TRANS (@lem3075498) (@lem3075501)). Qed.
Lemma lem3075503 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3075504 : term197 = term194.
Proof. exact (MK_COMB (@lem3075503) (@lem3075502)). Qed.
Lemma lem3075505 (_32033 : int) : (real_of_int _32033) = (real_of_int _32033).
Proof. exact (eq_refl (real_of_int _32033)). Qed.
Lemma lem3075506 (_32033 : int) : (term181 _32033) = (term198 _32033).
Proof. exact (MK_COMB (@lem3075504) (@lem3075505 _32033)). Qed.
Lemma lem3075507 (_32033 : int) : (term203 _32033) = (term198 _32033).
Proof. exact (TRANS (@lem3075404 _32033) (@lem3075506 _32033)). Qed.
Lemma lem3075508 (_32033 : int) : (term198 _32033) = term61.
Proof. exact (@lem1982719 (real_of_int _32033)). Qed.
Lemma lem3075509 (_32033 : int) : (term203 _32033) = term61.
Proof. exact (TRANS (@lem3075507 _32033) (@lem3075508 _32033)). Qed.
Lemma lem3075510 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3075511 (_32033 : int) : (term204 _32033) = term200.
Proof. exact (MK_COMB (@lem3075510) (@lem3075509 _32033)). Qed.
Lemma lem3075512 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3075513 (_32033 : int) : (term202 _32033) = term205.
Proof. exact (MK_COMB (@lem3075511 _32033) (@lem3075512)). Qed.
Lemma lem3075514 (_32033 : int) : (term201 _32033) = term205.
Proof. exact (TRANS (@lem3075403 _32033) (@lem3075513 _32033)). Qed.
Lemma lem3075515 : term205 = term95.
Proof. exact (@lem1982721 term95). Qed.
Lemma lem3075516 (_32033 : int) : (term201 _32033) = term95.
Proof. exact (TRANS (@lem3075514 _32033) (@lem3075515)). Qed.
Lemma lem3075517 (_32032 : int) (_32033 : int) : (term179 _32032 _32033) = term205.
Proof. exact (MK_COMB (@lem3075402 _32032) (@lem3075516 _32033)). Qed.
Lemma lem3075518 (_32032 : int) (_32033 : int) : (term178 _32032 _32033) = term205.
Proof. exact (TRANS (@lem3075294 _32032 _32033) (@lem3075517 _32032 _32033)). Qed.
Lemma lem3075519 : term205 = term95.
Proof. exact (@lem1982721 term95). Qed.
Lemma lem3075520 (_32032 : int) (_32033 : int) : (term178 _32032 _32033) = term95.
Proof. exact (TRANS (@lem3075518 _32032 _32033) (@lem3075519)). Qed.
Lemma lem3075521 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3075522 (_32032 : int) (_32033 : int) : (term206 _32032 _32033) = term207.
Proof. exact (MK_COMB (@lem3075521) (@lem3075520 _32032 _32033)). Qed.
Lemma lem3075523 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3075524 (_32032 : int) (_32033 : int) : (term177 _32032 _32033) = term208.
Proof. exact (MK_COMB (@lem3075522 _32032 _32033) (@lem3075523)). Qed.
Lemma lem3075525 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term208.
Proof. exact (EQ_MP (@lem3075524 _32032 _32033) (@lem3075293 _32032 _32033 h1)). Qed.
Lemma lem3075527 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3075528 : term208 = term209.
Proof. exact (@lem3075527 term61 term95). Qed.
Lemma lem3075530 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3075531 : term95 = term96.
Proof. exact (@lem3075530 term75). Qed.
Lemma lem3075533 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3075534 : term61 = term92.
Proof. exact (@lem3075533 (NUMERAL 0)). Qed.
Lemma lem3075535 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3075536 : term63 = term210.
Proof. exact (MK_COMB (@lem3075535) (@lem3075534)). Qed.
Lemma lem3075537 : term209 = term211.
Proof. exact (MK_COMB (@lem3075536) (@lem3075531)). Qed.
Lemma lem3075538 : term212.
Proof. exact (@lem1980026 term61 term74 term95 term74). Qed.
Lemma lem3075540 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075541 : term150 = term156.
Proof. exact (@lem3075540 (NUMERAL 0) term75). Qed.
Lemma lem3075542 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075543 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075544 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075543 h1) (fun h1 : term156 = True => @lem3075542)). Qed.
Lemma lem3075545 : term156 = True.
Proof. exact (EQ_MP (@lem3075544) (@lem3075542)). Qed.
Lemma lem3075546 : term150 = True.
Proof. exact (TRANS (@lem3075541) (@lem3075545)). Qed.
Lemma lem3075547 : True = term150.
Proof. exact (SYM (@lem3075546)). Qed.
Lemma lem3075548 : term150.
Proof. exact (EQ_MP (@lem3075547) (@lem0)). Qed.
Lemma lem3075549 : term213.
Proof. exact (@lem3075538 (@lem3075548)). Qed.
Lemma lem3075551 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3075552 : term150 = term156.
Proof. exact (@lem3075551 (NUMERAL 0) term75). Qed.
Lemma lem3075553 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075554 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3075555 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075554 h1) (fun h1 : term156 = True => @lem3075553)). Qed.
Lemma lem3075556 : term156 = True.
Proof. exact (EQ_MP (@lem3075555) (@lem3075553)). Qed.
Lemma lem3075557 : term150 = True.
Proof. exact (TRANS (@lem3075552) (@lem3075556)). Qed.
Lemma lem3075558 : True = term150.
Proof. exact (SYM (@lem3075557)). Qed.
Lemma lem3075559 : term150.
Proof. exact (EQ_MP (@lem3075558) (@lem0)). Qed.
Lemma lem3075560 : term211 = term214.
Proof. exact (@lem3075549 (@lem3075559)). Qed.
Lemma lem3075562 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3075563 : term122 = term127.
Proof. exact (@lem3075562 term75 term75). Qed.
Lemma lem3075564 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3075565 : term107 = term75.
Proof. exact (EQ_MP (@lem3075564) (@lem940073)). Qed.
Lemma lem3075566 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3075567 : term105 = term74.
Proof. exact (MK_COMB (@lem3075566) (@lem3075565)). Qed.
Lemma lem3075568 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3075569 : term127 = term95.
Proof. exact (MK_COMB (@lem3075568) (@lem3075567)). Qed.
Lemma lem3075570 : term122 = term95.
Proof. exact (TRANS (@lem3075563) (@lem3075569)). Qed.
Lemma lem3075572 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3075573 : term161 = term61.
Proof. exact (@lem3075572 term75). Qed.
Lemma lem3075574 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3075575 : term215 = term63.
Proof. exact (MK_COMB (@lem3075574) (@lem3075573)). Qed.
Lemma lem3075576 : term214 = term209.
Proof. exact (MK_COMB (@lem3075575) (@lem3075570)). Qed.
Lemma lem3075578 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3075579 : term209 = term218.
Proof. exact (@lem3075578 (NUMERAL 0) term75). Qed.
Lemma lem3075580 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3075581 (h1 : term157 = (BIT1 0)) : (term75 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3075582 : (term157 = (BIT1 0)) = ((term75 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3075581 h1) (fun h1 : (term75 = (NUMERAL 0)) = False => @lem3075580)). Qed.
Lemma lem3075583 : (term75 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3075582) (@lem3075580)). Qed.
Lemma lem3075584 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3075585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3075586 : term219 = (and True).
Proof. exact (MK_COMB (@lem3075585) (@lem3075584)). Qed.
Lemma lem3075587 : term218 = (True /\ False).
Proof. exact (MK_COMB (@lem3075586) (@lem3075583)). Qed.
Lemma lem3075589 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3075590 : term218 = False.
Proof. exact (TRANS (@lem3075587) (@lem3075589)). Qed.
Lemma lem3075591 : term209 = False.
Proof. exact (TRANS (@lem3075579) (@lem3075590)). Qed.
Lemma lem3075592 : term214 = False.
Proof. exact (TRANS (@lem3075576) (@lem3075591)). Qed.
Lemma lem3075593 : term211 = False.
Proof. exact (TRANS (@lem3075560) (@lem3075592)). Qed.
Lemma lem3075594 : term209 = False.
Proof. exact (TRANS (@lem3075537) (@lem3075593)). Qed.
Lemma lem3075595 : term208 = False.
Proof. exact (TRANS (@lem3075528) (@lem3075594)). Qed.
Lemma lem3075596 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : False.
Proof. exact (EQ_MP (@lem3075595) (@lem3075525 _32032 _32033 h1)). Qed.
Lemma lem3075598 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : term148 _32032 _32033.
Proof. exact (h1). Qed.
Lemma lem3075599 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : (term148 _32032 _32033) = False.
Proof. exact (prop_ext (fun h2 : term148 _32032 _32033 => @lem3075596 _32032 _32033 h1) (fun h2 : False => @lem3075598 _32032 _32033 h1)). Qed.
Lemma lem3075600 (_32032 : int) (_32033 : int) (h1 : term148 _32032 _32033) : False.
Proof. exact (EQ_MP (@lem3075599 _32032 _32033 h1) (@lem3075598 _32032 _32033 h1)). Qed.
Lemma lem3075601 (_32032 : int) (_32033 : int) (h1 : term87 _32032 _32033) : term87 _32032 _32033.
Proof. exact (h1). Qed.
Lemma lem3075602 (_32032 : int) (_32033 : int) (h1 : term87 _32032 _32033) : term148 _32032 _32033.
Proof. exact (EQ_MP (@lem3075130 _32032 _32033) (@lem3075601 _32032 _32033 h1)). Qed.
Lemma lem3075603 (_32032 : int) (_32033 : int) (h1 : term87 _32032 _32033) : (term148 _32032 _32033) = False.
Proof. exact (prop_ext (fun h2 : term148 _32032 _32033 => @lem3075600 _32032 _32033 h2) (fun h2 : False => @lem3075602 _32032 _32033 h1)). Qed.
Lemma lem3075604 (_32032 : int) (_32033 : int) (h1 : term87 _32032 _32033) : False.
Proof. exact (EQ_MP (@lem3075603 _32032 _32033 h1) (@lem3075602 _32032 _32033 h1)). Qed.
Lemma lem3075605 (_32032 : int) (_32033 : int) : term220 _32032 _32033.
Proof. exact (fun h0 : term87 _32032 _32033 => @lem3075604 _32032 _32033 h0). Qed.
Lemma lem3075606 (_32032 : int) (_32033 : int) : term221 _32032 _32033.
Proof. exact (@lem1386578 (term222 _32032 _32033)). Qed.
Lemma lem3075609 (_32032 : int) (_32033 : int) : term222 _32032 _32033.
Proof. exact (@lem3075606 _32032 _32033 (@lem3075605 _32032 _32033)). Qed.
Lemma lem3075610 (_32032 : int) (_32033 : int) : (term85 _32032 _32033) = (term42 _32032 _32033).
Proof. exact (SYM (@lem3074872 _32032 _32033)). Qed.
Lemma lem3075611 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3075612 (_32032 : int) (_32033 : int) : (term222 _32032 _32033) = (term29 _32032 _32033).
Proof. exact (MK_COMB (@lem3075611) (@lem3075610 _32032 _32033)). Qed.
Lemma lem3075613 (_32032 : int) (_32033 : int) : term29 _32032 _32033.
Proof. exact (EQ_MP (@lem3075612 _32032 _32033) (@lem3075609 _32032 _32033)). Qed.
Lemma lem3075614 (_32032 : int) (_32033 : int) : term30 _32032 _32033.
Proof. exact (EQ_MP (@lem3074741 _32032 _32033) (@lem3075613 _32032 _32033)). Qed.
Lemma lem3075615 (m : nat) (n : nat) : term223 m n.
Proof. exact (@lem3075614 (int_of_num m) (term224 m n)). Qed.
Lemma lem3075616 (m : nat) (n : nat) : term225 m n.
Proof. exact (@lem3075615 m n (@lem3074737 m)). Qed.
Lemma lem3075617 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem3075616 m n (@lem3074740 m n)). Qed.
Lemma lem3075618 (m : nat) (n : nat) : (term24 m n) = ((term0 m n) = (term1 m n)).
Proof. exact (SYM (@lem3074734 m n)). Qed.
Lemma lem3075620 (m : nat) : term226 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem3075621 (m : nat) : (term226 m) = (term227 m).
Proof. exact (eq_refl (term226 m)). Qed.
Lemma lem3075622 (m : nat) : term227 m.
Proof. exact (EQ_MP (@lem3075621 m) (@lem3075620 m)). Qed.
Lemma lem3075623 (m : nat) (n : nat) : term228 m n.
Proof. exact (@lem3075622 m n). Qed.
Lemma lem3075624 (m : nat) (n : nat) : (term228 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term229 m n)).
Proof. exact (eq_refl (term228 m n)). Qed.
Lemma lem3075626 (m : nat) : term230 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem3075627 (m : nat) : (term230 m) = (term231 m).
Proof. exact (eq_refl (term230 m)). Qed.
Lemma lem3075628 (m : nat) : term231 m.
Proof. exact (EQ_MP (@lem3075627 m) (@lem3075626 m)). Qed.
Lemma lem3075629 (m : nat) (n : nat) : term232 m n.
Proof. exact (@lem3075628 m n). Qed.
Lemma lem3075630 (m : nat) (n : nat) : (term232 m n) = (term233 m n).
Proof. exact (eq_refl (term232 m n)). Qed.
Lemma lem3075631 (m : nat) (n : nat) : term233 m n.
Proof. exact (EQ_MP (@lem3075630 m n) (@lem3075629 m n)). Qed.
Lemma lem3075632 (m : nat) (n : nat) (p : nat) : term234 m n p.
Proof. exact (@lem3075631 m n p). Qed.
Lemma lem3075633 (m : nat) (n : nat) (p : nat) : (term234 m n p) = ((term235 n m p) = (term236 m n p)).
Proof. exact (eq_refl (term234 m n p)). Qed.
Lemma lem3075635 (h1 : term237) : term237.
Proof. exact (h1). Qed.
Lemma lem3075646 (b : nat) : term238 b.
Proof. exact (fun a : nat => @lem3074597 b a). Qed.
Lemma lem3075647 : term239.
Proof. exact (fun b : nat => @lem3075646 b). Qed.
Lemma lem3075649 (p : Prop) : p = (term240 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3075650 : term241 = term242.
Proof. exact (@lem3075649 term241). Qed.
Lemma lem3075651 : term242 = term241.
Proof. exact (SYM (@lem3075650)). Qed.
Lemma lem3075652 (h1 : term243) : term243.
Proof. exact (h1). Qed.
Lemma lem3075655 (h1 : term244) : term244.
Proof. exact (h1). Qed.
Lemma lem3075656 : term245.
Proof. exact (fun h0 : term244 => @lem3075655 h0). Qed.
Lemma lem3075657 (h1 : term245) : term245.
Proof. exact (h1). Qed.
Lemma lem3075658 (h1 : term244) : term244.
Proof. exact (h1). Qed.
Lemma lem3075659 (h1 : term244) (h2 : term245) : term244.
Proof. exact (@lem3075657 h2 (@lem3075658 h1)). Qed.
Lemma lem3075660 (h1 : term244) : term246.
Proof. exact (fun h0 : term245 => @lem3075659 h1 h0). Qed.
Lemma lem3075661 (h1 : term245) : term245.
Proof. exact (h1). Qed.
Lemma lem3075662 (h1 : term244) (h2 : term245) : term244.
Proof. exact (@lem3075660 h1 (@lem3075661 h2)). Qed.
Lemma lem3075663 (h1 : term245) : term245.
Proof. exact (fun h0 : term244 => @lem3075662 h0 h1). Qed.
Lemma lem3075664 : term247.
Proof. exact (fun h0 : term245 => @lem3075663 h0). Qed.
Lemma lem3075667 : term245.
Proof. exact (@lem3075664 (@lem3075656)). Qed.
Lemma lem3075739 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3075740 : term248 = term249.
Proof. exact (@lem3075739 term239). Qed.
Lemma lem3075753 : term250 = term250.
Proof. exact (eq_refl term250). Qed.
Lemma lem3075754 : term251 = term252.
Proof. exact (MK_COMB (@lem3075753) (@lem3075740)). Qed.
Lemma lem3075757 : term253 = term253.
Proof. exact (eq_refl term253). Qed.
Lemma lem3075764 : term244 = term254.
Proof. exact (MK_COMB (@lem3075757) (@lem3075754)). Qed.
Lemma lem3075765 (b : nat) (a : nat) (x : nat) : (b = (Nat.mul a x)) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (b = (Nat.mul a x))). Qed.
Lemma lem3075766 (b : nat) (a : nat) : (term255 b a) = (term255 b a).
Proof. exact (fun_ext (fun x : nat => @lem3075765 b a x)). Qed.
Lemma lem3075767 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3075768 (b : nat) (a : nat) : (term256 b a) = (term256 b a).
Proof. exact (MK_COMB (@lem3075767) (@lem3075766 b a)). Qed.
Lemma lem3075771 (a : nat) (b : nat) : (term257 a b) = (term257 a b).
Proof. exact (eq_refl (term257 a b)). Qed.
Lemma lem3075772 (b : nat) (a : nat) : ((num_divides a b) = (term256 b a)) = ((num_divides a b) = (term256 b a)).
Proof. exact (MK_COMB (@lem3075771 a b) (@lem3075768 b a)). Qed.
Lemma lem3075773 (b : nat) : (term258 b) = (term258 b).
Proof. exact (fun_ext (fun a : nat => @lem3075772 b a)). Qed.
Lemma lem3075774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3075775 (b : nat) : (term238 b) = (term238 b).
Proof. exact (MK_COMB (@lem3075774) (@lem3075773 b)). Qed.
Lemma lem3075776 : term259 = term259.
Proof. exact (fun_ext (fun b : nat => @lem3075775 b)). Qed.
Lemma lem3075777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3075778 : term239 = term239.
Proof. exact (MK_COMB (@lem3075777) (@lem3075776)). Qed.
Lemma lem3075779 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3075780 : term249 = term249.
Proof. exact (MK_COMB (@lem3075779) (@lem3075778)). Qed.
Lemma lem3075785 (m : nat) (n : nat) : (term260 m n) = (term260 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem3075786 (m : nat) : (term261 m) = (term261 m).
Proof. exact (fun_ext (fun n : nat => @lem3075785 m n)). Qed.
Lemma lem3075787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3075788 (m : nat) : (term262 m) = (term262 m).
Proof. exact (MK_COMB (@lem3075787) (@lem3075786 m)). Qed.
Lemma lem3075789 : term263 = term263.
Proof. exact (fun_ext (fun m : nat => @lem3075788 m)). Qed.
Lemma lem3075790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3075791 : term237 = term237.
Proof. exact (MK_COMB (@lem3075790) (@lem3075789)). Qed.
Lemma lem3075792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3075793 : term250 = term250.
Proof. exact (MK_COMB (@lem3075792) (@lem3075791)). Qed.
Lemma lem3075794 : term252 = term252.
Proof. exact (MK_COMB (@lem3075793) (@lem3075780)). Qed.
Lemma lem3075803 (m : nat) (n : nat) : (term264 m n) = (term264 m n).
Proof. exact (eq_refl (term264 m n)). Qed.
Lemma lem3075804 (m : nat) : (term265 m) = (term265 m).
Proof. exact (fun_ext (fun n : nat => @lem3075803 m n)). Qed.
Lemma lem3075805 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3075806 (m : nat) : (term266 m) = (term266 m).
Proof. exact (MK_COMB (@lem3075805) (@lem3075804 m)). Qed.
Lemma lem3075807 : term267 = term267.
Proof. exact (fun_ext (fun m : nat => @lem3075806 m)). Qed.
Lemma lem3075808 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3075809 : term241 = term241.
Proof. exact (MK_COMB (@lem3075808) (@lem3075807)). Qed.
Lemma lem3075810 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3075811 : term243 = term243.
Proof. exact (MK_COMB (@lem3075810) (@lem3075809)). Qed.
Lemma lem3075812 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3075813 : term253 = term253.
Proof. exact (MK_COMB (@lem3075812) (@lem3075811)). Qed.
Lemma lem3075814 : term254 = term254.
Proof. exact (MK_COMB (@lem3075813) (@lem3075794)). Qed.
Lemma lem3075869 : term244 = term254.
Proof. exact (TRANS (@lem3075764) (@lem3075814)). Qed.
Lemma lem3075870 : term254 = term244.
Proof. exact (SYM (@lem3075869)). Qed.
Lemma lem3075871 (h1 : term243) : term243.
Proof. exact (h1). Qed.
Lemma lem3075872 (h1 : term237) : term237.
Proof. exact (h1). Qed.
Lemma lem3075873 (h1 : term239) : term239.
Proof. exact (h1). Qed.
Lemma lem3075881 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (@lem17160 (Peano.le m n) (n = (NUMERAL 0))). Qed.
Lemma lem3075883 (m : nat) (n : nat) : (term270 m n) = (term270 m n).
Proof. exact (eq_refl (term270 m n)). Qed.
Lemma lem3075884 (m : nat) (n : nat) : (term271 m n) = (term272 m n).
Proof. exact (MK_COMB (@lem3075883 m n) (@lem3075881 m n)). Qed.
Lemma lem3075885 (m : nat) (n : nat) : (term273 m n) = (term271 m n).
Proof. exact (@lem17362 (num_divides m n) (term274 m n)). Qed.
Lemma lem3075886 (m : nat) (n : nat) : (term273 m n) = (term272 m n).
Proof. exact (TRANS (@lem3075885 m n) (@lem3075884 m n)). Qed.
Lemma lem3075887 (P : nat -> Prop) : (term275 P) = (term276 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3075888 (m : nat) : (term277 m) = (term278 m).
Proof. exact (@lem3075887 (term265 m)). Qed.
Lemma lem3075889 (m : nat) (n : nat) : (term279 m n) = (term264 m n).
Proof. exact (eq_refl (term279 m n)). Qed.
Lemma lem3075890 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3075891 (m : nat) (n : nat) : (term280 m n) = (term273 m n).
Proof. exact (MK_COMB (@lem3075890) (@lem3075889 m n)). Qed.
Lemma lem3075892 (m : nat) (n : nat) : (term280 m n) = (term272 m n).
Proof. exact (TRANS (@lem3075891 m n) (@lem3075886 m n)). Qed.
Lemma lem3075893 (m : nat) : (term281 m) = (term282 m).
Proof. exact (fun_ext (fun n : nat => @lem3075892 m n)). Qed.
Lemma lem3075894 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3075895 (m : nat) : (term278 m) = (term283 m).
Proof. exact (MK_COMB (@lem3075894) (@lem3075893 m)). Qed.
Lemma lem3075896 (m : nat) : (term277 m) = (term283 m).
Proof. exact (TRANS (@lem3075888 m) (@lem3075895 m)). Qed.
Lemma lem3075897 (P : nat -> Prop) : (term275 P) = (term276 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3075898 : term243 = term284.
Proof. exact (@lem3075897 term267). Qed.
Lemma lem3075899 (m : nat) : (term285 m) = (term266 m).
Proof. exact (eq_refl (term285 m)). Qed.
Lemma lem3075900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3075901 (m : nat) : (term286 m) = (term277 m).
Proof. exact (MK_COMB (@lem3075900) (@lem3075899 m)). Qed.
Lemma lem3075902 (m : nat) : (term286 m) = (term283 m).
Proof. exact (TRANS (@lem3075901 m) (@lem3075896 m)). Qed.
Lemma lem3075903 : term287 = term288.
Proof. exact (fun_ext (fun m : nat => @lem3075902 m)). Qed.
Lemma lem3075904 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3075905 : term284 = term289.
Proof. exact (MK_COMB (@lem3075904) (@lem3075903)). Qed.
Lemma lem3075962 : term243 = term289.
Proof. exact (TRANS (@lem3075898) (@lem3075905)). Qed.
Lemma lem3075963 (h1 : term243) : term289.
Proof. exact (EQ_MP (@lem3075962) (@lem3075871 h1)). Qed.
Lemma lem3075968 (m : nat) (n : nat) : (term260 m n) = (term260 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem3075969 (m : nat) : (term261 m) = (term261 m).
Proof. exact (fun_ext (fun n : nat => @lem3075968 m n)). Qed.
Lemma lem3075970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3075971 (m : nat) : (term262 m) = (term262 m).
Proof. exact (MK_COMB (@lem3075970) (@lem3075969 m)). Qed.
Lemma lem3075972 : term263 = term263.
Proof. exact (fun_ext (fun m : nat => @lem3075971 m)). Qed.
Lemma lem3075973 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076030 : term237 = term237.
Proof. exact (MK_COMB (@lem3075973) (@lem3075972)). Qed.
Lemma lem3076031 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem3076030) (@lem3075872 h1)). Qed.
Lemma lem3076035 (b : nat) (a : nat) (x : nat) : (b = (Nat.mul a x)) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (b = (Nat.mul a x))). Qed.
Lemma lem3076036 (P : nat -> Prop) : (term290 P) = (term291 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem3076037 (b : nat) (a : nat) : (term292 b a) = (term293 b a).
Proof. exact (@lem3076036 (term255 b a)). Qed.
Lemma lem3076038 (b : nat) (a : nat) (x : nat) : (term294 b a x) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (term294 b a x)). Qed.
Lemma lem3076039 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3076041 (b : nat) (a : nat) (x : nat) : (term295 b a x) = (term296 b a x).
Proof. exact (MK_COMB (@lem3076039) (@lem3076038 b a x)). Qed.
Lemma lem3076042 (b : nat) (a : nat) : (term297 b a) = (term298 b a).
Proof. exact (fun_ext (fun x : nat => @lem3076041 b a x)). Qed.
Lemma lem3076043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076044 (b : nat) (a : nat) : (term293 b a) = (term299 b a).
Proof. exact (MK_COMB (@lem3076043) (@lem3076042 b a)). Qed.
Lemma lem3076045 (b : nat) (a : nat) : (term292 b a) = (term299 b a).
Proof. exact (TRANS (@lem3076037 b a) (@lem3076044 b a)). Qed.
Lemma lem3076046 (b : nat) (a : nat) : (term255 b a) = (term255 b a).
Proof. exact (fun_ext (fun x : nat => @lem3076035 b a x)). Qed.
Lemma lem3076047 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3076048 (b : nat) (a : nat) : (term256 b a) = (term256 b a).
Proof. exact (MK_COMB (@lem3076047) (@lem3076046 b a)). Qed.
Lemma lem3076050 (a : nat) (b : nat) : (term300 a b) = (term300 a b).
Proof. exact (eq_refl (term300 a b)). Qed.
Lemma lem3076051 (b : nat) (a : nat) : (term301 b a) = (term301 b a).
Proof. exact (MK_COMB (@lem3076050 a b) (@lem3076048 b a)). Qed.
Lemma lem3076053 (a : nat) (b : nat) : (term302 a b) = (term302 a b).
Proof. exact (eq_refl (term302 a b)). Qed.
Lemma lem3076054 (b : nat) (a : nat) : (term303 b a) = (term304 b a).
Proof. exact (MK_COMB (@lem3076053 a b) (@lem3076045 b a)). Qed.
Lemma lem3076055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3076056 (b : nat) (a : nat) : (term305 b a) = (term306 b a).
Proof. exact (MK_COMB (@lem3076055) (@lem3076054 b a)). Qed.
Lemma lem3076057 (b : nat) (a : nat) : (term307 b a) = (term308 b a).
Proof. exact (MK_COMB (@lem3076056 b a) (@lem3076051 b a)). Qed.
Lemma lem3076058 (b : nat) (a : nat) : ((num_divides a b) = (term256 b a)) = (term307 b a).
Proof. exact (@lem17784 (num_divides a b) (term256 b a)). Qed.
Lemma lem3076059 (b : nat) (a : nat) : ((num_divides a b) = (term256 b a)) = (term308 b a).
Proof. exact (TRANS (@lem3076058 b a) (@lem3076057 b a)). Qed.
Lemma lem3076060 (b : nat) : (term258 b) = (term309 b).
Proof. exact (fun_ext (fun a : nat => @lem3076059 b a)). Qed.
Lemma lem3076061 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076062 (b : nat) : (term238 b) = (term310 b).
Proof. exact (MK_COMB (@lem3076061) (@lem3076060 b)). Qed.
Lemma lem3076063 : term259 = term311.
Proof. exact (fun_ext (fun b : nat => @lem3076062 b)). Qed.
Lemma lem3076064 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076065 : term239 = term312.
Proof. exact (MK_COMB (@lem3076064) (@lem3076063)). Qed.
Lemma lem3076071 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3076072 (P : nat -> Prop) (Q : nat -> Prop) : (term315 P Q) = (term316 P Q).
Proof. exact (@lem3076071 nat P Q). Qed.
Lemma lem3076073 (b : nat) : (term317 b) = (term318 b).
Proof. exact (@lem3076072 (term319 b) (term320 b)). Qed.
Lemma lem3076074 (b : nat) (a : nat) : (term321 b a) = (term304 b a).
Proof. exact (eq_refl (term321 b a)). Qed.
Lemma lem3076075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3076076 (b : nat) (a : nat) : (term322 b a) = (term306 b a).
Proof. exact (MK_COMB (@lem3076075) (@lem3076074 b a)). Qed.
Lemma lem3076077 (b : nat) (a : nat) : (term323 b a) = (term301 b a).
Proof. exact (eq_refl (term323 b a)). Qed.
Lemma lem3076078 (b : nat) (a : nat) : (term324 b a) = (term308 b a).
Proof. exact (MK_COMB (@lem3076076 b a) (@lem3076077 b a)). Qed.
Lemma lem3076079 (b : nat) : (term325 b) = (term309 b).
Proof. exact (fun_ext (fun a : nat => @lem3076078 b a)). Qed.
Lemma lem3076080 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076081 (b : nat) : (term317 b) = (term310 b).
Proof. exact (MK_COMB (@lem3076080) (@lem3076079 b)). Qed.
Lemma lem3076082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3076083 (b : nat) : (term326 b) = (term327 b).
Proof. exact (MK_COMB (@lem3076082) (@lem3076081 b)). Qed.
Lemma lem3076084 (b : nat) (a : nat) : (term321 b a) = (term304 b a).
Proof. exact (eq_refl (term321 b a)). Qed.
Lemma lem3076085 (b : nat) : (term328 b) = (term319 b).
Proof. exact (fun_ext (fun a : nat => @lem3076084 b a)). Qed.
Lemma lem3076086 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076087 (b : nat) : (term329 b) = (term330 b).
Proof. exact (MK_COMB (@lem3076086) (@lem3076085 b)). Qed.
Lemma lem3076088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3076089 (b : nat) : (term331 b) = (term332 b).
Proof. exact (MK_COMB (@lem3076088) (@lem3076087 b)). Qed.
Lemma lem3076090 (b : nat) (a : nat) : (term323 b a) = (term301 b a).
Proof. exact (eq_refl (term323 b a)). Qed.
Lemma lem3076091 (b : nat) : (term333 b) = (term320 b).
Proof. exact (fun_ext (fun a : nat => @lem3076090 b a)). Qed.
Lemma lem3076092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076093 (b : nat) : (term334 b) = (term335 b).
Proof. exact (MK_COMB (@lem3076092) (@lem3076091 b)). Qed.
Lemma lem3076094 (b : nat) : (term318 b) = (term336 b).
Proof. exact (MK_COMB (@lem3076089 b) (@lem3076093 b)). Qed.
Lemma lem3076095 (b : nat) : ((term317 b) = (term318 b)) = ((term310 b) = (term336 b)).
Proof. exact (MK_COMB (@lem3076083 b) (@lem3076094 b)). Qed.
Lemma lem3076096 (b : nat) : (term310 b) = (term336 b).
Proof. exact (EQ_MP (@lem3076095 b) (@lem3076073 b)). Qed.
Lemma lem3076201 : term311 = term337.
Proof. exact (fun_ext (fun b : nat => @lem3076096 b)). Qed.
Lemma lem3076202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076203 : term312 = term338.
Proof. exact (MK_COMB (@lem3076202) (@lem3076201)). Qed.
Lemma lem3076205 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3076206 (P : nat -> Prop) (Q : nat -> Prop) : (term315 P Q) = (term316 P Q).
Proof. exact (@lem3076205 nat P Q). Qed.
Lemma lem3076207 : term339 = term340.
Proof. exact (@lem3076206 term341 term342). Qed.
Lemma lem3076208 (b : nat) : (term343 b) = (term330 b).
Proof. exact (eq_refl (term343 b)). Qed.
Lemma lem3076209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3076210 (b : nat) : (term344 b) = (term332 b).
Proof. exact (MK_COMB (@lem3076209) (@lem3076208 b)). Qed.
Lemma lem3076211 (b : nat) : (term345 b) = (term335 b).
Proof. exact (eq_refl (term345 b)). Qed.
Lemma lem3076212 (b : nat) : (term346 b) = (term336 b).
Proof. exact (MK_COMB (@lem3076210 b) (@lem3076211 b)). Qed.
Lemma lem3076213 : term347 = term337.
Proof. exact (fun_ext (fun b : nat => @lem3076212 b)). Qed.
Lemma lem3076214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076215 : term339 = term338.
Proof. exact (MK_COMB (@lem3076214) (@lem3076213)). Qed.
Lemma lem3076216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3076217 : term348 = term349.
Proof. exact (MK_COMB (@lem3076216) (@lem3076215)). Qed.
Lemma lem3076218 (b : nat) : (term343 b) = (term330 b).
Proof. exact (eq_refl (term343 b)). Qed.
Lemma lem3076219 : term350 = term341.
Proof. exact (fun_ext (fun b : nat => @lem3076218 b)). Qed.
Lemma lem3076220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076221 : term351 = term352.
Proof. exact (MK_COMB (@lem3076220) (@lem3076219)). Qed.
Lemma lem3076222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3076223 : term353 = term354.
Proof. exact (MK_COMB (@lem3076222) (@lem3076221)). Qed.
Lemma lem3076224 (b : nat) : (term345 b) = (term335 b).
Proof. exact (eq_refl (term345 b)). Qed.
Lemma lem3076225 : term355 = term342.
Proof. exact (fun_ext (fun b : nat => @lem3076224 b)). Qed.
Lemma lem3076226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076227 : term356 = term357.
Proof. exact (MK_COMB (@lem3076226) (@lem3076225)). Qed.
Lemma lem3076228 : term340 = term358.
Proof. exact (MK_COMB (@lem3076223) (@lem3076227)). Qed.
Lemma lem3076229 : (term339 = term340) = (term338 = term358).
Proof. exact (MK_COMB (@lem3076217) (@lem3076228)). Qed.
Lemma lem3076230 : term338 = term358.
Proof. exact (EQ_MP (@lem3076229) (@lem3076207)). Qed.
Lemma lem3076343 : term312 = term358.
Proof. exact (TRANS (@lem3076203) (@lem3076230)). Qed.
Lemma lem3076345 {A : Type'} (P : Prop) (Q : A -> Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3076346 (P : Prop) (Q : nat -> Prop) : (term361 P Q) = (term362 P Q).
Proof. exact (@lem3076345 nat P Q). Qed.
Lemma lem3076347 (b : nat) (a : nat) : (term363 b a) = (term364 b a).
Proof. exact (@lem3076346 (term365 a b) (term255 b a)). Qed.
Lemma lem3076348 (b : nat) (a : nat) (x : nat) : (term294 b a x) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (term294 b a x)). Qed.
Lemma lem3076349 (b : nat) (a : nat) : (term366 b a) = (term255 b a).
Proof. exact (fun_ext (fun x : nat => @lem3076348 b a x)). Qed.
Lemma lem3076350 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3076351 (b : nat) (a : nat) : (term367 b a) = (term256 b a).
Proof. exact (MK_COMB (@lem3076350) (@lem3076349 b a)). Qed.
Lemma lem3076352 (a : nat) (b : nat) : (term300 a b) = (term300 a b).
Proof. exact (eq_refl (term300 a b)). Qed.
Lemma lem3076353 (b : nat) (a : nat) : (term363 b a) = (term301 b a).
Proof. exact (MK_COMB (@lem3076352 a b) (@lem3076351 b a)). Qed.
Lemma lem3076354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3076355 (b : nat) (a : nat) : (term368 b a) = (term369 b a).
Proof. exact (MK_COMB (@lem3076354) (@lem3076353 b a)). Qed.
Lemma lem3076356 (b : nat) (a : nat) (x : nat) : (term294 b a x) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (term294 b a x)). Qed.
Lemma lem3076357 (a : nat) (b : nat) : (term300 a b) = (term300 a b).
Proof. exact (eq_refl (term300 a b)). Qed.
Lemma lem3076358 (b : nat) (a : nat) (x : nat) : (term370 b a x) = (term371 b a x).
Proof. exact (MK_COMB (@lem3076357 a b) (@lem3076356 b a x)). Qed.
Lemma lem3076359 (b : nat) (a : nat) : (term372 b a) = (term373 b a).
Proof. exact (fun_ext (fun x : nat => @lem3076358 b a x)). Qed.
Lemma lem3076360 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3076361 (b : nat) (a : nat) : (term364 b a) = (term374 b a).
Proof. exact (MK_COMB (@lem3076360) (@lem3076359 b a)). Qed.
Lemma lem3076362 (b : nat) (a : nat) : ((term363 b a) = (term364 b a)) = ((term301 b a) = (term374 b a)).
Proof. exact (MK_COMB (@lem3076355 b a) (@lem3076361 b a)). Qed.
Lemma lem3076363 (b : nat) (a : nat) : (term301 b a) = (term374 b a).
Proof. exact (EQ_MP (@lem3076362 b a) (@lem3076347 b a)). Qed.
Lemma lem3076364 (b : nat) : (term320 b) = (term375 b).
Proof. exact (fun_ext (fun a : nat => @lem3076363 b a)). Qed.
Lemma lem3076365 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076366 (b : nat) : (term335 b) = (term376 b).
Proof. exact (MK_COMB (@lem3076365) (@lem3076364 b)). Qed.
Lemma lem3076368 {A B : Type'} (P : type1413 A B) : (term377 A B P) = (term378 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3076369 (P : type1605) : (term379 P) = (term380 P).
Proof. exact (@lem3076368 nat nat P). Qed.
Lemma lem3076370 (b : nat) : (term381 b) = (term382 b).
Proof. exact (@lem3076369 (term383 b)). Qed.
Lemma lem3076371 (b : nat) (a : nat) : (term384 b a) = (term373 b a).
Proof. exact (eq_refl (term384 b a)). Qed.
Lemma lem3076372 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3076373 (b : nat) (a : nat) (x : nat) : (term385 b a x) = (term386 b a x).
Proof. exact (MK_COMB (@lem3076371 b a) (@lem3076372 x)). Qed.
Lemma lem3076374 (b : nat) (a : nat) (x : nat) : (term386 b a x) = (term371 b a x).
Proof. exact (eq_refl (term386 b a x)). Qed.
Lemma lem3076375 (b : nat) (a : nat) (x : nat) : (term385 b a x) = (term371 b a x).
Proof. exact (TRANS (@lem3076373 b a x) (@lem3076374 b a x)). Qed.
Lemma lem3076376 (b : nat) (a : nat) : (term387 b a) = (term373 b a).
Proof. exact (fun_ext (fun x : nat => @lem3076375 b a x)). Qed.
Lemma lem3076377 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3076378 (b : nat) (a : nat) : (term388 b a) = (term374 b a).
Proof. exact (MK_COMB (@lem3076377) (@lem3076376 b a)). Qed.
Lemma lem3076379 (b : nat) : (term389 b) = (term375 b).
Proof. exact (fun_ext (fun a : nat => @lem3076378 b a)). Qed.
Lemma lem3076380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076381 (b : nat) : (term381 b) = (term376 b).
Proof. exact (MK_COMB (@lem3076380) (@lem3076379 b)). Qed.
Lemma lem3076382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3076383 (b : nat) : (term390 b) = (term391 b).
Proof. exact (MK_COMB (@lem3076382) (@lem3076381 b)). Qed.
Lemma lem3076384 (b : nat) (a : nat) : (term384 b a) = (term373 b a).
Proof. exact (eq_refl (term384 b a)). Qed.
Lemma lem3076385 (x : nat -> nat) (a : nat) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem3076386 (b : nat) (x : nat -> nat) (a : nat) : (term392 b x a) = (term393 b x a).
Proof. exact (MK_COMB (@lem3076384 b a) (@lem3076385 x a)). Qed.
Lemma lem3076387 (b : nat) (x : nat -> nat) (a : nat) : (term393 b x a) = (term394 b x a).
Proof. exact (eq_refl (term393 b x a)). Qed.
Lemma lem3076388 (b : nat) (x : nat -> nat) (a : nat) : (term392 b x a) = (term394 b x a).
Proof. exact (TRANS (@lem3076386 b x a) (@lem3076387 b x a)). Qed.
Lemma lem3076389 (b : nat) (x : nat -> nat) : (term395 b x) = (term396 b x).
Proof. exact (fun_ext (fun a : nat => @lem3076388 b x a)). Qed.
Lemma lem3076390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076391 (b : nat) (x : nat -> nat) : (term397 b x) = (term398 b x).
Proof. exact (MK_COMB (@lem3076390) (@lem3076389 b x)). Qed.
Lemma lem3076392 (b : nat) : (term399 b) = (term400 b).
Proof. exact (fun_ext (fun x : nat -> nat => @lem3076391 b x)). Qed.
Lemma lem3076393 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem3076394 (b : nat) : (term382 b) = (term401 b).
Proof. exact (MK_COMB (@lem3076393) (@lem3076392 b)). Qed.
Lemma lem3076395 (b : nat) : ((term381 b) = (term382 b)) = ((term376 b) = (term401 b)).
Proof. exact (MK_COMB (@lem3076383 b) (@lem3076394 b)). Qed.
Lemma lem3076396 (b : nat) : (term376 b) = (term401 b).
Proof. exact (EQ_MP (@lem3076395 b) (@lem3076370 b)). Qed.
Lemma lem3076397 (b : nat) : (term335 b) = (term401 b).
Proof. exact (TRANS (@lem3076366 b) (@lem3076396 b)). Qed.
Lemma lem3076398 : term342 = term402.
Proof. exact (fun_ext (fun b : nat => @lem3076397 b)). Qed.
Lemma lem3076399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076400 : term357 = term403.
Proof. exact (MK_COMB (@lem3076399) (@lem3076398)). Qed.
Lemma lem3076402 {A B : Type'} (P : type1413 A B) : (term377 A B P) = (term378 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3076403 (P : type1586) : (term404 P) = (term405 P).
Proof. exact (@lem3076402 nat (nat -> nat) P). Qed.
Lemma lem3076404 : term406 = term407.
Proof. exact (@lem3076403 term408). Qed.
Lemma lem3076405 (b : nat) : (term409 b) = (term400 b).
Proof. exact (eq_refl (term409 b)). Qed.
Lemma lem3076406 (x : nat -> nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3076407 (b : nat) (x : nat -> nat) : (term410 b x) = (term411 b x).
Proof. exact (MK_COMB (@lem3076405 b) (@lem3076406 x)). Qed.
Lemma lem3076408 (b : nat) (x : nat -> nat) : (term411 b x) = (term398 b x).
Proof. exact (eq_refl (term411 b x)). Qed.
Lemma lem3076409 (b : nat) (x : nat -> nat) : (term410 b x) = (term398 b x).
Proof. exact (TRANS (@lem3076407 b x) (@lem3076408 b x)). Qed.
Lemma lem3076410 (b : nat) : (term412 b) = (term400 b).
Proof. exact (fun_ext (fun x : nat -> nat => @lem3076409 b x)). Qed.
Lemma lem3076411 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem3076412 (b : nat) : (term413 b) = (term401 b).
Proof. exact (MK_COMB (@lem3076411) (@lem3076410 b)). Qed.
Lemma lem3076413 : term414 = term402.
Proof. exact (fun_ext (fun b : nat => @lem3076412 b)). Qed.
Lemma lem3076414 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076415 : term406 = term403.
Proof. exact (MK_COMB (@lem3076414) (@lem3076413)). Qed.
Lemma lem3076416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3076417 : term415 = term416.
Proof. exact (MK_COMB (@lem3076416) (@lem3076415)). Qed.
Lemma lem3076418 (b : nat) : (term409 b) = (term400 b).
Proof. exact (eq_refl (term409 b)). Qed.
Lemma lem3076419 (x : type1606) (b : nat) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem3076420 (x : type1606) (b : nat) : (term417 x b) = (term418 x b).
Proof. exact (MK_COMB (@lem3076418 b) (@lem3076419 x b)). Qed.
Lemma lem3076421 (x : type1606) (b : nat) : (term418 x b) = (term419 x b).
Proof. exact (eq_refl (term418 x b)). Qed.
Lemma lem3076422 (x : type1606) (b : nat) : (term417 x b) = (term419 x b).
Proof. exact (TRANS (@lem3076420 x b) (@lem3076421 x b)). Qed.
Lemma lem3076423 (x : type1606) : (term420 x) = (term421 x).
Proof. exact (fun_ext (fun b : nat => @lem3076422 x b)). Qed.
Lemma lem3076424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076425 (x : type1606) : (term422 x) = (term423 x).
Proof. exact (MK_COMB (@lem3076424) (@lem3076423 x)). Qed.
Lemma lem3076426 : term424 = term425.
Proof. exact (fun_ext (fun x : type1606 => @lem3076425 x)). Qed.
Lemma lem3076427 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem3076428 : term407 = term426.
Proof. exact (MK_COMB (@lem3076427) (@lem3076426)). Qed.
Lemma lem3076429 : (term406 = term407) = (term403 = term426).
Proof. exact (MK_COMB (@lem3076417) (@lem3076428)). Qed.
Lemma lem3076430 : term403 = term426.
Proof. exact (EQ_MP (@lem3076429) (@lem3076404)). Qed.
Lemma lem3076431 : term357 = term426.
Proof. exact (TRANS (@lem3076400) (@lem3076430)). Qed.
Lemma lem3076432 : term354 = term354.
Proof. exact (eq_refl term354). Qed.
Lemma lem3076433 : term358 = term427.
Proof. exact (MK_COMB (@lem3076432) (@lem3076431)). Qed.
Lemma lem3076435 {A : Type'} (P : Prop) (Q : A -> Prop) : (term428 A P Q) = (term429 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3076436 (P : Prop) (Q : type961) : (term430 P Q) = (term431 P Q).
Proof. exact (@lem3076435 type1606 P Q). Qed.
Lemma lem3076437 : term432 = term433.
Proof. exact (@lem3076436 term352 term425). Qed.
Lemma lem3076438 (x : type1606) : (term434 x) = (term423 x).
Proof. exact (eq_refl (term434 x)). Qed.
Lemma lem3076439 : term435 = term425.
Proof. exact (fun_ext (fun x : type1606 => @lem3076438 x)). Qed.
Lemma lem3076440 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem3076441 : term436 = term426.
Proof. exact (MK_COMB (@lem3076440) (@lem3076439)). Qed.
Lemma lem3076442 : term354 = term354.
Proof. exact (eq_refl term354). Qed.
Lemma lem3076443 : term432 = term427.
Proof. exact (MK_COMB (@lem3076442) (@lem3076441)). Qed.
Lemma lem3076444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3076445 : term437 = term438.
Proof. exact (MK_COMB (@lem3076444) (@lem3076443)). Qed.
Lemma lem3076446 (x : type1606) : (term434 x) = (term423 x).
Proof. exact (eq_refl (term434 x)). Qed.
Lemma lem3076447 : term354 = term354.
Proof. exact (eq_refl term354). Qed.
Lemma lem3076448 (x : type1606) : (term439 x) = (term440 x).
Proof. exact (MK_COMB (@lem3076447) (@lem3076446 x)). Qed.
Lemma lem3076449 : term441 = term442.
Proof. exact (fun_ext (fun x : type1606 => @lem3076448 x)). Qed.
Lemma lem3076450 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem3076451 : term433 = term443.
Proof. exact (MK_COMB (@lem3076450) (@lem3076449)). Qed.
Lemma lem3076452 : (term432 = term433) = (term427 = term443).
Proof. exact (MK_COMB (@lem3076445) (@lem3076451)). Qed.
Lemma lem3076453 : term427 = term443.
Proof. exact (EQ_MP (@lem3076452) (@lem3076437)). Qed.
Lemma lem3076454 : term358 = term443.
Proof. exact (TRANS (@lem3076433) (@lem3076453)). Qed.
Lemma lem3076455 : term312 = term443.
Proof. exact (TRANS (@lem3076343) (@lem3076454)). Qed.
Lemma lem3076456 : term239 = term443.
Proof. exact (TRANS (@lem3076065) (@lem3076455)). Qed.
Lemma lem3076457 (h1 : term239) : term443.
Proof. exact (EQ_MP (@lem3076456) (@lem3075873 h1)). Qed.
Lemma lem3076458 (x : type1606) (h1 : term440 x) : term440 x.
Proof. exact (h1). Qed.
Lemma lem3076459 (m : nat) (h1 : term283 m) : term283 m.
Proof. exact (h1). Qed.
Lemma lem3076483 (m : nat) (n : nat) : (term260 m n) = (term260 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem3076484 (m : nat) : (term261 m) = (term261 m).
Proof. exact (fun_ext (fun n : nat => @lem3076483 m n)). Qed.
Lemma lem3076485 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076486 (m : nat) : (term262 m) = (term262 m).
Proof. exact (MK_COMB (@lem3076485) (@lem3076484 m)). Qed.
Lemma lem3076487 : term263 = term263.
Proof. exact (fun_ext (fun m : nat => @lem3076486 m)). Qed.
Lemma lem3076488 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076489 : term237 = term237.
Proof. exact (MK_COMB (@lem3076488) (@lem3076487)). Qed.
Lemma lem3076490 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem3076489) (@lem3076031 h1)). Qed.
Lemma lem3076513 (x : type1606) (b : nat) (a : nat) : (term444 x b a) = (term444 x b a).
Proof. exact (eq_refl (term444 x b a)). Qed.
Lemma lem3076514 (x : type1606) (b : nat) : (term445 x b) = (term445 x b).
Proof. exact (fun_ext (fun a : nat => @lem3076513 x b a)). Qed.
Lemma lem3076515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076516 (x : type1606) (b : nat) : (term419 x b) = (term419 x b).
Proof. exact (MK_COMB (@lem3076515) (@lem3076514 x b)). Qed.
Lemma lem3076517 (x : type1606) : (term421 x) = (term421 x).
Proof. exact (fun_ext (fun b : nat => @lem3076516 x b)). Qed.
Lemma lem3076518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076519 (x : type1606) : (term423 x) = (term423 x).
Proof. exact (MK_COMB (@lem3076518) (@lem3076517 x)). Qed.
Lemma lem3076530 (b : nat) (a : nat) (x : nat) : (term296 b a x) = (term296 b a x).
Proof. exact (eq_refl (term296 b a x)). Qed.
Lemma lem3076531 (b : nat) (a : nat) : (term298 b a) = (term298 b a).
Proof. exact (fun_ext (fun x : nat => @lem3076530 b a x)). Qed.
Lemma lem3076532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076533 (b : nat) (a : nat) : (term299 b a) = (term299 b a).
Proof. exact (MK_COMB (@lem3076532) (@lem3076531 b a)). Qed.
Lemma lem3076540 (a : nat) (b : nat) : (term302 a b) = (term302 a b).
Proof. exact (eq_refl (term302 a b)). Qed.
Lemma lem3076541 (b : nat) (a : nat) : (term304 b a) = (term304 b a).
Proof. exact (MK_COMB (@lem3076540 a b) (@lem3076533 b a)). Qed.
Lemma lem3076542 (b : nat) : (term319 b) = (term319 b).
Proof. exact (fun_ext (fun a : nat => @lem3076541 b a)). Qed.
Lemma lem3076543 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076544 (b : nat) : (term330 b) = (term330 b).
Proof. exact (MK_COMB (@lem3076543) (@lem3076542 b)). Qed.
Lemma lem3076545 : term341 = term341.
Proof. exact (fun_ext (fun b : nat => @lem3076544 b)). Qed.
Lemma lem3076546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076547 : term352 = term352.
Proof. exact (MK_COMB (@lem3076546) (@lem3076545)). Qed.
Lemma lem3076548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3076549 : term354 = term354.
Proof. exact (MK_COMB (@lem3076548) (@lem3076547)). Qed.
Lemma lem3076550 (x : type1606) : (term440 x) = (term440 x).
Proof. exact (MK_COMB (@lem3076549) (@lem3076519 x)). Qed.
Lemma lem3076551 (x : type1606) (h1 : term440 x) : term440 x.
Proof. exact (EQ_MP (@lem3076550 x) (@lem3076458 x h1)). Qed.
Lemma lem3076579 (m : nat) (n : nat) (h1 : term272 m n) : term272 m n.
Proof. exact (h1). Qed.
Lemma lem3076580 (m : nat) (n : nat) (h1 : term272 m n) : term269 m n.
Proof. exact (proj2 (@lem3076579 m n h1)). Qed.
Lemma lem3076584 (x : type1606) (h1 : term440 x) : term423 x.
Proof. exact (proj2 (@lem3076551 x h1)). Qed.
Lemma lem3076593 (m : nat) (n : nat) : (term260 m n) = (term260 m n).
Proof. exact (eq_refl (term260 m n)). Qed.
Lemma lem3076594 (m : nat) : (term261 m) = (term261 m).
Proof. exact (fun_ext (fun n : nat => @lem3076593 m n)). Qed.
Lemma lem3076595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076596 (m : nat) : (term262 m) = (term262 m).
Proof. exact (MK_COMB (@lem3076595) (@lem3076594 m)). Qed.
Lemma lem3076597 : term263 = term263.
Proof. exact (fun_ext (fun m : nat => @lem3076596 m)). Qed.
Lemma lem3076598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076600 : term237 = term237.
Proof. exact (MK_COMB (@lem3076598) (@lem3076597)). Qed.
Lemma lem3076601 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem3076600) (@lem3076490 h1)). Qed.
Lemma lem3076665 (x : type1606) (b : nat) (a : nat) : (term444 x b a) = (term444 x b a).
Proof. exact (eq_refl (term444 x b a)). Qed.
Lemma lem3076666 (x : type1606) (b : nat) : (term445 x b) = (term445 x b).
Proof. exact (fun_ext (fun a : nat => @lem3076665 x b a)). Qed.
Lemma lem3076667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076668 (x : type1606) (b : nat) : (term419 x b) = (term419 x b).
Proof. exact (MK_COMB (@lem3076667) (@lem3076666 x b)). Qed.
Lemma lem3076669 (x : type1606) : (term421 x) = (term421 x).
Proof. exact (fun_ext (fun b : nat => @lem3076668 x b)). Qed.
Lemma lem3076670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3076672 (x : type1606) : (term423 x) = (term423 x).
Proof. exact (MK_COMB (@lem3076670) (@lem3076669 x)). Qed.
Lemma lem3076673 (x : type1606) (h1 : term440 x) : term423 x.
Proof. exact (EQ_MP (@lem3076672 x) (@lem3076584 x h1)). Qed.
Lemma lem3076674 (_32036 : nat) (h1 : term237) : term446 _32036.
Proof. exact (@lem3076601 h1 _32036). Qed.
Lemma lem3076675 (_32036 : nat) : (term446 _32036) = (term262 _32036).
Proof. exact (eq_refl (term446 _32036)). Qed.
Lemma lem3076676 (_32036 : nat) (h1 : term237) : term262 _32036.
Proof. exact (EQ_MP (@lem3076675 _32036) (@lem3076674 _32036 h1)). Qed.
Lemma lem3076677 (_32036 : nat) (_32037 : nat) (h1 : term237) : term447 _32036 _32037.
Proof. exact (@lem3076676 _32036 h1 _32037). Qed.
Lemma lem3076678 (_32036 : nat) (_32037 : nat) : (term447 _32036 _32037) = (term260 _32036 _32037).
Proof. exact (eq_refl (term447 _32036 _32037)). Qed.
Lemma lem3076689 (_32041 : nat) (x : type1606) (h1 : term440 x) : term448 x _32041.
Proof. exact (@lem3076673 x h1 _32041). Qed.
Lemma lem3076690 (x : type1606) (_32041 : nat) : (term448 x _32041) = (term419 x _32041).
Proof. exact (eq_refl (term448 x _32041)). Qed.
Lemma lem3076691 (_32041 : nat) (x : type1606) (h1 : term440 x) : term419 x _32041.
Proof. exact (EQ_MP (@lem3076690 x _32041) (@lem3076689 _32041 x h1)). Qed.
Lemma lem3076692 (_32041 : nat) (_32042 : nat) (x : type1606) (h1 : term440 x) : term449 x _32041 _32042.
Proof. exact (@lem3076691 _32041 x h1 _32042). Qed.
Lemma lem3076693 (x : type1606) (_32041 : nat) (_32042 : nat) : (term449 x _32041 _32042) = (term444 x _32041 _32042).
Proof. exact (eq_refl (term449 x _32041 _32042)). Qed.
Lemma lem3076700 (_32036 : nat) (_32037 : nat) (h1 : term237) : term260 _32036 _32037.
Proof. exact (EQ_MP (@lem3076678 _32036 _32037) (@lem3076677 _32036 _32037 h1)). Qed.
Lemma lem3076706 (m : nat) (n : nat) (h1 : term272 m n) : term450 n.
Proof. exact (proj2 (@lem3076580 m n h1)). Qed.
Lemma lem3076718 (_32041 : nat) (_32042 : nat) (x : type1606) (h1 : term440 x) : term444 x _32041 _32042.
Proof. exact (EQ_MP (@lem3076693 x _32041 _32042) (@lem3076692 _32041 _32042 x h1)). Qed.
Lemma lem3076738 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem3076739 (_32047 : nat) (_32049 : nat) (h1 : _32047 = _32049) : _32047 = _32049.
Proof. exact (h1). Qed.
Lemma lem3076740 (_32048 : nat) (_32050 : nat) (h1 : _32048 = _32050) : _32048 = _32050.
Proof. exact (h1). Qed.
Lemma lem3076741 (_32047 : nat) (_32049 : nat) (h1 : _32047 = _32049) : (Peano.le _32047) = (Peano.le _32049).
Proof. exact (MK_COMB (@lem3076738) (@lem3076739 _32047 _32049 h1)). Qed.
Lemma lem3076742 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) (h1 : _32047 = _32049) (h2 : _32048 = _32050) : (Peano.le _32047 _32048) = (Peano.le _32049 _32050).
Proof. exact (MK_COMB (@lem3076741 _32047 _32049 h1) (@lem3076740 _32048 _32050 h2)). Qed.
Lemma lem3076744 (b : Prop) (a : Prop) : term451 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3076745 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : term452 _32049 _32050 _32047 _32048.
Proof. exact (@lem3076744 (Peano.le _32049 _32050) (Peano.le _32047 _32048)). Qed.
Lemma lem3076746 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) (h1 : _32047 = _32049) (h2 : _32048 = _32050) : term453 _32049 _32050 _32047 _32048.
Proof. exact (@lem3076745 _32049 _32050 _32047 _32048 (@lem3076742 _32047 _32049 _32048 _32050 h1 h2)). Qed.
Lemma lem3076747 (_32050 : nat) (_32048 : nat) (_32047 : nat) (_32049 : nat) (h1 : _32047 = _32049) : term454 _32049 _32050 _32047 _32048.
Proof. exact (fun h0 : _32048 = _32050 => @lem3076746 _32047 _32049 _32048 _32050 h1 h0). Qed.
Lemma lem3076749 (a : Prop) (b : Prop) : (a -> b) = (term455 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3076750 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : (term454 _32049 _32050 _32047 _32048) = (term456 _32049 _32050 _32047 _32048).
Proof. exact (@lem3076749 (_32048 = _32050) (term453 _32049 _32050 _32047 _32048)). Qed.
Lemma lem3076751 (_32050 : nat) (_32048 : nat) (_32047 : nat) (_32049 : nat) (h1 : _32047 = _32049) : term456 _32049 _32050 _32047 _32048.
Proof. exact (EQ_MP (@lem3076750 _32049 _32050 _32047 _32048) (@lem3076747 _32050 _32048 _32047 _32049 h1)). Qed.
Lemma lem3076752 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : term457 _32049 _32050 _32047 _32048.
Proof. exact (fun h0 : _32047 = _32049 => @lem3076751 _32050 _32048 _32047 _32049 h0). Qed.
Lemma lem3076754 (a : Prop) (b : Prop) : (a -> b) = (term455 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3076755 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : (term457 _32049 _32050 _32047 _32048) = (term458 _32049 _32050 _32047 _32048).
Proof. exact (@lem3076754 (_32047 = _32049) (term456 _32049 _32050 _32047 _32048)). Qed.
Lemma lem3076756 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : term458 _32049 _32050 _32047 _32048.
Proof. exact (EQ_MP (@lem3076755 _32049 _32050 _32047 _32048) (@lem3076752 _32049 _32050 _32047 _32048)). Qed.
Lemma lem3076796 (x : nat) (y : nat) (z : nat) : term459 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem3076798 (m : nat) (n : nat) (h1 : term272 m n) : num_divides m n.
Proof. exact (proj1 (@lem3076579 m n h1)). Qed.
Lemma lem3076799 (m : nat) (n : nat) (h1 : term272 m n) : term460 m n.
Proof. exact (fun h0 : term365 m n => @lem3076798 m n h1). Qed.
Lemma lem3076801 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3076802 (m : nat) (n : nat) : (term460 m n) = (num_divides m n).
Proof. exact (@lem3076801 (num_divides m n)). Qed.
Lemma lem3076803 (m : nat) (n : nat) (h1 : term272 m n) : num_divides m n.
Proof. exact (EQ_MP (@lem3076802 m n) (@lem3076799 m n h1)). Qed.
Lemma lem3076809 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3076810 (x : type1606) (_32042 : nat) (_32041 : nat) : (term444 x _32041 _32042) = (term462 x _32042 _32041).
Proof. exact (@lem3076809 (_32041 = (term463 x _32041 _32042)) (term365 _32042 _32041)). Qed.
Lemma lem3076818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3076819 (x : type1606) (_32042 : nat) (_32041 : nat) : (term464 x _32041 _32042) = (term465 x _32042 _32041).
Proof. exact (MK_COMB (@lem3076818) (@lem3076810 x _32042 _32041)). Qed.
Lemma lem3076827 (x : type1606) (_32042 : nat) (_32041 : nat) : (term462 x _32042 _32041) = (term462 x _32042 _32041).
Proof. exact (eq_refl (term462 x _32042 _32041)). Qed.
Lemma lem3076828 (x : type1606) (_32042 : nat) (_32041 : nat) : ((term444 x _32041 _32042) = (term462 x _32042 _32041)) = ((term462 x _32042 _32041) = (term462 x _32042 _32041)).
Proof. exact (MK_COMB (@lem3076819 x _32042 _32041) (@lem3076827 x _32042 _32041)). Qed.
Lemma lem3076830 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3076831 (x : Prop) : (x = x) = True.
Proof. exact (@lem3076830 Prop x). Qed.
Lemma lem3076832 (x : type1606) (_32042 : nat) (_32041 : nat) : ((term462 x _32042 _32041) = (term462 x _32042 _32041)) = True.
Proof. exact (@lem3076831 (term462 x _32042 _32041)). Qed.
Lemma lem3076833 (x : type1606) (_32042 : nat) (_32041 : nat) : ((term444 x _32041 _32042) = (term462 x _32042 _32041)) = True.
Proof. exact (TRANS (@lem3076828 x _32042 _32041) (@lem3076832 x _32042 _32041)). Qed.
Lemma lem3076834 (x : type1606) (_32042 : nat) (_32041 : nat) : True = ((term444 x _32041 _32042) = (term462 x _32042 _32041)).
Proof. exact (SYM (@lem3076833 x _32042 _32041)). Qed.
Lemma lem3076835 (x : type1606) (_32042 : nat) (_32041 : nat) : (term444 x _32041 _32042) = (term462 x _32042 _32041).
Proof. exact (EQ_MP (@lem3076834 x _32042 _32041) (@lem0)). Qed.
Lemma lem3076836 (_32042 : nat) (_32041 : nat) (x : type1606) (h1 : term440 x) : term462 x _32042 _32041.
Proof. exact (EQ_MP (@lem3076835 x _32042 _32041) (@lem3076718 _32041 _32042 x h1)). Qed.
Lemma lem3076838 (b : Prop) (a : Prop) : (a \/ b) = (term466 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3076839 (x : type1606) (_32041 : nat) (_32042 : nat) : (term462 x _32042 _32041) = (term467 x _32041 _32042).
Proof. exact (@lem3076838 (term365 _32042 _32041) (_32041 = (term463 x _32041 _32042))). Qed.
Lemma lem3076841 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3076842 (_32042 : nat) (_32041 : nat) : (term468 _32042 _32041) = (num_divides _32042 _32041).
Proof. exact (@lem3076841 (num_divides _32042 _32041)). Qed.
Lemma lem3076843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3076844 (_32042 : nat) (_32041 : nat) : (term469 _32042 _32041) = (term470 _32042 _32041).
Proof. exact (MK_COMB (@lem3076843) (@lem3076842 _32042 _32041)). Qed.
Lemma lem3076845 (x : type1606) (_32041 : nat) (_32042 : nat) : (_32041 = (term463 x _32041 _32042)) = (_32041 = (term463 x _32041 _32042)).
Proof. exact (eq_refl (_32041 = (term463 x _32041 _32042))). Qed.
Lemma lem3076846 (x : type1606) (_32041 : nat) (_32042 : nat) : (term467 x _32041 _32042) = (term471 x _32041 _32042).
Proof. exact (MK_COMB (@lem3076844 _32042 _32041) (@lem3076845 x _32041 _32042)). Qed.
Lemma lem3076847 (x : type1606) (_32041 : nat) (_32042 : nat) : (term462 x _32042 _32041) = (term471 x _32041 _32042).
Proof. exact (TRANS (@lem3076839 x _32041 _32042) (@lem3076846 x _32041 _32042)). Qed.
Lemma lem3076850 (_32041 : nat) (_32042 : nat) (x : type1606) (h1 : term440 x) : term471 x _32041 _32042.
Proof. exact (EQ_MP (@lem3076847 x _32041 _32042) (@lem3076836 _32042 _32041 x h1)). Qed.
Lemma lem3076851 (n : nat) (m : nat) (x : type1606) (h1 : term440 x) : term471 x n m.
Proof. exact (@lem3076850 n m x h1). Qed.
Lemma lem3076854 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : n = (term463 x n m).
Proof. exact (@lem3076851 n m x h1 (@lem3076803 m n h2)). Qed.
Lemma lem3076855 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term472 x n m.
Proof. exact (fun h0 : term473 x n m => @lem3076854 x m n h1 h2). Qed.
Lemma lem3076857 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3076858 (x : type1606) (n : nat) (m : nat) : (term472 x n m) = (n = (term463 x n m)).
Proof. exact (@lem3076857 (n = (term463 x n m))). Qed.
Lemma lem3076859 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : n = (term463 x n m).
Proof. exact (EQ_MP (@lem3076858 x n m) (@lem3076855 x m n h1 h2)). Qed.
Lemma lem3076861 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3076862 (n : nat) : n = n.
Proof. exact (@lem3076861 n). Qed.
Lemma lem3076863 (n : nat) : term474 n.
Proof. exact (fun h0 : term475 n => @lem3076862 n). Qed.
Lemma lem3076865 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3076866 (n : nat) : (term474 n) = (n = n).
Proof. exact (@lem3076865 (n = n)). Qed.
Lemma lem3076867 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem3076866 n) (@lem3076863 n)). Qed.
Lemma lem3076885 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3076886 (y : nat) (x : nat) (z : nat) : (term476 x y z) = (term477 y x z).
Proof. exact (@lem3076885 (y = z) (term478 x z)). Qed.
Lemma lem3076896 (x : nat) (y : nat) : (term479 x y) = (term479 x y).
Proof. exact (eq_refl (term479 x y)). Qed.
Lemma lem3076897 (y : nat) (x : nat) (z : nat) : (term459 x y z) = (term480 y x z).
Proof. exact (MK_COMB (@lem3076896 x y) (@lem3076886 y x z)). Qed.
Lemma lem3076901 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3076902 (y : nat) (x : nat) (z : nat) : (term480 y x z) = (term482 y x z).
Proof. exact (@lem3076901 (y = z) (term478 x y) (term478 x z)). Qed.
Lemma lem3076924 (y : nat) (x : nat) (z : nat) : (term459 x y z) = (term482 y x z).
Proof. exact (TRANS (@lem3076897 y x z) (@lem3076902 y x z)). Qed.
Lemma lem3076925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3076926 (y : nat) (x : nat) (z : nat) : (term483 x y z) = (term484 y x z).
Proof. exact (MK_COMB (@lem3076925) (@lem3076924 y x z)). Qed.
Lemma lem3076948 (y : nat) (x : nat) (z : nat) : (term482 y x z) = (term482 y x z).
Proof. exact (eq_refl (term482 y x z)). Qed.
Lemma lem3076949 (y : nat) (x : nat) (z : nat) : ((term459 x y z) = (term482 y x z)) = ((term482 y x z) = (term482 y x z)).
Proof. exact (MK_COMB (@lem3076926 y x z) (@lem3076948 y x z)). Qed.
Lemma lem3076951 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3076952 (x : Prop) : (x = x) = True.
Proof. exact (@lem3076951 Prop x). Qed.
Lemma lem3076953 (y : nat) (x : nat) (z : nat) : ((term482 y x z) = (term482 y x z)) = True.
Proof. exact (@lem3076952 (term482 y x z)). Qed.
Lemma lem3076954 (y : nat) (x : nat) (z : nat) : ((term459 x y z) = (term482 y x z)) = True.
Proof. exact (TRANS (@lem3076949 y x z) (@lem3076953 y x z)). Qed.
Lemma lem3076955 (y : nat) (x : nat) (z : nat) : True = ((term459 x y z) = (term482 y x z)).
Proof. exact (SYM (@lem3076954 y x z)). Qed.
Lemma lem3076956 (y : nat) (x : nat) (z : nat) : (term459 x y z) = (term482 y x z).
Proof. exact (EQ_MP (@lem3076955 y x z) (@lem0)). Qed.
Lemma lem3076957 (y : nat) (x : nat) (z : nat) : term482 y x z.
Proof. exact (EQ_MP (@lem3076956 y x z) (@lem3076796 x y z)). Qed.
Lemma lem3076959 (b : Prop) (a : Prop) : (a \/ b) = (term466 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3076960 (x : nat) (y : nat) (z : nat) : (term482 y x z) = (term485 x y z).
Proof. exact (@lem3076959 (term486 y x z) (y = z)). Qed.
Lemma lem3076962 (a : Prop) (b : Prop) : (term487 a b) = (term488 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3076963 (y : nat) (x : nat) (z : nat) : (term489 y x z) = (term490 y x z).
Proof. exact (@lem3076962 (term478 x y) (term478 x z)). Qed.
Lemma lem3076965 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3076966 (x : nat) (y : nat) : (term491 x y) = (x = y).
Proof. exact (@lem3076965 (x = y)). Qed.
Lemma lem3076967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3076968 (x : nat) (y : nat) : (term492 x y) = (term493 x y).
Proof. exact (MK_COMB (@lem3076967) (@lem3076966 x y)). Qed.
Lemma lem3076970 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3076971 (x : nat) (z : nat) : (term491 x z) = (x = z).
Proof. exact (@lem3076970 (x = z)). Qed.
Lemma lem3076972 (y : nat) (x : nat) (z : nat) : (term490 y x z) = (term494 y x z).
Proof. exact (MK_COMB (@lem3076968 x y) (@lem3076971 x z)). Qed.
Lemma lem3076973 (y : nat) (x : nat) (z : nat) : (term489 y x z) = (term494 y x z).
Proof. exact (TRANS (@lem3076963 y x z) (@lem3076972 y x z)). Qed.
Lemma lem3076974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3076975 (y : nat) (x : nat) (z : nat) : (term495 y x z) = (term496 y x z).
Proof. exact (MK_COMB (@lem3076974) (@lem3076973 y x z)). Qed.
Lemma lem3076976 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3076977 (x : nat) (y : nat) (z : nat) : (term485 x y z) = (term497 x y z).
Proof. exact (MK_COMB (@lem3076975 y x z) (@lem3076976 y z)). Qed.
Lemma lem3076978 (x : nat) (y : nat) (z : nat) : (term482 y x z) = (term497 x y z).
Proof. exact (TRANS (@lem3076960 x y z) (@lem3076977 x y z)). Qed.
Lemma lem3076980 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term498 x m n.
Proof. exact (conj (@lem3076859 x m n h1 h2) (@lem3076867 n)). Qed.
Lemma lem3076982 (x : nat) (y : nat) (z : nat) : term497 x y z.
Proof. exact (EQ_MP (@lem3076978 x y z) (@lem3076957 y x z)). Qed.
Lemma lem3076983 (x : type1606) (m : nat) (n : nat) : term499 x m n.
Proof. exact (@lem3076982 n (term463 x n m) n). Qed.
Lemma lem3076986 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : (term463 x n m) = n.
Proof. exact (@lem3076983 x m n (@lem3076980 x m n h1 h2)). Qed.
Lemma lem3076987 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term500 x m n.
Proof. exact (fun h0 : term501 x m n => @lem3076986 x m n h1 h2). Qed.
Lemma lem3076989 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3076990 (x : type1606) (m : nat) (n : nat) : (term500 x m n) = ((term463 x n m) = n).
Proof. exact (@lem3076989 ((term463 x n m) = n)). Qed.
Lemma lem3076991 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : (term463 x n m) = n.
Proof. exact (EQ_MP (@lem3076990 x m n) (@lem3076987 x m n h1 h2)). Qed.
Lemma lem3076993 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3076994 (m : nat) : m = m.
Proof. exact (@lem3076993 m). Qed.
Lemma lem3076995 (m : nat) : term474 m.
Proof. exact (fun h0 : term475 m => @lem3076994 m). Qed.
Lemma lem3076997 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3076998 (m : nat) : (term474 m) = (m = m).
Proof. exact (@lem3076997 (m = m)). Qed.
Lemma lem3076999 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem3076998 m) (@lem3076995 m)). Qed.
Lemma lem3077001 (m : nat) (n : nat) (h1 : term272 m n) : num_divides m n.
Proof. exact (proj1 (@lem3076579 m n h1)). Qed.
Lemma lem3077002 (m : nat) (n : nat) (h1 : term272 m n) : term460 m n.
Proof. exact (fun h0 : term365 m n => @lem3077001 m n h1). Qed.
Lemma lem3077004 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3077005 (m : nat) (n : nat) : (term460 m n) = (num_divides m n).
Proof. exact (@lem3077004 (num_divides m n)). Qed.
Lemma lem3077006 (m : nat) (n : nat) (h1 : term272 m n) : num_divides m n.
Proof. exact (EQ_MP (@lem3077005 m n) (@lem3077002 m n h1)). Qed.
Lemma lem3077008 (_32041 : nat) (_32042 : nat) (x : type1606) (h1 : term440 x) : term471 x _32041 _32042.
Proof. exact (EQ_MP (@lem3076847 x _32041 _32042) (@lem3076836 _32042 _32041 x h1)). Qed.
Lemma lem3077009 (n : nat) (m : nat) (x : type1606) (h1 : term440 x) : term471 x n m.
Proof. exact (@lem3077008 n m x h1). Qed.
Lemma lem3077012 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : n = (term463 x n m).
Proof. exact (@lem3077009 n m x h1 (@lem3077006 m n h2)). Qed.
Lemma lem3077013 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term472 x n m.
Proof. exact (fun h0 : term473 x n m => @lem3077012 x m n h1 h2). Qed.
Lemma lem3077015 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3077016 (x : type1606) (n : nat) (m : nat) : (term472 x n m) = (n = (term463 x n m)).
Proof. exact (@lem3077015 (n = (term463 x n m))). Qed.
Lemma lem3077017 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : n = (term463 x n m).
Proof. exact (EQ_MP (@lem3077016 x n m) (@lem3077013 x m n h1 h2)). Qed.
Lemma lem3077019 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3077020 (n : nat) : n = n.
Proof. exact (@lem3077019 n). Qed.
Lemma lem3077021 (n : nat) : term474 n.
Proof. exact (fun h0 : term475 n => @lem3077020 n). Qed.
Lemma lem3077023 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3077024 (n : nat) : (term474 n) = (n = n).
Proof. exact (@lem3077023 (n = n)). Qed.
Lemma lem3077025 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem3077024 n) (@lem3077021 n)). Qed.
Lemma lem3077026 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term498 x m n.
Proof. exact (conj (@lem3077017 x m n h1 h2) (@lem3077025 n)). Qed.
Lemma lem3077028 (x : nat) (y : nat) (z : nat) : term497 x y z.
Proof. exact (EQ_MP (@lem3076978 x y z) (@lem3076957 y x z)). Qed.
Lemma lem3077029 (x : type1606) (m : nat) (n : nat) : term499 x m n.
Proof. exact (@lem3077028 n (term463 x n m) n). Qed.
Lemma lem3077032 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : (term463 x n m) = n.
Proof. exact (@lem3077029 x m n (@lem3077026 x m n h1 h2)). Qed.
Lemma lem3077033 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term500 x m n.
Proof. exact (fun h0 : term501 x m n => @lem3077032 x m n h1 h2). Qed.
Lemma lem3077035 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3077036 (x : type1606) (m : nat) (n : nat) : (term500 x m n) = ((term463 x n m) = n).
Proof. exact (@lem3077035 ((term463 x n m) = n)). Qed.
Lemma lem3077037 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : (term463 x n m) = n.
Proof. exact (EQ_MP (@lem3077036 x m n) (@lem3077033 x m n h1 h2)). Qed.
Lemma lem3077039 (m : nat) (n : nat) (h1 : term272 m n) : term502 m n.
Proof. exact (proj1 (@lem3076580 m n h1)). Qed.
Lemma lem3077040 (m : nat) (n : nat) (h1 : term272 m n) : term503 m n.
Proof. exact (fun h0 : Peano.le m n => @lem3077039 m n h1). Qed.
Lemma lem3077042 (p : Prop) : (term504 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3077043 (m : nat) (n : nat) : (term503 m n) = (term502 m n).
Proof. exact (@lem3077042 (Peano.le m n)). Qed.
Lemma lem3077044 (m : nat) (n : nat) (h1 : term272 m n) : term502 m n.
Proof. exact (EQ_MP (@lem3077043 m n) (@lem3077040 m n h1)). Qed.
Lemma lem3077062 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3077063 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : (term456 _32049 _32050 _32047 _32048) = (term505 _32049 _32050 _32047 _32048).
Proof. exact (@lem3077062 (Peano.le _32049 _32050) (term478 _32048 _32050) (term502 _32047 _32048)). Qed.
Lemma lem3077077 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3077078 (_32047 : nat) (_32048 : nat) (_32050 : nat) : (term506 _32050 _32047 _32048) = (term507 _32047 _32048 _32050).
Proof. exact (@lem3077077 (term502 _32047 _32048) (term478 _32048 _32050)). Qed.
Lemma lem3077086 (_32049 : nat) (_32050 : nat) : (term508 _32049 _32050) = (term508 _32049 _32050).
Proof. exact (eq_refl (term508 _32049 _32050)). Qed.
Lemma lem3077087 (_32049 : nat) (_32047 : nat) (_32048 : nat) (_32050 : nat) : (term505 _32049 _32050 _32047 _32048) = (term509 _32049 _32047 _32048 _32050).
Proof. exact (MK_COMB (@lem3077086 _32049 _32050) (@lem3077078 _32047 _32048 _32050)). Qed.
Lemma lem3077098 (_32049 : nat) (_32047 : nat) (_32048 : nat) (_32050 : nat) : (term456 _32049 _32050 _32047 _32048) = (term509 _32049 _32047 _32048 _32050).
Proof. exact (TRANS (@lem3077063 _32049 _32050 _32047 _32048) (@lem3077087 _32049 _32047 _32048 _32050)). Qed.
Lemma lem3077099 (_32047 : nat) (_32049 : nat) : (term479 _32047 _32049) = (term479 _32047 _32049).
Proof. exact (eq_refl (term479 _32047 _32049)). Qed.
Lemma lem3077100 (_32049 : nat) (_32047 : nat) (_32048 : nat) (_32050 : nat) : (term458 _32049 _32050 _32047 _32048) = (term510 _32049 _32047 _32048 _32050).
Proof. exact (MK_COMB (@lem3077099 _32047 _32049) (@lem3077098 _32049 _32047 _32048 _32050)). Qed.
Lemma lem3077104 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3077105 (_32049 : nat) (_32047 : nat) (_32048 : nat) (_32050 : nat) : (term510 _32049 _32047 _32048 _32050) = (term511 _32049 _32047 _32048 _32050).
Proof. exact (@lem3077104 (Peano.le _32049 _32050) (term478 _32047 _32049) (term507 _32047 _32048 _32050)). Qed.
Lemma lem3077119 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3077120 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term512 _32049 _32047 _32048 _32050) = (term513 _32047 _32049 _32048 _32050).
Proof. exact (@lem3077119 (term502 _32047 _32048) (term478 _32047 _32049) (term478 _32048 _32050)). Qed.
Lemma lem3077140 (_32049 : nat) (_32050 : nat) : (term508 _32049 _32050) = (term508 _32049 _32050).
Proof. exact (eq_refl (term508 _32049 _32050)). Qed.
Lemma lem3077141 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term511 _32049 _32047 _32048 _32050) = (term514 _32047 _32049 _32048 _32050).
Proof. exact (MK_COMB (@lem3077140 _32049 _32050) (@lem3077120 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077152 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term510 _32049 _32047 _32048 _32050) = (term514 _32047 _32049 _32048 _32050).
Proof. exact (TRANS (@lem3077105 _32049 _32047 _32048 _32050) (@lem3077141 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077153 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term458 _32049 _32050 _32047 _32048) = (term514 _32047 _32049 _32048 _32050).
Proof. exact (TRANS (@lem3077100 _32049 _32047 _32048 _32050) (@lem3077152 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3077155 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term515 _32049 _32050 _32047 _32048) = (term516 _32047 _32049 _32048 _32050).
Proof. exact (MK_COMB (@lem3077154) (@lem3077153 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077181 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3077182 (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term517 _32048 _32049 _32050) = (term518 _32049 _32048 _32050).
Proof. exact (@lem3077181 (Peano.le _32049 _32050) (term478 _32048 _32050)). Qed.
Lemma lem3077190 (_32047 : nat) (_32049 : nat) : (term479 _32047 _32049) = (term479 _32047 _32049).
Proof. exact (eq_refl (term479 _32047 _32049)). Qed.
Lemma lem3077191 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term519 _32047 _32048 _32049 _32050) = (term520 _32047 _32049 _32048 _32050).
Proof. exact (MK_COMB (@lem3077190 _32047 _32049) (@lem3077182 _32049 _32048 _32050)). Qed.
Lemma lem3077195 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3077196 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term520 _32047 _32049 _32048 _32050) = (term521 _32047 _32049 _32048 _32050).
Proof. exact (@lem3077195 (Peano.le _32049 _32050) (term478 _32047 _32049) (term478 _32048 _32050)). Qed.
Lemma lem3077216 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term519 _32047 _32048 _32049 _32050) = (term521 _32047 _32049 _32048 _32050).
Proof. exact (TRANS (@lem3077191 _32047 _32049 _32048 _32050) (@lem3077196 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077217 (_32047 : nat) (_32048 : nat) : (term522 _32047 _32048) = (term522 _32047 _32048).
Proof. exact (eq_refl (term522 _32047 _32048)). Qed.
Lemma lem3077218 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term523 _32047 _32048 _32049 _32050) = (term524 _32047 _32049 _32048 _32050).
Proof. exact (MK_COMB (@lem3077217 _32047 _32048) (@lem3077216 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077222 (q : Prop) (p : Prop) (r : Prop) : (term481 p q r) = (term481 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3077223 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term524 _32047 _32049 _32048 _32050) = (term514 _32047 _32049 _32048 _32050).
Proof. exact (@lem3077222 (Peano.le _32049 _32050) (term502 _32047 _32048) (term525 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077253 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : (term523 _32047 _32048 _32049 _32050) = (term514 _32047 _32049 _32048 _32050).
Proof. exact (TRANS (@lem3077218 _32047 _32049 _32048 _32050) (@lem3077223 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077254 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : ((term458 _32049 _32050 _32047 _32048) = (term523 _32047 _32048 _32049 _32050)) = ((term514 _32047 _32049 _32048 _32050) = (term514 _32047 _32049 _32048 _32050)).
Proof. exact (MK_COMB (@lem3077155 _32047 _32049 _32048 _32050) (@lem3077253 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077256 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3077257 (x : Prop) : (x = x) = True.
Proof. exact (@lem3077256 Prop x). Qed.
Lemma lem3077258 (_32047 : nat) (_32049 : nat) (_32048 : nat) (_32050 : nat) : ((term514 _32047 _32049 _32048 _32050) = (term514 _32047 _32049 _32048 _32050)) = True.
Proof. exact (@lem3077257 (term514 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077259 (_32047 : nat) (_32048 : nat) (_32049 : nat) (_32050 : nat) : ((term458 _32049 _32050 _32047 _32048) = (term523 _32047 _32048 _32049 _32050)) = True.
Proof. exact (TRANS (@lem3077254 _32047 _32049 _32048 _32050) (@lem3077258 _32047 _32049 _32048 _32050)). Qed.
Lemma lem3077260 (_32047 : nat) (_32048 : nat) (_32049 : nat) (_32050 : nat) : True = ((term458 _32049 _32050 _32047 _32048) = (term523 _32047 _32048 _32049 _32050)).
Proof. exact (SYM (@lem3077259 _32047 _32048 _32049 _32050)). Qed.
Lemma lem3077261 (_32047 : nat) (_32048 : nat) (_32049 : nat) (_32050 : nat) : (term458 _32049 _32050 _32047 _32048) = (term523 _32047 _32048 _32049 _32050).
Proof. exact (EQ_MP (@lem3077260 _32047 _32048 _32049 _32050) (@lem0)). Qed.
Lemma lem3077262 (_32047 : nat) (_32048 : nat) (_32049 : nat) (_32050 : nat) : term523 _32047 _32048 _32049 _32050.
Proof. exact (EQ_MP (@lem3077261 _32047 _32048 _32049 _32050) (@lem3076756 _32049 _32050 _32047 _32048)). Qed.
Lemma lem3077264 (b : Prop) (a : Prop) : (a \/ b) = (term466 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3077265 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : (term523 _32047 _32048 _32049 _32050) = (term526 _32049 _32050 _32047 _32048).
Proof. exact (@lem3077264 (term519 _32047 _32048 _32049 _32050) (term502 _32047 _32048)). Qed.
Lemma lem3077267 (a : Prop) (b : Prop) : (term487 a b) = (term488 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3077268 (_32047 : nat) (_32048 : nat) (_32049 : nat) (_32050 : nat) : (term527 _32047 _32048 _32049 _32050) = (term528 _32047 _32048 _32049 _32050).
Proof. exact (@lem3077267 (term478 _32047 _32049) (term517 _32048 _32049 _32050)). Qed.
Lemma lem3077270 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3077271 (_32047 : nat) (_32049 : nat) : (term491 _32047 _32049) = (_32047 = _32049).
Proof. exact (@lem3077270 (_32047 = _32049)). Qed.
Lemma lem3077272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3077273 (_32047 : nat) (_32049 : nat) : (term492 _32047 _32049) = (term493 _32047 _32049).
Proof. exact (MK_COMB (@lem3077272) (@lem3077271 _32047 _32049)). Qed.
Lemma lem3077275 (a : Prop) (b : Prop) : (term487 a b) = (term488 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3077276 (_32048 : nat) (_32049 : nat) (_32050 : nat) : (term529 _32048 _32049 _32050) = (term530 _32048 _32049 _32050).
Proof. exact (@lem3077275 (term478 _32048 _32050) (Peano.le _32049 _32050)). Qed.
Lemma lem3077278 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3077279 (_32048 : nat) (_32050 : nat) : (term491 _32048 _32050) = (_32048 = _32050).
Proof. exact (@lem3077278 (_32048 = _32050)). Qed.
Lemma lem3077280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3077281 (_32048 : nat) (_32050 : nat) : (term492 _32048 _32050) = (term493 _32048 _32050).
Proof. exact (MK_COMB (@lem3077280) (@lem3077279 _32048 _32050)). Qed.
Lemma lem3077282 (_32049 : nat) (_32050 : nat) : (term502 _32049 _32050) = (term502 _32049 _32050).
Proof. exact (eq_refl (term502 _32049 _32050)). Qed.
Lemma lem3077283 (_32048 : nat) (_32049 : nat) (_32050 : nat) : (term530 _32048 _32049 _32050) = (term531 _32048 _32049 _32050).
Proof. exact (MK_COMB (@lem3077281 _32048 _32050) (@lem3077282 _32049 _32050)). Qed.
Lemma lem3077284 (_32048 : nat) (_32049 : nat) (_32050 : nat) : (term529 _32048 _32049 _32050) = (term531 _32048 _32049 _32050).
Proof. exact (TRANS (@lem3077276 _32048 _32049 _32050) (@lem3077283 _32048 _32049 _32050)). Qed.
Lemma lem3077285 (_32047 : nat) (_32048 : nat) (_32049 : nat) (_32050 : nat) : (term528 _32047 _32048 _32049 _32050) = (term532 _32047 _32048 _32049 _32050).
Proof. exact (MK_COMB (@lem3077273 _32047 _32049) (@lem3077284 _32048 _32049 _32050)). Qed.
Lemma lem3077286 (_32047 : nat) (_32048 : nat) (_32049 : nat) (_32050 : nat) : (term527 _32047 _32048 _32049 _32050) = (term532 _32047 _32048 _32049 _32050).
Proof. exact (TRANS (@lem3077268 _32047 _32048 _32049 _32050) (@lem3077285 _32047 _32048 _32049 _32050)). Qed.
Lemma lem3077287 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3077288 (_32047 : nat) (_32048 : nat) (_32049 : nat) (_32050 : nat) : (term533 _32047 _32048 _32049 _32050) = (term534 _32047 _32048 _32049 _32050).
Proof. exact (MK_COMB (@lem3077287) (@lem3077286 _32047 _32048 _32049 _32050)). Qed.
Lemma lem3077289 (_32047 : nat) (_32048 : nat) : (term502 _32047 _32048) = (term502 _32047 _32048).
Proof. exact (eq_refl (term502 _32047 _32048)). Qed.
Lemma lem3077290 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : (term526 _32049 _32050 _32047 _32048) = (term535 _32049 _32050 _32047 _32048).
Proof. exact (MK_COMB (@lem3077288 _32047 _32048 _32049 _32050) (@lem3077289 _32047 _32048)). Qed.
Lemma lem3077291 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : (term523 _32047 _32048 _32049 _32050) = (term535 _32049 _32050 _32047 _32048).
Proof. exact (TRANS (@lem3077265 _32049 _32050 _32047 _32048) (@lem3077290 _32049 _32050 _32047 _32048)). Qed.
Lemma lem3077293 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term536 x m n.
Proof. exact (conj (@lem3077037 x m n h1 h2) (@lem3077044 m n h2)). Qed.
Lemma lem3077294 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term537 x m n.
Proof. exact (conj (@lem3076999 m) (@lem3077293 x m n h1 h2)). Qed.
Lemma lem3077296 (_32049 : nat) (_32050 : nat) (_32047 : nat) (_32048 : nat) : term535 _32049 _32050 _32047 _32048.
Proof. exact (EQ_MP (@lem3077291 _32049 _32050 _32047 _32048) (@lem3077262 _32047 _32048 _32049 _32050)). Qed.
Lemma lem3077297 (x : type1606) (n : nat) (m : nat) : term538 x n m.
Proof. exact (@lem3077296 m n m (term463 x n m)). Qed.
Lemma lem3077300 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term539 x n m.
Proof. exact (@lem3077297 x n m (@lem3077294 x m n h1 h2)). Qed.
Lemma lem3077301 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term540 x n m.
Proof. exact (fun h0 : term541 x n m => @lem3077300 x m n h1 h2). Qed.
Lemma lem3077303 (p : Prop) : (term504 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3077304 (x : type1606) (n : nat) (m : nat) : (term540 x n m) = (term539 x n m).
Proof. exact (@lem3077303 (term541 x n m)). Qed.
Lemma lem3077305 (x : type1606) (m : nat) (n : nat) (h1 : term440 x) (h2 : term272 m n) : term539 x n m.
Proof. exact (EQ_MP (@lem3077304 x n m) (@lem3077301 x m n h1 h2)). Qed.
Lemma lem3077318 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3077319 (_32036 : nat) (_32037 : nat) : (term542 _32036 _32037) = (term260 _32036 _32037).
Proof. exact (@lem3077318 (term0 _32036 _32037) ((Nat.mul _32036 _32037) = (NUMERAL 0))). Qed.
Lemma lem3077327 (_32036 : nat) (_32037 : nat) : (term543 _32036 _32037) = (term543 _32036 _32037).
Proof. exact (eq_refl (term543 _32036 _32037)). Qed.
Lemma lem3077328 (_32036 : nat) (_32037 : nat) : ((term260 _32036 _32037) = (term542 _32036 _32037)) = ((term260 _32036 _32037) = (term260 _32036 _32037)).
Proof. exact (MK_COMB (@lem3077327 _32036 _32037) (@lem3077319 _32036 _32037)). Qed.
Lemma lem3077330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3077331 (x : Prop) : (x = x) = True.
Proof. exact (@lem3077330 Prop x). Qed.
Lemma lem3077332 (_32036 : nat) (_32037 : nat) : ((term260 _32036 _32037) = (term260 _32036 _32037)) = True.
Proof. exact (@lem3077331 (term260 _32036 _32037)). Qed.
Lemma lem3077333 (_32036 : nat) (_32037 : nat) : ((term260 _32036 _32037) = (term542 _32036 _32037)) = True.
Proof. exact (TRANS (@lem3077328 _32036 _32037) (@lem3077332 _32036 _32037)). Qed.
Lemma lem3077334 (_32036 : nat) (_32037 : nat) : True = ((term260 _32036 _32037) = (term542 _32036 _32037)).
Proof. exact (SYM (@lem3077333 _32036 _32037)). Qed.
Lemma lem3077335 (_32036 : nat) (_32037 : nat) : (term260 _32036 _32037) = (term542 _32036 _32037).
Proof. exact (EQ_MP (@lem3077334 _32036 _32037) (@lem0)). Qed.
Lemma lem3077336 (_32036 : nat) (_32037 : nat) (h1 : term237) : term542 _32036 _32037.
Proof. exact (EQ_MP (@lem3077335 _32036 _32037) (@lem3076700 _32036 _32037 h1)). Qed.
Lemma lem3077338 (b : Prop) (a : Prop) : (a \/ b) = (term466 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3077341 (_32036 : nat) (_32037 : nat) : (term542 _32036 _32037) = (term544 _32036 _32037).
Proof. exact (@lem3077338 (term0 _32036 _32037) ((Nat.mul _32036 _32037) = (NUMERAL 0))). Qed.
Lemma lem3077344 (_32036 : nat) (_32037 : nat) (h1 : term237) : term544 _32036 _32037.
Proof. exact (EQ_MP (@lem3077341 _32036 _32037) (@lem3077336 _32036 _32037 h1)). Qed.
Lemma lem3077345 (x : type1606) (n : nat) (m : nat) (h1 : term237) : term545 x n m.
Proof. exact (@lem3077344 m (x n m) h1). Qed.
Lemma lem3077348 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : (term463 x n m) = (NUMERAL 0).
Proof. exact (@lem3077345 x n m h1 (@lem3077305 x m n h2 h3)). Qed.
Lemma lem3077349 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : term546 x n m.
Proof. exact (fun h0 : term547 x n m => @lem3077348 x m n h1 h2 h3). Qed.
Lemma lem3077351 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3077352 (x : type1606) (n : nat) (m : nat) : (term546 x n m) = ((term463 x n m) = (NUMERAL 0)).
Proof. exact (@lem3077351 ((term463 x n m) = (NUMERAL 0))). Qed.
Lemma lem3077353 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : (term463 x n m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3077352 x n m) (@lem3077349 x m n h1 h2 h3)). Qed.
Lemma lem3077354 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : term548 x n m.
Proof. exact (conj (@lem3076991 x m n h2 h3) (@lem3077353 x m n h1 h2 h3)). Qed.
Lemma lem3077356 (x : nat) (y : nat) (z : nat) : term497 x y z.
Proof. exact (EQ_MP (@lem3076978 x y z) (@lem3076957 y x z)). Qed.
Lemma lem3077357 (x : type1606) (m : nat) (n : nat) : term549 x m n.
Proof. exact (@lem3077356 (term463 x n m) n (NUMERAL 0)). Qed.
Lemma lem3077360 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : n = (NUMERAL 0).
Proof. exact (@lem3077357 x m n (@lem3077354 x m n h1 h2 h3)). Qed.
Lemma lem3077361 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : term550 n.
Proof. exact (fun h0 : term450 n => @lem3077360 x m n h1 h2 h3). Qed.
Lemma lem3077363 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3077364 (n : nat) : (term550 n) = (n = (NUMERAL 0)).
Proof. exact (@lem3077363 (n = (NUMERAL 0))). Qed.
Lemma lem3077365 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : n = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3077364 n) (@lem3077361 x m n h1 h2 h3)). Qed.
Lemma lem3077368 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3077370 (n : nat) : (term450 n) = (term551 n).
Proof. exact (@lem3077368 (n = (NUMERAL 0))). Qed.
Lemma lem3077373 (m : nat) (n : nat) (h1 : term272 m n) : term551 n.
Proof. exact (EQ_MP (@lem3077370 n) (@lem3076706 m n h1)). Qed.
Lemma lem3077376 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : False.
Proof. exact (@lem3077373 m n h3 (@lem3077365 x m n h1 h2 h3)). Qed.
Lemma lem3077377 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : term552.
Proof. exact (fun h0 : ~ False => @lem3077376 x m n h1 h2 h3). Qed.
Lemma lem3077379 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3077380 : term552 = False.
Proof. exact (@lem3077379 False). Qed.
Lemma lem3077381 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : False.
Proof. exact (EQ_MP (@lem3077380) (@lem3077377 x m n h1 h2 h3)). Qed.
Lemma lem3077382 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : term237 = False.
Proof. exact (prop_ext (fun h4 : term237 => @lem3077381 x m n h1 h2 h3) (fun h4 : False => @lem3076601 h1)). Qed.
Lemma lem3077383 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : False.
Proof. exact (EQ_MP (@lem3077382 x m n h1 h2 h3) (@lem3076601 h1)). Qed.
Lemma lem3077384 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : (term272 m n) = False.
Proof. exact (prop_ext (fun h4 : term272 m n => @lem3077383 x m n h1 h2 h3) (fun h4 : False => @lem3076579 m n h3)). Qed.
Lemma lem3077385 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : False.
Proof. exact (EQ_MP (@lem3077384 x m n h1 h2 h3) (@lem3076579 m n h3)). Qed.
Lemma lem3077386 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : (term440 x) = False.
Proof. exact (prop_ext (fun h4 : term440 x => @lem3077385 x m n h1 h2 h3) (fun h4 : False => @lem3076551 x h2)). Qed.
Lemma lem3077387 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : False.
Proof. exact (EQ_MP (@lem3077386 x m n h1 h2 h3) (@lem3076551 x h2)). Qed.
Lemma lem3077388 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : term237 = False.
Proof. exact (prop_ext (fun h4 : term237 => @lem3077387 x m n h1 h2 h3) (fun h4 : False => @lem3076490 h1)). Qed.
Lemma lem3077389 (x : type1606) (m : nat) (n : nat) (h1 : term237) (h2 : term440 x) (h3 : term272 m n) : False.
Proof. exact (EQ_MP (@lem3077388 x m n h1 h2 h3) (@lem3076490 h1)). Qed.
Lemma lem3077390 (m : nat) (x : type1606) (h1 : term237) (h2 : term283 m) (h3 : term440 x) : False.
Proof. exact (ex_elim (@lem3076459 m h2) (fun n : nat => fun h0 : term282 m n => @lem3077389 x m n h1 h3 h0)). Qed.
Lemma lem3077391 (x : type1606) (h1 : term237) (h2 : term243) (h3 : term440 x) : False.
Proof. exact (ex_elim (@lem3075963 h2) (fun m : nat => fun h0 : term288 m => @lem3077390 m x h1 h0 h3)). Qed.
Lemma lem3077392 (h1 : term239) (h2 : term237) (h3 : term243) : False.
Proof. exact (ex_elim (@lem3076457 h1) (fun x : type1606 => fun h0 : term442 x => @lem3077391 x h2 h3 h0)). Qed.
Lemma lem3077393 (h1 : term239) (h2 : term237) (h3 : term243) : term237 = False.
Proof. exact (prop_ext (fun h4 : term237 => @lem3077392 h1 h2 h3) (fun h4 : False => @lem3076031 h2)). Qed.
Lemma lem3077394 (h1 : term239) (h2 : term237) (h3 : term243) : False.
Proof. exact (EQ_MP (@lem3077393 h1 h2 h3) (@lem3076031 h2)). Qed.
Lemma lem3077395 (h1 : term237) (h2 : term243) : term248.
Proof. exact (fun h0 : term239 => @lem3077394 h0 h1 h2). Qed.
Lemma lem3077396 : term248 = term249.
Proof. exact (@lem69 term239). Qed.
Lemma lem3077397 (h1 : term237) (h2 : term243) : term249.
Proof. exact (EQ_MP (@lem3077396) (@lem3077395 h1 h2)). Qed.
Lemma lem3077398 (h1 : term243) : term252.
Proof. exact (fun h0 : term237 => @lem3077397 h0 h1). Qed.
Lemma lem3077399 : term254.
Proof. exact (fun h0 : term243 => @lem3077398 h0). Qed.
Lemma lem3077400 : term244.
Proof. exact (EQ_MP (@lem3075870) (@lem3077399)). Qed.
Lemma lem3077402 : term244.
Proof. exact (@lem3075667 (@lem3077400)). Qed.
Lemma lem3077403 (h1 : term243) : term251.
Proof. exact (@lem3077402 (@lem3075652 h1)). Qed.
Lemma lem3077404 (h1 : term237) (h2 : term243) : term248.
Proof. exact (@lem3077403 h2 (@lem3075635 h1)). Qed.
Lemma lem3077405 (h1 : term237) (h2 : term243) : False.
Proof. exact (@lem3077404 h1 h2 (@lem3075647)). Qed.
Lemma lem3077406 (h1 : term237) (h2 : term243) : term237 = False.
Proof. exact (prop_ext (fun h3 : term237 => @lem3077405 h1 h2) (fun h3 : False => @lem3075635 h1)). Qed.
Lemma lem3077407 (h1 : term237) (h2 : term243) : False.
Proof. exact (EQ_MP (@lem3077406 h1 h2) (@lem3075635 h1)). Qed.
Lemma lem3077408 (h1 : term237) (h2 : term243) : term243 = False.
Proof. exact (prop_ext (fun h3 : term243 => @lem3077407 h1 h2) (fun h3 : False => @lem3075652 h2)). Qed.
Lemma lem3077409 (h1 : term237) (h2 : term243) : False.
Proof. exact (EQ_MP (@lem3077408 h1 h2) (@lem3075652 h2)). Qed.
Lemma lem3077410 (h1 : term237) : term242.
Proof. exact (fun h0 : term243 => @lem3077409 h1 h0). Qed.
Lemma lem3077411 (h1 : term237) : term241.
Proof. exact (EQ_MP (@lem3075651) (@lem3077410 h1)). Qed.
Lemma lem3077423 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem3075618 m n) (@lem3075617 m n)). Qed.
Lemma lem3077425 (m : nat) (n : nat) (p : nat) : (term235 n m p) = (term236 m n p).
Proof. exact (EQ_MP (@lem3075633 m n p) (@lem3075632 m n p)). Qed.
Lemma lem3077426 (m : nat) (n : nat) : (term1 m n) = (term553 m n).
Proof. exact (@lem3077425 m term75 n). Qed.
Lemma lem3077429 (m : nat) (n : nat) : (term0 m n) = (term553 m n).
Proof. exact (TRANS (@lem3077423 m n) (@lem3077426 m n)). Qed.
Lemma lem3077432 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3077433 (m : nat) (n : nat) : (term554 m n) = (term555 m n).
Proof. exact (MK_COMB (@lem3077432) (@lem3077429 m n)). Qed.
Lemma lem3077435 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term229 m n).
Proof. exact (EQ_MP (@lem3075624 m n) (@lem3075623 m n)). Qed.
Lemma lem3077442 (m : nat) (n : nat) : (term260 m n) = (term556 m n).
Proof. exact (MK_COMB (@lem3077433 m n) (@lem3077435 m n)). Qed.
Lemma lem3077445 (m : nat) : (term261 m) = (term557 m).
Proof. exact (fun_ext (fun n : nat => @lem3077442 m n)). Qed.
Lemma lem3077446 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077447 (m : nat) : (term262 m) = (term558 m).
Proof. exact (MK_COMB (@lem3077446) (@lem3077445 m)). Qed.
Lemma lem3077452 : term263 = term559.
Proof. exact (fun_ext (fun m : nat => @lem3077447 m)). Qed.
Lemma lem3077453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077454 : term237 = term560.
Proof. exact (MK_COMB (@lem3077453) (@lem3077452)). Qed.
Lemma lem3077459 : term560 = term237.
Proof. exact (SYM (@lem3077454)). Qed.
Lemma lem3077493 (m : nat) (n : nat) : (term556 m n) = (term556 m n).
Proof. exact (eq_refl (term556 m n)). Qed.
Lemma lem3077494 (m : nat) : (term557 m) = (term557 m).
Proof. exact (fun_ext (fun n : nat => @lem3077493 m n)). Qed.
Lemma lem3077495 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077496 (m : nat) : (term558 m) = (term558 m).
Proof. exact (MK_COMB (@lem3077495) (@lem3077494 m)). Qed.
Lemma lem3077497 : term559 = term559.
Proof. exact (fun_ext (fun m : nat => @lem3077496 m)). Qed.
Lemma lem3077498 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077500 : term560 = term560.
Proof. exact (MK_COMB (@lem3077498) (@lem3077497)). Qed.
Lemma lem3077513 (m : nat) (n : nat) : (term556 m n) = (term556 m n).
Proof. exact (eq_refl (term556 m n)). Qed.
Lemma lem3077514 (m : nat) : (term557 m) = (term557 m).
Proof. exact (fun_ext (fun n : nat => @lem3077513 m n)). Qed.
Lemma lem3077515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077516 (m : nat) : (term558 m) = (term558 m).
Proof. exact (MK_COMB (@lem3077515) (@lem3077514 m)). Qed.
Lemma lem3077517 : term559 = term559.
Proof. exact (fun_ext (fun m : nat => @lem3077516 m)). Qed.
Lemma lem3077518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077519 : term560 = term560.
Proof. exact (MK_COMB (@lem3077518) (@lem3077517)). Qed.
Lemma lem3077520 : term560 = term560.
Proof. exact (TRANS (@lem3077500) (@lem3077519)). Qed.
Lemma lem3077521 (m : nat) (n : nat) : (term556 m n) = (term556 m n).
Proof. exact (eq_refl (term556 m n)). Qed.
Lemma lem3077522 (m : nat) : (term557 m) = (term557 m).
Proof. exact (fun_ext (fun n : nat => @lem3077521 m n)). Qed.
Lemma lem3077523 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077524 (m : nat) : (term558 m) = (term558 m).
Proof. exact (MK_COMB (@lem3077523) (@lem3077522 m)). Qed.
Lemma lem3077525 : term559 = term559.
Proof. exact (fun_ext (fun m : nat => @lem3077524 m)). Qed.
Lemma lem3077526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077527 : term560 = term560.
Proof. exact (MK_COMB (@lem3077526) (@lem3077525)). Qed.
Lemma lem3077554 : term560 = term560.
Proof. exact (TRANS (@lem3077520) (@lem3077527)). Qed.
Lemma lem3077583 (m : nat) (n : nat) : (term556 m n) = (term556 m n).
Proof. exact (eq_refl (term556 m n)). Qed.
Lemma lem3077584 (m : nat) : (term557 m) = (term557 m).
Proof. exact (fun_ext (fun n : nat => @lem3077583 m n)). Qed.
Lemma lem3077585 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077586 (m : nat) : (term558 m) = (term558 m).
Proof. exact (MK_COMB (@lem3077585) (@lem3077584 m)). Qed.
Lemma lem3077587 : term559 = term559.
Proof. exact (fun_ext (fun m : nat => @lem3077586 m)). Qed.
Lemma lem3077588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077589 : term560 = term560.
Proof. exact (MK_COMB (@lem3077588) (@lem3077587)). Qed.
Lemma lem3077592 : term560 = term560.
Proof. exact (TRANS (@lem3077554) (@lem3077589)). Qed.
Lemma lem3077594 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3077595 (m : nat) : (m = (NUMERAL 0)) = ((int_of_num m) = term58).
Proof. exact (@lem3077594 m (NUMERAL 0)). Qed.
Lemma lem3077598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3077599 (m : nat) : (term561 m) = (term562 m).
Proof. exact (MK_COMB (@lem3077598) (@lem3077595 m)). Qed.
Lemma lem3077601 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3077602 (n : nat) : (term563 n) = (term564 n).
Proof. exact (@lem3077601 term75 n). Qed.
Lemma lem3077603 (m : nat) (n : nat) : (term553 m n) = (term565 m n).
Proof. exact (MK_COMB (@lem3077599 m) (@lem3077602 n)). Qed.
Lemma lem3077604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3077605 (m : nat) (n : nat) : (term555 m n) = (term566 m n).
Proof. exact (MK_COMB (@lem3077604) (@lem3077603 m n)). Qed.
Lemma lem3077607 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3077608 (m : nat) : (m = (NUMERAL 0)) = ((int_of_num m) = term58).
Proof. exact (@lem3077607 m (NUMERAL 0)). Qed.
Lemma lem3077611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3077612 (m : nat) : (term561 m) = (term562 m).
Proof. exact (MK_COMB (@lem3077611) (@lem3077608 m)). Qed.
Lemma lem3077614 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3077615 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term58).
Proof. exact (@lem3077614 n (NUMERAL 0)). Qed.
Lemma lem3077618 (m : nat) (n : nat) : (term229 m n) = (term567 m n).
Proof. exact (MK_COMB (@lem3077612 m) (@lem3077615 n)). Qed.
Lemma lem3077619 (m : nat) (n : nat) : (term556 m n) = (term568 m n).
Proof. exact (MK_COMB (@lem3077605 m n) (@lem3077618 m n)). Qed.
Lemma lem3077620 (m : nat) : (term557 m) = (term569 m).
Proof. exact (fun_ext (fun n : nat => @lem3077619 m n)). Qed.
Lemma lem3077621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077622 (m : nat) : (term558 m) = (term570 m).
Proof. exact (MK_COMB (@lem3077621) (@lem3077620 m)). Qed.
Lemma lem3077623 : term559 = term571.
Proof. exact (fun_ext (fun m : nat => @lem3077622 m)). Qed.
Lemma lem3077624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3077625 : term560 = term572.
Proof. exact (MK_COMB (@lem3077624) (@lem3077623)). Qed.
Lemma lem3077626 : term560 = term572.
Proof. exact (TRANS (@lem3077592) (@lem3077625)). Qed.
Lemma lem3077627 (m : nat) : term25 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem3077628 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem3077629 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem3077628 m) (@lem3077627 m)). Qed.
Lemma lem3077630 (n : nat) : term25 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem3077631 (n : nat) : (term25 n) = (term26 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem3077632 (n : nat) : term26 n.
Proof. exact (EQ_MP (@lem3077631 n) (@lem3077630 n)). Qed.
Lemma lem3077633 (_32061 : int) (_32062 : int) : (term573 _32061 _32062) = (term574 _32061 _32062).
Proof. exact (@lem2318604 (term574 _32061 _32062)). Qed.
Lemma lem3077657 (_32061 : int) (_32062 : int) : (term575 _32061 _32062) = (term576 _32061 _32062).
Proof. exact (@lem17160 (_32061 = term58) (term577 _32062)). Qed.
Lemma lem3077664 (_32061 : int) (_32062 : int) : (term578 _32061 _32062) = (term579 _32061 _32062).
Proof. exact (@lem17160 (_32061 = term58) (_32062 = term58)). Qed.
Lemma lem3077665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3077666 (_32061 : int) (_32062 : int) : (term580 _32061 _32062) = (term581 _32061 _32062).
Proof. exact (MK_COMB (@lem3077665) (@lem3077657 _32061 _32062)). Qed.
Lemma lem3077667 (_32061 : int) (_32062 : int) : (term582 _32061 _32062) = (term583 _32061 _32062).
Proof. exact (MK_COMB (@lem3077666 _32061 _32062) (@lem3077664 _32061 _32062)). Qed.
Lemma lem3077668 (_32061 : int) (_32062 : int) : (term584 _32061 _32062) = (term582 _32061 _32062).
Proof. exact (@lem17160 (term585 _32061 _32062) (term586 _32061 _32062)). Qed.
Lemma lem3077669 (_32061 : int) (_32062 : int) : (term584 _32061 _32062) = (term583 _32061 _32062).
Proof. exact (TRANS (@lem3077668 _32061 _32062) (@lem3077667 _32061 _32062)). Qed.
Lemma lem3077671 (_32062 : int) : (term49 _32062) = (term49 _32062).
Proof. exact (eq_refl (term49 _32062)). Qed.
Lemma lem3077672 (_32061 : int) (_32062 : int) : (term587 _32061 _32062) = (term588 _32061 _32062).
Proof. exact (MK_COMB (@lem3077671 _32062) (@lem3077669 _32061 _32062)). Qed.
Lemma lem3077673 (_32061 : int) (_32062 : int) : (term589 _32061 _32062) = (term587 _32061 _32062).
Proof. exact (@lem17362 (term53 _32062) (term590 _32061 _32062)). Qed.
Lemma lem3077674 (_32061 : int) (_32062 : int) : (term589 _32061 _32062) = (term588 _32061 _32062).
Proof. exact (TRANS (@lem3077673 _32061 _32062) (@lem3077672 _32061 _32062)). Qed.
Lemma lem3077676 (_32061 : int) : (term49 _32061) = (term49 _32061).
Proof. exact (eq_refl (term49 _32061)). Qed.
Lemma lem3077677 (_32061 : int) (_32062 : int) : (term591 _32061 _32062) = (term592 _32061 _32062).
Proof. exact (MK_COMB (@lem3077676 _32061) (@lem3077674 _32061 _32062)). Qed.
Lemma lem3077678 (_32061 : int) (_32062 : int) : (term593 _32061 _32062) = (term591 _32061 _32062).
Proof. exact (@lem17362 (term53 _32061) (term594 _32061 _32062)). Qed.
Lemma lem3077710 (_32061 : int) (_32062 : int) : (term593 _32061 _32062) = (term592 _32061 _32062).
Proof. exact (TRANS (@lem3077678 _32061 _32062) (@lem3077677 _32061 _32062)). Qed.
Lemma lem3077713 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077714 (_32061 : int) : (term53 _32061) = (term57 _32061).
Proof. exact (@lem3077713 term58 _32061). Qed.
Lemma lem3077716 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077717 : term60 = term61.
Proof. exact (@lem3077716 (NUMERAL 0)). Qed.
Lemma lem3077718 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077719 : term62 = term63.
Proof. exact (MK_COMB (@lem3077718) (@lem3077717)). Qed.
Lemma lem3077720 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3077721 (_32061 : int) : (term57 _32061) = (term64 _32061).
Proof. exact (MK_COMB (@lem3077719) (@lem3077720 _32061)). Qed.
Lemma lem3077723 (_32061 : int) : (term53 _32061) = (term64 _32061).
Proof. exact (TRANS (@lem3077714 _32061) (@lem3077721 _32061)). Qed.
Lemma lem3077726 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077727 (_32062 : int) : (term53 _32062) = (term57 _32062).
Proof. exact (@lem3077726 term58 _32062). Qed.
Lemma lem3077729 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077730 : term60 = term61.
Proof. exact (@lem3077729 (NUMERAL 0)). Qed.
Lemma lem3077731 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077732 : term62 = term63.
Proof. exact (MK_COMB (@lem3077731) (@lem3077730)). Qed.
Lemma lem3077733 (_32062 : int) : (real_of_int _32062) = (real_of_int _32062).
Proof. exact (eq_refl (real_of_int _32062)). Qed.
Lemma lem3077734 (_32062 : int) : (term57 _32062) = (term64 _32062).
Proof. exact (MK_COMB (@lem3077732) (@lem3077733 _32062)). Qed.
Lemma lem3077736 (_32062 : int) : (term53 _32062) = (term64 _32062).
Proof. exact (TRANS (@lem3077727 _32062) (@lem3077734 _32062)). Qed.
Lemma lem3077738 (y : int) (x : int) : (term595 x y) = (term596 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3077739 (_32061 : int) : (term597 _32061) = (term598 _32061).
Proof. exact (@lem3077738 term58 _32061). Qed.
Lemma lem3077741 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077742 (_32061 : int) : (term599 _32061) = (term600 _32061).
Proof. exact (@lem3077741 (term67 _32061) term58). Qed.
Lemma lem3077744 (x : int) (y : int) : (term68 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3077745 (_32061 : int) : (term70 _32061) = (term71 _32061).
Proof. exact (@lem3077744 _32061 term72). Qed.
Lemma lem3077747 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077748 : term73 = term74.
Proof. exact (@lem3077747 term75). Qed.
Lemma lem3077749 (_32061 : int) : (term76 _32061) = (term76 _32061).
Proof. exact (eq_refl (term76 _32061)). Qed.
Lemma lem3077750 (_32061 : int) : (term71 _32061) = (term77 _32061).
Proof. exact (MK_COMB (@lem3077749 _32061) (@lem3077748)). Qed.
Lemma lem3077751 (_32061 : int) : (term70 _32061) = (term77 _32061).
Proof. exact (TRANS (@lem3077745 _32061) (@lem3077750 _32061)). Qed.
Lemma lem3077752 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077753 (_32061 : int) : (term78 _32061) = (term79 _32061).
Proof. exact (MK_COMB (@lem3077752) (@lem3077751 _32061)). Qed.
Lemma lem3077755 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077756 : term60 = term61.
Proof. exact (@lem3077755 (NUMERAL 0)). Qed.
Lemma lem3077757 (_32061 : int) : (term600 _32061) = (term601 _32061).
Proof. exact (MK_COMB (@lem3077753 _32061) (@lem3077756)). Qed.
Lemma lem3077758 (_32061 : int) : (term599 _32061) = (term601 _32061).
Proof. exact (TRANS (@lem3077742 _32061) (@lem3077757 _32061)). Qed.
Lemma lem3077759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3077760 (_32061 : int) : (term602 _32061) = (term603 _32061).
Proof. exact (MK_COMB (@lem3077759) (@lem3077758 _32061)). Qed.
Lemma lem3077762 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077763 (_32061 : int) : (term604 _32061) = (term605 _32061).
Proof. exact (@lem3077762 term606 _32061). Qed.
Lemma lem3077765 (x : int) (y : int) : (term68 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3077766 : term607 = term608.
Proof. exact (@lem3077765 term58 term72). Qed.
Lemma lem3077768 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077769 : term60 = term61.
Proof. exact (@lem3077768 (NUMERAL 0)). Qed.
Lemma lem3077770 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3077771 : term609 = term200.
Proof. exact (MK_COMB (@lem3077770) (@lem3077769)). Qed.
Lemma lem3077773 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077774 : term73 = term74.
Proof. exact (@lem3077773 term75). Qed.
Lemma lem3077775 : term608 = term610.
Proof. exact (MK_COMB (@lem3077771) (@lem3077774)). Qed.
Lemma lem3077776 : term607 = term610.
Proof. exact (TRANS (@lem3077766) (@lem3077775)). Qed.
Lemma lem3077777 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077778 : term611 = term612.
Proof. exact (MK_COMB (@lem3077777) (@lem3077776)). Qed.
Lemma lem3077779 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3077780 (_32061 : int) : (term605 _32061) = (term613 _32061).
Proof. exact (MK_COMB (@lem3077778) (@lem3077779 _32061)). Qed.
Lemma lem3077781 (_32061 : int) : (term604 _32061) = (term613 _32061).
Proof. exact (TRANS (@lem3077763 _32061) (@lem3077780 _32061)). Qed.
Lemma lem3077782 (_32061 : int) : (term598 _32061) = (term614 _32061).
Proof. exact (MK_COMB (@lem3077760 _32061) (@lem3077781 _32061)). Qed.
Lemma lem3077783 (_32061 : int) : (term597 _32061) = (term614 _32061).
Proof. exact (TRANS (@lem3077739 _32061) (@lem3077782 _32061)). Qed.
Lemma lem3077785 (y : int) (x : int) : (term35 x y) = (term65 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem3077786 (_32062 : int) : (term615 _32062) = (term616 _32062).
Proof. exact (@lem3077785 _32062 term72). Qed.
Lemma lem3077788 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077789 (_32062 : int) : (term616 _32062) = (term617 _32062).
Proof. exact (@lem3077788 (term67 _32062) term72). Qed.
Lemma lem3077791 (x : int) (y : int) : (term68 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3077792 (_32062 : int) : (term70 _32062) = (term71 _32062).
Proof. exact (@lem3077791 _32062 term72). Qed.
Lemma lem3077794 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077795 : term73 = term74.
Proof. exact (@lem3077794 term75). Qed.
Lemma lem3077796 (_32062 : int) : (term76 _32062) = (term76 _32062).
Proof. exact (eq_refl (term76 _32062)). Qed.
Lemma lem3077797 (_32062 : int) : (term71 _32062) = (term77 _32062).
Proof. exact (MK_COMB (@lem3077796 _32062) (@lem3077795)). Qed.
Lemma lem3077798 (_32062 : int) : (term70 _32062) = (term77 _32062).
Proof. exact (TRANS (@lem3077792 _32062) (@lem3077797 _32062)). Qed.
Lemma lem3077799 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077800 (_32062 : int) : (term78 _32062) = (term79 _32062).
Proof. exact (MK_COMB (@lem3077799) (@lem3077798 _32062)). Qed.
Lemma lem3077802 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077803 : term73 = term74.
Proof. exact (@lem3077802 term75). Qed.
Lemma lem3077804 (_32062 : int) : (term617 _32062) = (term618 _32062).
Proof. exact (MK_COMB (@lem3077800 _32062) (@lem3077803)). Qed.
Lemma lem3077805 (_32062 : int) : (term616 _32062) = (term618 _32062).
Proof. exact (TRANS (@lem3077789 _32062) (@lem3077804 _32062)). Qed.
Lemma lem3077806 (_32062 : int) : (term615 _32062) = (term618 _32062).
Proof. exact (TRANS (@lem3077786 _32062) (@lem3077805 _32062)). Qed.
Lemma lem3077807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3077808 (_32061 : int) : (term619 _32061) = (term620 _32061).
Proof. exact (MK_COMB (@lem3077807) (@lem3077783 _32061)). Qed.
Lemma lem3077809 (_32061 : int) (_32062 : int) : (term576 _32061 _32062) = (term621 _32061 _32062).
Proof. exact (MK_COMB (@lem3077808 _32061) (@lem3077806 _32062)). Qed.
Lemma lem3077811 (y : int) (x : int) : (term595 x y) = (term596 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3077812 (_32061 : int) : (term597 _32061) = (term598 _32061).
Proof. exact (@lem3077811 term58 _32061). Qed.
Lemma lem3077814 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077815 (_32061 : int) : (term599 _32061) = (term600 _32061).
Proof. exact (@lem3077814 (term67 _32061) term58). Qed.
Lemma lem3077817 (x : int) (y : int) : (term68 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3077818 (_32061 : int) : (term70 _32061) = (term71 _32061).
Proof. exact (@lem3077817 _32061 term72). Qed.
Lemma lem3077820 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077821 : term73 = term74.
Proof. exact (@lem3077820 term75). Qed.
Lemma lem3077822 (_32061 : int) : (term76 _32061) = (term76 _32061).
Proof. exact (eq_refl (term76 _32061)). Qed.
Lemma lem3077823 (_32061 : int) : (term71 _32061) = (term77 _32061).
Proof. exact (MK_COMB (@lem3077822 _32061) (@lem3077821)). Qed.
Lemma lem3077824 (_32061 : int) : (term70 _32061) = (term77 _32061).
Proof. exact (TRANS (@lem3077818 _32061) (@lem3077823 _32061)). Qed.
Lemma lem3077825 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077826 (_32061 : int) : (term78 _32061) = (term79 _32061).
Proof. exact (MK_COMB (@lem3077825) (@lem3077824 _32061)). Qed.
Lemma lem3077828 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077829 : term60 = term61.
Proof. exact (@lem3077828 (NUMERAL 0)). Qed.
Lemma lem3077830 (_32061 : int) : (term600 _32061) = (term601 _32061).
Proof. exact (MK_COMB (@lem3077826 _32061) (@lem3077829)). Qed.
Lemma lem3077831 (_32061 : int) : (term599 _32061) = (term601 _32061).
Proof. exact (TRANS (@lem3077815 _32061) (@lem3077830 _32061)). Qed.
Lemma lem3077832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3077833 (_32061 : int) : (term602 _32061) = (term603 _32061).
Proof. exact (MK_COMB (@lem3077832) (@lem3077831 _32061)). Qed.
Lemma lem3077835 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077836 (_32061 : int) : (term604 _32061) = (term605 _32061).
Proof. exact (@lem3077835 term606 _32061). Qed.
Lemma lem3077838 (x : int) (y : int) : (term68 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3077839 : term607 = term608.
Proof. exact (@lem3077838 term58 term72). Qed.
Lemma lem3077841 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077842 : term60 = term61.
Proof. exact (@lem3077841 (NUMERAL 0)). Qed.
Lemma lem3077843 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3077844 : term609 = term200.
Proof. exact (MK_COMB (@lem3077843) (@lem3077842)). Qed.
Lemma lem3077846 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077847 : term73 = term74.
Proof. exact (@lem3077846 term75). Qed.
Lemma lem3077848 : term608 = term610.
Proof. exact (MK_COMB (@lem3077844) (@lem3077847)). Qed.
Lemma lem3077849 : term607 = term610.
Proof. exact (TRANS (@lem3077839) (@lem3077848)). Qed.
Lemma lem3077850 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077851 : term611 = term612.
Proof. exact (MK_COMB (@lem3077850) (@lem3077849)). Qed.
Lemma lem3077852 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3077853 (_32061 : int) : (term605 _32061) = (term613 _32061).
Proof. exact (MK_COMB (@lem3077851) (@lem3077852 _32061)). Qed.
Lemma lem3077854 (_32061 : int) : (term604 _32061) = (term613 _32061).
Proof. exact (TRANS (@lem3077836 _32061) (@lem3077853 _32061)). Qed.
Lemma lem3077855 (_32061 : int) : (term598 _32061) = (term614 _32061).
Proof. exact (MK_COMB (@lem3077833 _32061) (@lem3077854 _32061)). Qed.
Lemma lem3077856 (_32061 : int) : (term597 _32061) = (term614 _32061).
Proof. exact (TRANS (@lem3077812 _32061) (@lem3077855 _32061)). Qed.
Lemma lem3077858 (y : int) (x : int) : (term595 x y) = (term596 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3077859 (_32062 : int) : (term597 _32062) = (term598 _32062).
Proof. exact (@lem3077858 term58 _32062). Qed.
Lemma lem3077861 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077862 (_32062 : int) : (term599 _32062) = (term600 _32062).
Proof. exact (@lem3077861 (term67 _32062) term58). Qed.
Lemma lem3077864 (x : int) (y : int) : (term68 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3077865 (_32062 : int) : (term70 _32062) = (term71 _32062).
Proof. exact (@lem3077864 _32062 term72). Qed.
Lemma lem3077867 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077868 : term73 = term74.
Proof. exact (@lem3077867 term75). Qed.
Lemma lem3077869 (_32062 : int) : (term76 _32062) = (term76 _32062).
Proof. exact (eq_refl (term76 _32062)). Qed.
Lemma lem3077870 (_32062 : int) : (term71 _32062) = (term77 _32062).
Proof. exact (MK_COMB (@lem3077869 _32062) (@lem3077868)). Qed.
Lemma lem3077871 (_32062 : int) : (term70 _32062) = (term77 _32062).
Proof. exact (TRANS (@lem3077865 _32062) (@lem3077870 _32062)). Qed.
Lemma lem3077872 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077873 (_32062 : int) : (term78 _32062) = (term79 _32062).
Proof. exact (MK_COMB (@lem3077872) (@lem3077871 _32062)). Qed.
Lemma lem3077875 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077876 : term60 = term61.
Proof. exact (@lem3077875 (NUMERAL 0)). Qed.
Lemma lem3077877 (_32062 : int) : (term600 _32062) = (term601 _32062).
Proof. exact (MK_COMB (@lem3077873 _32062) (@lem3077876)). Qed.
Lemma lem3077878 (_32062 : int) : (term599 _32062) = (term601 _32062).
Proof. exact (TRANS (@lem3077862 _32062) (@lem3077877 _32062)). Qed.
Lemma lem3077879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3077880 (_32062 : int) : (term602 _32062) = (term603 _32062).
Proof. exact (MK_COMB (@lem3077879) (@lem3077878 _32062)). Qed.
Lemma lem3077882 (x : int) (y : int) : (int_le x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3077883 (_32062 : int) : (term604 _32062) = (term605 _32062).
Proof. exact (@lem3077882 term606 _32062). Qed.
Lemma lem3077885 (x : int) (y : int) : (term68 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3077886 : term607 = term608.
Proof. exact (@lem3077885 term58 term72). Qed.
Lemma lem3077888 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077889 : term60 = term61.
Proof. exact (@lem3077888 (NUMERAL 0)). Qed.
Lemma lem3077890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3077891 : term609 = term200.
Proof. exact (MK_COMB (@lem3077890) (@lem3077889)). Qed.
Lemma lem3077893 (n : nat) : (term59 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3077894 : term73 = term74.
Proof. exact (@lem3077893 term75). Qed.
Lemma lem3077895 : term608 = term610.
Proof. exact (MK_COMB (@lem3077891) (@lem3077894)). Qed.
Lemma lem3077896 : term607 = term610.
Proof. exact (TRANS (@lem3077886) (@lem3077895)). Qed.
Lemma lem3077897 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3077898 : term611 = term612.
Proof. exact (MK_COMB (@lem3077897) (@lem3077896)). Qed.
Lemma lem3077899 (_32062 : int) : (real_of_int _32062) = (real_of_int _32062).
Proof. exact (eq_refl (real_of_int _32062)). Qed.
Lemma lem3077900 (_32062 : int) : (term605 _32062) = (term613 _32062).
Proof. exact (MK_COMB (@lem3077898) (@lem3077899 _32062)). Qed.
Lemma lem3077901 (_32062 : int) : (term604 _32062) = (term613 _32062).
Proof. exact (TRANS (@lem3077883 _32062) (@lem3077900 _32062)). Qed.
Lemma lem3077902 (_32062 : int) : (term598 _32062) = (term614 _32062).
Proof. exact (MK_COMB (@lem3077880 _32062) (@lem3077901 _32062)). Qed.
Lemma lem3077903 (_32062 : int) : (term597 _32062) = (term614 _32062).
Proof. exact (TRANS (@lem3077859 _32062) (@lem3077902 _32062)). Qed.
Lemma lem3077904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3077905 (_32061 : int) : (term619 _32061) = (term620 _32061).
Proof. exact (MK_COMB (@lem3077904) (@lem3077856 _32061)). Qed.
Lemma lem3077906 (_32061 : int) (_32062 : int) : (term579 _32061 _32062) = (term622 _32061 _32062).
Proof. exact (MK_COMB (@lem3077905 _32061) (@lem3077903 _32062)). Qed.
Lemma lem3077907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3077908 (_32061 : int) (_32062 : int) : (term581 _32061 _32062) = (term623 _32061 _32062).
Proof. exact (MK_COMB (@lem3077907) (@lem3077809 _32061 _32062)). Qed.
Lemma lem3077909 (_32061 : int) (_32062 : int) : (term583 _32061 _32062) = (term624 _32061 _32062).
Proof. exact (MK_COMB (@lem3077908 _32061 _32062) (@lem3077906 _32061 _32062)). Qed.
Lemma lem3077910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3077911 (_32062 : int) : (term49 _32062) = (term83 _32062).
Proof. exact (MK_COMB (@lem3077910) (@lem3077736 _32062)). Qed.
Lemma lem3077912 (_32061 : int) (_32062 : int) : (term588 _32061 _32062) = (term625 _32061 _32062).
Proof. exact (MK_COMB (@lem3077911 _32062) (@lem3077909 _32061 _32062)). Qed.
Lemma lem3077913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3077914 (_32061 : int) : (term49 _32061) = (term83 _32061).
Proof. exact (MK_COMB (@lem3077913) (@lem3077723 _32061)). Qed.
Lemma lem3077915 (_32061 : int) (_32062 : int) : (term592 _32061 _32062) = (term626 _32061 _32062).
Proof. exact (MK_COMB (@lem3077914 _32061) (@lem3077912 _32061 _32062)). Qed.
Lemma lem3077916 (_32061 : int) (_32062 : int) : (term593 _32061 _32062) = (term626 _32061 _32062).
Proof. exact (TRANS (@lem3077710 _32061 _32062) (@lem3077915 _32061 _32062)). Qed.
Lemma lem3077920 (t : Prop) : (term86 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3078006 (_32061 : int) (_32062 : int) : (term627 _32061 _32062) = (term626 _32061 _32062).
Proof. exact (@lem3077920 (term626 _32061 _32062)). Qed.
Lemma lem3078007 (_32061 : int) : (term64 _32061) = (term88 _32061).
Proof. exact (@lem1988287 (real_of_int _32061) term61). Qed.
Lemma lem3078013 (_32061 : int) : (term89 _32061) = (term90 _32061).
Proof. exact (@lem1982792 (real_of_int _32061) term61). Qed.
Lemma lem3078015 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078016 : term61 = term92.
Proof. exact (@lem3078015 (NUMERAL 0)). Qed.
Lemma lem3078018 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078019 : term95 = term96.
Proof. exact (@lem3078018 term75). Qed.
Lemma lem3078020 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078021 : term97 = term98.
Proof. exact (MK_COMB (@lem3078020) (@lem3078019)). Qed.
Lemma lem3078022 : term99 = term100.
Proof. exact (MK_COMB (@lem3078021) (@lem3078016)). Qed.
Lemma lem3078023 : term100 = term101.
Proof. exact (@lem1981613 term95 term61 term74 term74). Qed.
Lemma lem3078025 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078026 : term104 = term105.
Proof. exact (@lem3078025 term75 term75). Qed.
Lemma lem3078027 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078028 : term107 = term75.
Proof. exact (EQ_MP (@lem3078027) (@lem940073)). Qed.
Lemma lem3078029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078030 : term105 = term74.
Proof. exact (MK_COMB (@lem3078029) (@lem3078028)). Qed.
Lemma lem3078031 : term104 = term74.
Proof. exact (TRANS (@lem3078026) (@lem3078030)). Qed.
Lemma lem3078033 (x : nat) : (term108 x) = term61.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3078034 : term99 = term61.
Proof. exact (@lem3078033 term75). Qed.
Lemma lem3078035 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078036 : term109 = term110.
Proof. exact (MK_COMB (@lem3078035) (@lem3078034)). Qed.
Lemma lem3078037 : term101 = term92.
Proof. exact (MK_COMB (@lem3078036) (@lem3078031)). Qed.
Lemma lem3078038 : term100 = term92.
Proof. exact (TRANS (@lem3078023) (@lem3078037)). Qed.
Lemma lem3078039 : term99 = term92.
Proof. exact (TRANS (@lem3078022) (@lem3078038)). Qed.
Lemma lem3078041 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078042 : term92 = term61.
Proof. exact (@lem3078041 term61). Qed.
Lemma lem3078043 : term99 = term61.
Proof. exact (TRANS (@lem3078039) (@lem3078042)). Qed.
Lemma lem3078044 (_32061 : int) : (term76 _32061) = (term76 _32061).
Proof. exact (eq_refl (term76 _32061)). Qed.
Lemma lem3078045 (_32061 : int) : (term90 _32061) = (term112 _32061).
Proof. exact (MK_COMB (@lem3078044 _32061) (@lem3078043)). Qed.
Lemma lem3078046 (_32061 : int) : (term112 _32061) = (real_of_int _32061).
Proof. exact (@lem1982723 (real_of_int _32061)). Qed.
Lemma lem3078047 (_32061 : int) : (term90 _32061) = (real_of_int _32061).
Proof. exact (TRANS (@lem3078045 _32061) (@lem3078046 _32061)). Qed.
Lemma lem3078049 (_32061 : int) : (term89 _32061) = (real_of_int _32061).
Proof. exact (TRANS (@lem3078013 _32061) (@lem3078047 _32061)). Qed.
Lemma lem3078050 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078051 (_32061 : int) : (term113 _32061) = (term114 _32061).
Proof. exact (MK_COMB (@lem3078050) (@lem3078049 _32061)). Qed.
Lemma lem3078052 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078053 (_32061 : int) : (term88 _32061) = (term115 _32061).
Proof. exact (MK_COMB (@lem3078051 _32061) (@lem3078052)). Qed.
Lemma lem3078054 (_32061 : int) : (term64 _32061) = (term115 _32061).
Proof. exact (TRANS (@lem3078007 _32061) (@lem3078053 _32061)). Qed.
Lemma lem3078055 (_32062 : int) : (term64 _32062) = (term88 _32062).
Proof. exact (@lem1988287 (real_of_int _32062) term61). Qed.
Lemma lem3078061 (_32062 : int) : (term89 _32062) = (term90 _32062).
Proof. exact (@lem1982792 (real_of_int _32062) term61). Qed.
Lemma lem3078063 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078064 : term61 = term92.
Proof. exact (@lem3078063 (NUMERAL 0)). Qed.
Lemma lem3078066 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078067 : term95 = term96.
Proof. exact (@lem3078066 term75). Qed.
Lemma lem3078068 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078069 : term97 = term98.
Proof. exact (MK_COMB (@lem3078068) (@lem3078067)). Qed.
Lemma lem3078070 : term99 = term100.
Proof. exact (MK_COMB (@lem3078069) (@lem3078064)). Qed.
Lemma lem3078071 : term100 = term101.
Proof. exact (@lem1981613 term95 term61 term74 term74). Qed.
Lemma lem3078073 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078074 : term104 = term105.
Proof. exact (@lem3078073 term75 term75). Qed.
Lemma lem3078075 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078076 : term107 = term75.
Proof. exact (EQ_MP (@lem3078075) (@lem940073)). Qed.
Lemma lem3078077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078078 : term105 = term74.
Proof. exact (MK_COMB (@lem3078077) (@lem3078076)). Qed.
Lemma lem3078079 : term104 = term74.
Proof. exact (TRANS (@lem3078074) (@lem3078078)). Qed.
Lemma lem3078081 (x : nat) : (term108 x) = term61.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3078082 : term99 = term61.
Proof. exact (@lem3078081 term75). Qed.
Lemma lem3078083 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078084 : term109 = term110.
Proof. exact (MK_COMB (@lem3078083) (@lem3078082)). Qed.
Lemma lem3078085 : term101 = term92.
Proof. exact (MK_COMB (@lem3078084) (@lem3078079)). Qed.
Lemma lem3078086 : term100 = term92.
Proof. exact (TRANS (@lem3078071) (@lem3078085)). Qed.
Lemma lem3078087 : term99 = term92.
Proof. exact (TRANS (@lem3078070) (@lem3078086)). Qed.
Lemma lem3078089 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078090 : term92 = term61.
Proof. exact (@lem3078089 term61). Qed.
Lemma lem3078091 : term99 = term61.
Proof. exact (TRANS (@lem3078087) (@lem3078090)). Qed.
Lemma lem3078092 (_32062 : int) : (term76 _32062) = (term76 _32062).
Proof. exact (eq_refl (term76 _32062)). Qed.
Lemma lem3078093 (_32062 : int) : (term90 _32062) = (term112 _32062).
Proof. exact (MK_COMB (@lem3078092 _32062) (@lem3078091)). Qed.
Lemma lem3078094 (_32062 : int) : (term112 _32062) = (real_of_int _32062).
Proof. exact (@lem1982723 (real_of_int _32062)). Qed.
Lemma lem3078095 (_32062 : int) : (term90 _32062) = (real_of_int _32062).
Proof. exact (TRANS (@lem3078093 _32062) (@lem3078094 _32062)). Qed.
Lemma lem3078097 (_32062 : int) : (term89 _32062) = (real_of_int _32062).
Proof. exact (TRANS (@lem3078061 _32062) (@lem3078095 _32062)). Qed.
Lemma lem3078098 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078099 (_32062 : int) : (term113 _32062) = (term114 _32062).
Proof. exact (MK_COMB (@lem3078098) (@lem3078097 _32062)). Qed.
Lemma lem3078100 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078101 (_32062 : int) : (term88 _32062) = (term115 _32062).
Proof. exact (MK_COMB (@lem3078099 _32062) (@lem3078100)). Qed.
Lemma lem3078102 (_32062 : int) : (term64 _32062) = (term115 _32062).
Proof. exact (TRANS (@lem3078055 _32062) (@lem3078101 _32062)). Qed.
Lemma lem3078103 (_32061 : int) : (term601 _32061) = (term628 _32061).
Proof. exact (@lem1988287 term61 (term77 _32061)). Qed.
Lemma lem3078115 (_32061 : int) : (term629 _32061) = (term630 _32061).
Proof. exact (@lem1982792 term61 (term77 _32061)). Qed.
Lemma lem3078116 (_32061 : int) : (term119 _32061) = (term120 _32061).
Proof. exact (@lem1982781 (real_of_int _32061) term95 term74). Qed.
Lemma lem3078118 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078119 : term74 = term121.
Proof. exact (@lem3078118 term75). Qed.
Lemma lem3078121 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078122 : term95 = term96.
Proof. exact (@lem3078121 term75). Qed.
Lemma lem3078123 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078124 : term97 = term98.
Proof. exact (MK_COMB (@lem3078123) (@lem3078122)). Qed.
Lemma lem3078125 : term122 = term123.
Proof. exact (MK_COMB (@lem3078124) (@lem3078119)). Qed.
Lemma lem3078126 : term123 = term124.
Proof. exact (@lem1981613 term95 term74 term74 term74). Qed.
Lemma lem3078128 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078129 : term104 = term105.
Proof. exact (@lem3078128 term75 term75). Qed.
Lemma lem3078130 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078131 : term107 = term75.
Proof. exact (EQ_MP (@lem3078130) (@lem940073)). Qed.
Lemma lem3078132 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078133 : term105 = term74.
Proof. exact (MK_COMB (@lem3078132) (@lem3078131)). Qed.
Lemma lem3078134 : term104 = term74.
Proof. exact (TRANS (@lem3078129) (@lem3078133)). Qed.
Lemma lem3078136 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3078137 : term122 = term127.
Proof. exact (@lem3078136 term75 term75). Qed.
Lemma lem3078138 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078139 : term107 = term75.
Proof. exact (EQ_MP (@lem3078138) (@lem940073)). Qed.
Lemma lem3078140 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078141 : term105 = term74.
Proof. exact (MK_COMB (@lem3078140) (@lem3078139)). Qed.
Lemma lem3078142 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3078143 : term127 = term95.
Proof. exact (MK_COMB (@lem3078142) (@lem3078141)). Qed.
Lemma lem3078144 : term122 = term95.
Proof. exact (TRANS (@lem3078137) (@lem3078143)). Qed.
Lemma lem3078145 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078146 : term128 = term129.
Proof. exact (MK_COMB (@lem3078145) (@lem3078144)). Qed.
Lemma lem3078147 : term124 = term96.
Proof. exact (MK_COMB (@lem3078146) (@lem3078134)). Qed.
Lemma lem3078148 : term123 = term96.
Proof. exact (TRANS (@lem3078126) (@lem3078147)). Qed.
Lemma lem3078149 : term122 = term96.
Proof. exact (TRANS (@lem3078125) (@lem3078148)). Qed.
Lemma lem3078151 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078152 : term96 = term95.
Proof. exact (@lem3078151 term95). Qed.
Lemma lem3078153 : term122 = term95.
Proof. exact (TRANS (@lem3078149) (@lem3078152)). Qed.
Lemma lem3078156 (_32061 : int) : (term130 _32061) = (term130 _32061).
Proof. exact (eq_refl (term130 _32061)). Qed.
Lemma lem3078157 (_32061 : int) : (term120 _32061) = (term131 _32061).
Proof. exact (MK_COMB (@lem3078156 _32061) (@lem3078153)). Qed.
Lemma lem3078158 (_32061 : int) : (term119 _32061) = (term131 _32061).
Proof. exact (TRANS (@lem3078116 _32061) (@lem3078157 _32061)). Qed.
Lemma lem3078159 : term200 = term200.
Proof. exact (eq_refl term200). Qed.
Lemma lem3078160 (_32061 : int) : (term630 _32061) = (term631 _32061).
Proof. exact (MK_COMB (@lem3078159) (@lem3078158 _32061)). Qed.
Lemma lem3078161 (_32061 : int) : (term631 _32061) = (term131 _32061).
Proof. exact (@lem1982721 (term131 _32061)). Qed.
Lemma lem3078162 (_32061 : int) : (term630 _32061) = (term131 _32061).
Proof. exact (TRANS (@lem3078160 _32061) (@lem3078161 _32061)). Qed.
Lemma lem3078164 (_32061 : int) : (term629 _32061) = (term131 _32061).
Proof. exact (TRANS (@lem3078115 _32061) (@lem3078162 _32061)). Qed.
Lemma lem3078165 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078166 (_32061 : int) : (term632 _32061) = (term633 _32061).
Proof. exact (MK_COMB (@lem3078165) (@lem3078164 _32061)). Qed.
Lemma lem3078167 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078168 (_32061 : int) : (term628 _32061) = (term634 _32061).
Proof. exact (MK_COMB (@lem3078166 _32061) (@lem3078167)). Qed.
Lemma lem3078169 (_32061 : int) : (term601 _32061) = (term634 _32061).
Proof. exact (TRANS (@lem3078103 _32061) (@lem3078168 _32061)). Qed.
Lemma lem3078170 (_32061 : int) : (term613 _32061) = (term635 _32061).
Proof. exact (@lem1988287 (real_of_int _32061) term610). Qed.
Lemma lem3078177 : term610 = term74.
Proof. exact (@lem1982721 term74). Qed.
Lemma lem3078180 (_32061 : int) : (term636 _32061) = (term636 _32061).
Proof. exact (eq_refl (term636 _32061)). Qed.
Lemma lem3078181 (_32061 : int) : (term637 _32061) = (term638 _32061).
Proof. exact (MK_COMB (@lem3078180 _32061) (@lem3078177)). Qed.
Lemma lem3078182 (_32061 : int) : (term638 _32061) = (term639 _32061).
Proof. exact (@lem1982792 (real_of_int _32061) term74). Qed.
Lemma lem3078184 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078185 : term74 = term121.
Proof. exact (@lem3078184 term75). Qed.
Lemma lem3078187 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078188 : term95 = term96.
Proof. exact (@lem3078187 term75). Qed.
Lemma lem3078189 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078190 : term97 = term98.
Proof. exact (MK_COMB (@lem3078189) (@lem3078188)). Qed.
Lemma lem3078191 : term122 = term123.
Proof. exact (MK_COMB (@lem3078190) (@lem3078185)). Qed.
Lemma lem3078192 : term123 = term124.
Proof. exact (@lem1981613 term95 term74 term74 term74). Qed.
Lemma lem3078194 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078195 : term104 = term105.
Proof. exact (@lem3078194 term75 term75). Qed.
Lemma lem3078196 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078197 : term107 = term75.
Proof. exact (EQ_MP (@lem3078196) (@lem940073)). Qed.
Lemma lem3078198 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078199 : term105 = term74.
Proof. exact (MK_COMB (@lem3078198) (@lem3078197)). Qed.
Lemma lem3078200 : term104 = term74.
Proof. exact (TRANS (@lem3078195) (@lem3078199)). Qed.
Lemma lem3078202 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3078203 : term122 = term127.
Proof. exact (@lem3078202 term75 term75). Qed.
Lemma lem3078204 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078205 : term107 = term75.
Proof. exact (EQ_MP (@lem3078204) (@lem940073)). Qed.
Lemma lem3078206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078207 : term105 = term74.
Proof. exact (MK_COMB (@lem3078206) (@lem3078205)). Qed.
Lemma lem3078208 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3078209 : term127 = term95.
Proof. exact (MK_COMB (@lem3078208) (@lem3078207)). Qed.
Lemma lem3078210 : term122 = term95.
Proof. exact (TRANS (@lem3078203) (@lem3078209)). Qed.
Lemma lem3078211 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078212 : term128 = term129.
Proof. exact (MK_COMB (@lem3078211) (@lem3078210)). Qed.
Lemma lem3078213 : term124 = term96.
Proof. exact (MK_COMB (@lem3078212) (@lem3078200)). Qed.
Lemma lem3078214 : term123 = term96.
Proof. exact (TRANS (@lem3078192) (@lem3078213)). Qed.
Lemma lem3078215 : term122 = term96.
Proof. exact (TRANS (@lem3078191) (@lem3078214)). Qed.
Lemma lem3078217 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078218 : term96 = term95.
Proof. exact (@lem3078217 term95). Qed.
Lemma lem3078219 : term122 = term95.
Proof. exact (TRANS (@lem3078215) (@lem3078218)). Qed.
Lemma lem3078220 (_32061 : int) : (term76 _32061) = (term76 _32061).
Proof. exact (eq_refl (term76 _32061)). Qed.
Lemma lem3078223 (_32061 : int) : (term639 _32061) = (term640 _32061).
Proof. exact (MK_COMB (@lem3078220 _32061) (@lem3078219)). Qed.
Lemma lem3078224 (_32061 : int) : (term638 _32061) = (term640 _32061).
Proof. exact (TRANS (@lem3078182 _32061) (@lem3078223 _32061)). Qed.
Lemma lem3078225 (_32061 : int) : (term637 _32061) = (term640 _32061).
Proof. exact (TRANS (@lem3078181 _32061) (@lem3078224 _32061)). Qed.
Lemma lem3078226 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078227 (_32061 : int) : (term641 _32061) = (term642 _32061).
Proof. exact (MK_COMB (@lem3078226) (@lem3078225 _32061)). Qed.
Lemma lem3078228 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078229 (_32061 : int) : (term635 _32061) = (term643 _32061).
Proof. exact (MK_COMB (@lem3078227 _32061) (@lem3078228)). Qed.
Lemma lem3078230 (_32061 : int) : (term613 _32061) = (term643 _32061).
Proof. exact (TRANS (@lem3078170 _32061) (@lem3078229 _32061)). Qed.
Lemma lem3078231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078232 (_32061 : int) : (term603 _32061) = (term644 _32061).
Proof. exact (MK_COMB (@lem3078231) (@lem3078169 _32061)). Qed.
Lemma lem3078233 (_32061 : int) : (term614 _32061) = (term645 _32061).
Proof. exact (MK_COMB (@lem3078232 _32061) (@lem3078230 _32061)). Qed.
Lemma lem3078234 (_32062 : int) : (term618 _32062) = (term646 _32062).
Proof. exact (@lem1988287 term74 (term77 _32062)). Qed.
Lemma lem3078246 (_32062 : int) : (term647 _32062) = (term648 _32062).
Proof. exact (@lem1982792 term74 (term77 _32062)). Qed.
Lemma lem3078247 (_32062 : int) : (term119 _32062) = (term120 _32062).
Proof. exact (@lem1982781 (real_of_int _32062) term95 term74). Qed.
Lemma lem3078249 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078250 : term74 = term121.
Proof. exact (@lem3078249 term75). Qed.
Lemma lem3078252 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078253 : term95 = term96.
Proof. exact (@lem3078252 term75). Qed.
Lemma lem3078254 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078255 : term97 = term98.
Proof. exact (MK_COMB (@lem3078254) (@lem3078253)). Qed.
Lemma lem3078256 : term122 = term123.
Proof. exact (MK_COMB (@lem3078255) (@lem3078250)). Qed.
Lemma lem3078257 : term123 = term124.
Proof. exact (@lem1981613 term95 term74 term74 term74). Qed.
Lemma lem3078259 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078260 : term104 = term105.
Proof. exact (@lem3078259 term75 term75). Qed.
Lemma lem3078261 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078262 : term107 = term75.
Proof. exact (EQ_MP (@lem3078261) (@lem940073)). Qed.
Lemma lem3078263 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078264 : term105 = term74.
Proof. exact (MK_COMB (@lem3078263) (@lem3078262)). Qed.
Lemma lem3078265 : term104 = term74.
Proof. exact (TRANS (@lem3078260) (@lem3078264)). Qed.
Lemma lem3078267 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3078268 : term122 = term127.
Proof. exact (@lem3078267 term75 term75). Qed.
Lemma lem3078269 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078270 : term107 = term75.
Proof. exact (EQ_MP (@lem3078269) (@lem940073)). Qed.
Lemma lem3078271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078272 : term105 = term74.
Proof. exact (MK_COMB (@lem3078271) (@lem3078270)). Qed.
Lemma lem3078273 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3078274 : term127 = term95.
Proof. exact (MK_COMB (@lem3078273) (@lem3078272)). Qed.
Lemma lem3078275 : term122 = term95.
Proof. exact (TRANS (@lem3078268) (@lem3078274)). Qed.
Lemma lem3078276 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078277 : term128 = term129.
Proof. exact (MK_COMB (@lem3078276) (@lem3078275)). Qed.
Lemma lem3078278 : term124 = term96.
Proof. exact (MK_COMB (@lem3078277) (@lem3078265)). Qed.
Lemma lem3078279 : term123 = term96.
Proof. exact (TRANS (@lem3078257) (@lem3078278)). Qed.
Lemma lem3078280 : term122 = term96.
Proof. exact (TRANS (@lem3078256) (@lem3078279)). Qed.
Lemma lem3078282 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078283 : term96 = term95.
Proof. exact (@lem3078282 term95). Qed.
Lemma lem3078284 : term122 = term95.
Proof. exact (TRANS (@lem3078280) (@lem3078283)). Qed.
Lemma lem3078287 (_32062 : int) : (term130 _32062) = (term130 _32062).
Proof. exact (eq_refl (term130 _32062)). Qed.
Lemma lem3078288 (_32062 : int) : (term120 _32062) = (term131 _32062).
Proof. exact (MK_COMB (@lem3078287 _32062) (@lem3078284)). Qed.
Lemma lem3078289 (_32062 : int) : (term119 _32062) = (term131 _32062).
Proof. exact (TRANS (@lem3078247 _32062) (@lem3078288 _32062)). Qed.
Lemma lem3078290 : term649 = term649.
Proof. exact (eq_refl term649). Qed.
Lemma lem3078291 (_32062 : int) : (term648 _32062) = (term650 _32062).
Proof. exact (MK_COMB (@lem3078290) (@lem3078289 _32062)). Qed.
Lemma lem3078292 (_32062 : int) : (term650 _32062) = (term651 _32062).
Proof. exact (@lem1982757 (term140 _32062) term74 term95). Qed.
Lemma lem3078294 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078295 : term95 = term96.
Proof. exact (@lem3078294 term75). Qed.
Lemma lem3078297 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078298 : term74 = term121.
Proof. exact (@lem3078297 term75). Qed.
Lemma lem3078299 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3078300 : term649 = term652.
Proof. exact (MK_COMB (@lem3078299) (@lem3078298)). Qed.
Lemma lem3078301 : term653 = term654.
Proof. exact (MK_COMB (@lem3078300) (@lem3078295)). Qed.
Lemma lem3078302 : term655.
Proof. exact (@lem1981473 term74 term74 term95 term74 term61 term74). Qed.
Lemma lem3078304 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3078305 : term150 = term156.
Proof. exact (@lem3078304 (NUMERAL 0) term75). Qed.
Lemma lem3078306 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3078307 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3078308 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3078307 h1) (fun h1 : term156 = True => @lem3078306)). Qed.
Lemma lem3078309 : term156 = True.
Proof. exact (EQ_MP (@lem3078308) (@lem3078306)). Qed.
Lemma lem3078310 : term150 = True.
Proof. exact (TRANS (@lem3078305) (@lem3078309)). Qed.
Lemma lem3078311 : True = term150.
Proof. exact (SYM (@lem3078310)). Qed.
Lemma lem3078312 : term150.
Proof. exact (EQ_MP (@lem3078311) (@lem0)). Qed.
Lemma lem3078313 : term656.
Proof. exact (@lem3078302 (@lem3078312)). Qed.
Lemma lem3078315 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3078316 : term150 = term156.
Proof. exact (@lem3078315 (NUMERAL 0) term75). Qed.
Lemma lem3078317 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3078318 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3078319 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3078318 h1) (fun h1 : term156 = True => @lem3078317)). Qed.
Lemma lem3078320 : term156 = True.
Proof. exact (EQ_MP (@lem3078319) (@lem3078317)). Qed.
Lemma lem3078321 : term150 = True.
Proof. exact (TRANS (@lem3078316) (@lem3078320)). Qed.
Lemma lem3078322 : True = term150.
Proof. exact (SYM (@lem3078321)). Qed.
Lemma lem3078323 : term150.
Proof. exact (EQ_MP (@lem3078322) (@lem0)). Qed.
Lemma lem3078324 : term657.
Proof. exact (@lem3078313 (@lem3078323)). Qed.
Lemma lem3078326 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3078327 : term150 = term156.
Proof. exact (@lem3078326 (NUMERAL 0) term75). Qed.
Lemma lem3078328 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3078329 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3078330 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3078329 h1) (fun h1 : term156 = True => @lem3078328)). Qed.
Lemma lem3078331 : term156 = True.
Proof. exact (EQ_MP (@lem3078330) (@lem3078328)). Qed.
Lemma lem3078332 : term150 = True.
Proof. exact (TRANS (@lem3078327) (@lem3078331)). Qed.
Lemma lem3078333 : True = term150.
Proof. exact (SYM (@lem3078332)). Qed.
Lemma lem3078334 : term150.
Proof. exact (EQ_MP (@lem3078333) (@lem0)). Qed.
Lemma lem3078335 : term658.
Proof. exact (@lem3078324 (@lem3078334)). Qed.
Lemma lem3078337 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3078338 : term122 = term127.
Proof. exact (@lem3078337 term75 term75). Qed.
Lemma lem3078339 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078340 : term107 = term75.
Proof. exact (EQ_MP (@lem3078339) (@lem940073)). Qed.
Lemma lem3078341 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078342 : term105 = term74.
Proof. exact (MK_COMB (@lem3078341) (@lem3078340)). Qed.
Lemma lem3078343 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3078344 : term127 = term95.
Proof. exact (MK_COMB (@lem3078343) (@lem3078342)). Qed.
Lemma lem3078345 : term122 = term95.
Proof. exact (TRANS (@lem3078338) (@lem3078344)). Qed.
Lemma lem3078347 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078348 : term104 = term105.
Proof. exact (@lem3078347 term75 term75). Qed.
Lemma lem3078349 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078350 : term107 = term75.
Proof. exact (EQ_MP (@lem3078349) (@lem940073)). Qed.
Lemma lem3078351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078352 : term105 = term74.
Proof. exact (MK_COMB (@lem3078351) (@lem3078350)). Qed.
Lemma lem3078353 : term104 = term74.
Proof. exact (TRANS (@lem3078348) (@lem3078352)). Qed.
Lemma lem3078354 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3078355 : term659 = term649.
Proof. exact (MK_COMB (@lem3078354) (@lem3078353)). Qed.
Lemma lem3078356 : term660 = term653.
Proof. exact (MK_COMB (@lem3078355) (@lem3078345)). Qed.
Lemma lem3078358 (m : nat) : (term661 m) = term61.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem3078359 : term653 = term61.
Proof. exact (@lem3078358 term75). Qed.
Lemma lem3078360 : term660 = term61.
Proof. exact (TRANS (@lem3078356) (@lem3078359)). Qed.
Lemma lem3078361 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078362 : term662 = term194.
Proof. exact (MK_COMB (@lem3078361) (@lem3078360)). Qed.
Lemma lem3078363 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3078364 : term663 = term161.
Proof. exact (MK_COMB (@lem3078362) (@lem3078363)). Qed.
Lemma lem3078366 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3078367 : term161 = term61.
Proof. exact (@lem3078366 term75). Qed.
Lemma lem3078368 : term663 = term61.
Proof. exact (TRANS (@lem3078364) (@lem3078367)). Qed.
Lemma lem3078370 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078371 : term104 = term105.
Proof. exact (@lem3078370 term75 term75). Qed.
Lemma lem3078372 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078373 : term107 = term75.
Proof. exact (EQ_MP (@lem3078372) (@lem940073)). Qed.
Lemma lem3078374 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078375 : term105 = term74.
Proof. exact (MK_COMB (@lem3078374) (@lem3078373)). Qed.
Lemma lem3078376 : term104 = term74.
Proof. exact (TRANS (@lem3078371) (@lem3078375)). Qed.
Lemma lem3078377 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3078378 : term196 = term161.
Proof. exact (MK_COMB (@lem3078377) (@lem3078376)). Qed.
Lemma lem3078380 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3078381 : term161 = term61.
Proof. exact (@lem3078380 term75). Qed.
Lemma lem3078382 : term196 = term61.
Proof. exact (TRANS (@lem3078378) (@lem3078381)). Qed.
Lemma lem3078383 : term61 = term196.
Proof. exact (SYM (@lem3078382)). Qed.
Lemma lem3078384 : term663 = term196.
Proof. exact (TRANS (@lem3078368) (@lem3078383)). Qed.
Lemma lem3078385 : term654 = term92.
Proof. exact (@lem3078335 (@lem3078384)). Qed.
Lemma lem3078386 : term653 = term92.
Proof. exact (TRANS (@lem3078301) (@lem3078385)). Qed.
Lemma lem3078388 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3078389 : term92 = term61.
Proof. exact (@lem3078388 term61). Qed.
Lemma lem3078390 : term653 = term61.
Proof. exact (TRANS (@lem3078386) (@lem3078389)). Qed.
Lemma lem3078391 (_32062 : int) : (term130 _32062) = (term130 _32062).
Proof. exact (eq_refl (term130 _32062)). Qed.
Lemma lem3078392 (_32062 : int) : (term651 _32062) = (term664 _32062).
Proof. exact (MK_COMB (@lem3078391 _32062) (@lem3078390)). Qed.
Lemma lem3078393 (_32062 : int) : (term650 _32062) = (term664 _32062).
Proof. exact (TRANS (@lem3078292 _32062) (@lem3078392 _32062)). Qed.
Lemma lem3078394 (_32062 : int) : (term664 _32062) = (term140 _32062).
Proof. exact (@lem1982723 (term140 _32062)). Qed.
Lemma lem3078395 (_32062 : int) : (term650 _32062) = (term140 _32062).
Proof. exact (TRANS (@lem3078393 _32062) (@lem3078394 _32062)). Qed.
Lemma lem3078396 (_32062 : int) : (term648 _32062) = (term140 _32062).
Proof. exact (TRANS (@lem3078291 _32062) (@lem3078395 _32062)). Qed.
Lemma lem3078398 (_32062 : int) : (term647 _32062) = (term140 _32062).
Proof. exact (TRANS (@lem3078246 _32062) (@lem3078396 _32062)). Qed.
Lemma lem3078399 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078400 (_32062 : int) : (term665 _32062) = (term666 _32062).
Proof. exact (MK_COMB (@lem3078399) (@lem3078398 _32062)). Qed.
Lemma lem3078401 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078402 (_32062 : int) : (term646 _32062) = (term667 _32062).
Proof. exact (MK_COMB (@lem3078400 _32062) (@lem3078401)). Qed.
Lemma lem3078403 (_32062 : int) : (term618 _32062) = (term667 _32062).
Proof. exact (TRANS (@lem3078234 _32062) (@lem3078402 _32062)). Qed.
Lemma lem3078404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3078405 (_32061 : int) : (term620 _32061) = (term668 _32061).
Proof. exact (MK_COMB (@lem3078404) (@lem3078233 _32061)). Qed.
Lemma lem3078406 (_32061 : int) (_32062 : int) : (term621 _32061 _32062) = (term669 _32061 _32062).
Proof. exact (MK_COMB (@lem3078405 _32061) (@lem3078403 _32062)). Qed.
Lemma lem3078407 (_32061 : int) : (term601 _32061) = (term628 _32061).
Proof. exact (@lem1988287 term61 (term77 _32061)). Qed.
Lemma lem3078419 (_32061 : int) : (term629 _32061) = (term630 _32061).
Proof. exact (@lem1982792 term61 (term77 _32061)). Qed.
Lemma lem3078420 (_32061 : int) : (term119 _32061) = (term120 _32061).
Proof. exact (@lem1982781 (real_of_int _32061) term95 term74). Qed.
Lemma lem3078422 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078423 : term74 = term121.
Proof. exact (@lem3078422 term75). Qed.
Lemma lem3078425 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078426 : term95 = term96.
Proof. exact (@lem3078425 term75). Qed.
Lemma lem3078427 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078428 : term97 = term98.
Proof. exact (MK_COMB (@lem3078427) (@lem3078426)). Qed.
Lemma lem3078429 : term122 = term123.
Proof. exact (MK_COMB (@lem3078428) (@lem3078423)). Qed.
Lemma lem3078430 : term123 = term124.
Proof. exact (@lem1981613 term95 term74 term74 term74). Qed.
Lemma lem3078432 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078433 : term104 = term105.
Proof. exact (@lem3078432 term75 term75). Qed.
Lemma lem3078434 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078435 : term107 = term75.
Proof. exact (EQ_MP (@lem3078434) (@lem940073)). Qed.
Lemma lem3078436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078437 : term105 = term74.
Proof. exact (MK_COMB (@lem3078436) (@lem3078435)). Qed.
Lemma lem3078438 : term104 = term74.
Proof. exact (TRANS (@lem3078433) (@lem3078437)). Qed.
Lemma lem3078440 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3078441 : term122 = term127.
Proof. exact (@lem3078440 term75 term75). Qed.
Lemma lem3078442 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078443 : term107 = term75.
Proof. exact (EQ_MP (@lem3078442) (@lem940073)). Qed.
Lemma lem3078444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078445 : term105 = term74.
Proof. exact (MK_COMB (@lem3078444) (@lem3078443)). Qed.
Lemma lem3078446 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3078447 : term127 = term95.
Proof. exact (MK_COMB (@lem3078446) (@lem3078445)). Qed.
Lemma lem3078448 : term122 = term95.
Proof. exact (TRANS (@lem3078441) (@lem3078447)). Qed.
Lemma lem3078449 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078450 : term128 = term129.
Proof. exact (MK_COMB (@lem3078449) (@lem3078448)). Qed.
Lemma lem3078451 : term124 = term96.
Proof. exact (MK_COMB (@lem3078450) (@lem3078438)). Qed.
Lemma lem3078452 : term123 = term96.
Proof. exact (TRANS (@lem3078430) (@lem3078451)). Qed.
Lemma lem3078453 : term122 = term96.
Proof. exact (TRANS (@lem3078429) (@lem3078452)). Qed.
Lemma lem3078455 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078456 : term96 = term95.
Proof. exact (@lem3078455 term95). Qed.
Lemma lem3078457 : term122 = term95.
Proof. exact (TRANS (@lem3078453) (@lem3078456)). Qed.
Lemma lem3078460 (_32061 : int) : (term130 _32061) = (term130 _32061).
Proof. exact (eq_refl (term130 _32061)). Qed.
Lemma lem3078461 (_32061 : int) : (term120 _32061) = (term131 _32061).
Proof. exact (MK_COMB (@lem3078460 _32061) (@lem3078457)). Qed.
Lemma lem3078462 (_32061 : int) : (term119 _32061) = (term131 _32061).
Proof. exact (TRANS (@lem3078420 _32061) (@lem3078461 _32061)). Qed.
Lemma lem3078463 : term200 = term200.
Proof. exact (eq_refl term200). Qed.
Lemma lem3078464 (_32061 : int) : (term630 _32061) = (term631 _32061).
Proof. exact (MK_COMB (@lem3078463) (@lem3078462 _32061)). Qed.
Lemma lem3078465 (_32061 : int) : (term631 _32061) = (term131 _32061).
Proof. exact (@lem1982721 (term131 _32061)). Qed.
Lemma lem3078466 (_32061 : int) : (term630 _32061) = (term131 _32061).
Proof. exact (TRANS (@lem3078464 _32061) (@lem3078465 _32061)). Qed.
Lemma lem3078468 (_32061 : int) : (term629 _32061) = (term131 _32061).
Proof. exact (TRANS (@lem3078419 _32061) (@lem3078466 _32061)). Qed.
Lemma lem3078469 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078470 (_32061 : int) : (term632 _32061) = (term633 _32061).
Proof. exact (MK_COMB (@lem3078469) (@lem3078468 _32061)). Qed.
Lemma lem3078471 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078472 (_32061 : int) : (term628 _32061) = (term634 _32061).
Proof. exact (MK_COMB (@lem3078470 _32061) (@lem3078471)). Qed.
Lemma lem3078473 (_32061 : int) : (term601 _32061) = (term634 _32061).
Proof. exact (TRANS (@lem3078407 _32061) (@lem3078472 _32061)). Qed.
Lemma lem3078474 (_32061 : int) : (term613 _32061) = (term635 _32061).
Proof. exact (@lem1988287 (real_of_int _32061) term610). Qed.
Lemma lem3078481 : term610 = term74.
Proof. exact (@lem1982721 term74). Qed.
Lemma lem3078484 (_32061 : int) : (term636 _32061) = (term636 _32061).
Proof. exact (eq_refl (term636 _32061)). Qed.
Lemma lem3078485 (_32061 : int) : (term637 _32061) = (term638 _32061).
Proof. exact (MK_COMB (@lem3078484 _32061) (@lem3078481)). Qed.
Lemma lem3078486 (_32061 : int) : (term638 _32061) = (term639 _32061).
Proof. exact (@lem1982792 (real_of_int _32061) term74). Qed.
Lemma lem3078488 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078489 : term74 = term121.
Proof. exact (@lem3078488 term75). Qed.
Lemma lem3078491 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078492 : term95 = term96.
Proof. exact (@lem3078491 term75). Qed.
Lemma lem3078493 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078494 : term97 = term98.
Proof. exact (MK_COMB (@lem3078493) (@lem3078492)). Qed.
Lemma lem3078495 : term122 = term123.
Proof. exact (MK_COMB (@lem3078494) (@lem3078489)). Qed.
Lemma lem3078496 : term123 = term124.
Proof. exact (@lem1981613 term95 term74 term74 term74). Qed.
Lemma lem3078498 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078499 : term104 = term105.
Proof. exact (@lem3078498 term75 term75). Qed.
Lemma lem3078500 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078501 : term107 = term75.
Proof. exact (EQ_MP (@lem3078500) (@lem940073)). Qed.
Lemma lem3078502 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078503 : term105 = term74.
Proof. exact (MK_COMB (@lem3078502) (@lem3078501)). Qed.
Lemma lem3078504 : term104 = term74.
Proof. exact (TRANS (@lem3078499) (@lem3078503)). Qed.
Lemma lem3078506 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3078507 : term122 = term127.
Proof. exact (@lem3078506 term75 term75). Qed.
Lemma lem3078508 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078509 : term107 = term75.
Proof. exact (EQ_MP (@lem3078508) (@lem940073)). Qed.
Lemma lem3078510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078511 : term105 = term74.
Proof. exact (MK_COMB (@lem3078510) (@lem3078509)). Qed.
Lemma lem3078512 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3078513 : term127 = term95.
Proof. exact (MK_COMB (@lem3078512) (@lem3078511)). Qed.
Lemma lem3078514 : term122 = term95.
Proof. exact (TRANS (@lem3078507) (@lem3078513)). Qed.
Lemma lem3078515 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078516 : term128 = term129.
Proof. exact (MK_COMB (@lem3078515) (@lem3078514)). Qed.
Lemma lem3078517 : term124 = term96.
Proof. exact (MK_COMB (@lem3078516) (@lem3078504)). Qed.
Lemma lem3078518 : term123 = term96.
Proof. exact (TRANS (@lem3078496) (@lem3078517)). Qed.
Lemma lem3078519 : term122 = term96.
Proof. exact (TRANS (@lem3078495) (@lem3078518)). Qed.
Lemma lem3078521 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078522 : term96 = term95.
Proof. exact (@lem3078521 term95). Qed.
Lemma lem3078523 : term122 = term95.
Proof. exact (TRANS (@lem3078519) (@lem3078522)). Qed.
Lemma lem3078524 (_32061 : int) : (term76 _32061) = (term76 _32061).
Proof. exact (eq_refl (term76 _32061)). Qed.
Lemma lem3078527 (_32061 : int) : (term639 _32061) = (term640 _32061).
Proof. exact (MK_COMB (@lem3078524 _32061) (@lem3078523)). Qed.
Lemma lem3078528 (_32061 : int) : (term638 _32061) = (term640 _32061).
Proof. exact (TRANS (@lem3078486 _32061) (@lem3078527 _32061)). Qed.
Lemma lem3078529 (_32061 : int) : (term637 _32061) = (term640 _32061).
Proof. exact (TRANS (@lem3078485 _32061) (@lem3078528 _32061)). Qed.
Lemma lem3078530 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078531 (_32061 : int) : (term641 _32061) = (term642 _32061).
Proof. exact (MK_COMB (@lem3078530) (@lem3078529 _32061)). Qed.
Lemma lem3078532 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078533 (_32061 : int) : (term635 _32061) = (term643 _32061).
Proof. exact (MK_COMB (@lem3078531 _32061) (@lem3078532)). Qed.
Lemma lem3078534 (_32061 : int) : (term613 _32061) = (term643 _32061).
Proof. exact (TRANS (@lem3078474 _32061) (@lem3078533 _32061)). Qed.
Lemma lem3078535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078536 (_32061 : int) : (term603 _32061) = (term644 _32061).
Proof. exact (MK_COMB (@lem3078535) (@lem3078473 _32061)). Qed.
Lemma lem3078537 (_32061 : int) : (term614 _32061) = (term645 _32061).
Proof. exact (MK_COMB (@lem3078536 _32061) (@lem3078534 _32061)). Qed.
Lemma lem3078538 (_32062 : int) : (term601 _32062) = (term628 _32062).
Proof. exact (@lem1988287 term61 (term77 _32062)). Qed.
Lemma lem3078550 (_32062 : int) : (term629 _32062) = (term630 _32062).
Proof. exact (@lem1982792 term61 (term77 _32062)). Qed.
Lemma lem3078551 (_32062 : int) : (term119 _32062) = (term120 _32062).
Proof. exact (@lem1982781 (real_of_int _32062) term95 term74). Qed.
Lemma lem3078553 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078554 : term74 = term121.
Proof. exact (@lem3078553 term75). Qed.
Lemma lem3078556 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078557 : term95 = term96.
Proof. exact (@lem3078556 term75). Qed.
Lemma lem3078558 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078559 : term97 = term98.
Proof. exact (MK_COMB (@lem3078558) (@lem3078557)). Qed.
Lemma lem3078560 : term122 = term123.
Proof. exact (MK_COMB (@lem3078559) (@lem3078554)). Qed.
Lemma lem3078561 : term123 = term124.
Proof. exact (@lem1981613 term95 term74 term74 term74). Qed.
Lemma lem3078563 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078564 : term104 = term105.
Proof. exact (@lem3078563 term75 term75). Qed.
Lemma lem3078565 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078566 : term107 = term75.
Proof. exact (EQ_MP (@lem3078565) (@lem940073)). Qed.
Lemma lem3078567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078568 : term105 = term74.
Proof. exact (MK_COMB (@lem3078567) (@lem3078566)). Qed.
Lemma lem3078569 : term104 = term74.
Proof. exact (TRANS (@lem3078564) (@lem3078568)). Qed.
Lemma lem3078571 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3078572 : term122 = term127.
Proof. exact (@lem3078571 term75 term75). Qed.
Lemma lem3078573 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078574 : term107 = term75.
Proof. exact (EQ_MP (@lem3078573) (@lem940073)). Qed.
Lemma lem3078575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078576 : term105 = term74.
Proof. exact (MK_COMB (@lem3078575) (@lem3078574)). Qed.
Lemma lem3078577 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3078578 : term127 = term95.
Proof. exact (MK_COMB (@lem3078577) (@lem3078576)). Qed.
Lemma lem3078579 : term122 = term95.
Proof. exact (TRANS (@lem3078572) (@lem3078578)). Qed.
Lemma lem3078580 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078581 : term128 = term129.
Proof. exact (MK_COMB (@lem3078580) (@lem3078579)). Qed.
Lemma lem3078582 : term124 = term96.
Proof. exact (MK_COMB (@lem3078581) (@lem3078569)). Qed.
Lemma lem3078583 : term123 = term96.
Proof. exact (TRANS (@lem3078561) (@lem3078582)). Qed.
Lemma lem3078584 : term122 = term96.
Proof. exact (TRANS (@lem3078560) (@lem3078583)). Qed.
Lemma lem3078586 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078587 : term96 = term95.
Proof. exact (@lem3078586 term95). Qed.
Lemma lem3078588 : term122 = term95.
Proof. exact (TRANS (@lem3078584) (@lem3078587)). Qed.
Lemma lem3078591 (_32062 : int) : (term130 _32062) = (term130 _32062).
Proof. exact (eq_refl (term130 _32062)). Qed.
Lemma lem3078592 (_32062 : int) : (term120 _32062) = (term131 _32062).
Proof. exact (MK_COMB (@lem3078591 _32062) (@lem3078588)). Qed.
Lemma lem3078593 (_32062 : int) : (term119 _32062) = (term131 _32062).
Proof. exact (TRANS (@lem3078551 _32062) (@lem3078592 _32062)). Qed.
Lemma lem3078594 : term200 = term200.
Proof. exact (eq_refl term200). Qed.
Lemma lem3078595 (_32062 : int) : (term630 _32062) = (term631 _32062).
Proof. exact (MK_COMB (@lem3078594) (@lem3078593 _32062)). Qed.
Lemma lem3078596 (_32062 : int) : (term631 _32062) = (term131 _32062).
Proof. exact (@lem1982721 (term131 _32062)). Qed.
Lemma lem3078597 (_32062 : int) : (term630 _32062) = (term131 _32062).
Proof. exact (TRANS (@lem3078595 _32062) (@lem3078596 _32062)). Qed.
Lemma lem3078599 (_32062 : int) : (term629 _32062) = (term131 _32062).
Proof. exact (TRANS (@lem3078550 _32062) (@lem3078597 _32062)). Qed.
Lemma lem3078600 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078601 (_32062 : int) : (term632 _32062) = (term633 _32062).
Proof. exact (MK_COMB (@lem3078600) (@lem3078599 _32062)). Qed.
Lemma lem3078602 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078603 (_32062 : int) : (term628 _32062) = (term634 _32062).
Proof. exact (MK_COMB (@lem3078601 _32062) (@lem3078602)). Qed.
Lemma lem3078604 (_32062 : int) : (term601 _32062) = (term634 _32062).
Proof. exact (TRANS (@lem3078538 _32062) (@lem3078603 _32062)). Qed.
Lemma lem3078605 (_32062 : int) : (term613 _32062) = (term635 _32062).
Proof. exact (@lem1988287 (real_of_int _32062) term610). Qed.
Lemma lem3078612 : term610 = term74.
Proof. exact (@lem1982721 term74). Qed.
Lemma lem3078615 (_32062 : int) : (term636 _32062) = (term636 _32062).
Proof. exact (eq_refl (term636 _32062)). Qed.
Lemma lem3078616 (_32062 : int) : (term637 _32062) = (term638 _32062).
Proof. exact (MK_COMB (@lem3078615 _32062) (@lem3078612)). Qed.
Lemma lem3078617 (_32062 : int) : (term638 _32062) = (term639 _32062).
Proof. exact (@lem1982792 (real_of_int _32062) term74). Qed.
Lemma lem3078619 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078620 : term74 = term121.
Proof. exact (@lem3078619 term75). Qed.
Lemma lem3078622 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3078623 : term95 = term96.
Proof. exact (@lem3078622 term75). Qed.
Lemma lem3078624 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3078625 : term97 = term98.
Proof. exact (MK_COMB (@lem3078624) (@lem3078623)). Qed.
Lemma lem3078626 : term122 = term123.
Proof. exact (MK_COMB (@lem3078625) (@lem3078620)). Qed.
Lemma lem3078627 : term123 = term124.
Proof. exact (@lem1981613 term95 term74 term74 term74). Qed.
Lemma lem3078629 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078630 : term104 = term105.
Proof. exact (@lem3078629 term75 term75). Qed.
Lemma lem3078631 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078632 : term107 = term75.
Proof. exact (EQ_MP (@lem3078631) (@lem940073)). Qed.
Lemma lem3078633 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078634 : term105 = term74.
Proof. exact (MK_COMB (@lem3078633) (@lem3078632)). Qed.
Lemma lem3078635 : term104 = term74.
Proof. exact (TRANS (@lem3078630) (@lem3078634)). Qed.
Lemma lem3078637 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3078638 : term122 = term127.
Proof. exact (@lem3078637 term75 term75). Qed.
Lemma lem3078639 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078640 : term107 = term75.
Proof. exact (EQ_MP (@lem3078639) (@lem940073)). Qed.
Lemma lem3078641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078642 : term105 = term74.
Proof. exact (MK_COMB (@lem3078641) (@lem3078640)). Qed.
Lemma lem3078643 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3078644 : term127 = term95.
Proof. exact (MK_COMB (@lem3078643) (@lem3078642)). Qed.
Lemma lem3078645 : term122 = term95.
Proof. exact (TRANS (@lem3078638) (@lem3078644)). Qed.
Lemma lem3078646 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3078647 : term128 = term129.
Proof. exact (MK_COMB (@lem3078646) (@lem3078645)). Qed.
Lemma lem3078648 : term124 = term96.
Proof. exact (MK_COMB (@lem3078647) (@lem3078635)). Qed.
Lemma lem3078649 : term123 = term96.
Proof. exact (TRANS (@lem3078627) (@lem3078648)). Qed.
Lemma lem3078650 : term122 = term96.
Proof. exact (TRANS (@lem3078626) (@lem3078649)). Qed.
Lemma lem3078652 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3078653 : term96 = term95.
Proof. exact (@lem3078652 term95). Qed.
Lemma lem3078654 : term122 = term95.
Proof. exact (TRANS (@lem3078650) (@lem3078653)). Qed.
Lemma lem3078655 (_32062 : int) : (term76 _32062) = (term76 _32062).
Proof. exact (eq_refl (term76 _32062)). Qed.
Lemma lem3078658 (_32062 : int) : (term639 _32062) = (term640 _32062).
Proof. exact (MK_COMB (@lem3078655 _32062) (@lem3078654)). Qed.
Lemma lem3078659 (_32062 : int) : (term638 _32062) = (term640 _32062).
Proof. exact (TRANS (@lem3078617 _32062) (@lem3078658 _32062)). Qed.
Lemma lem3078660 (_32062 : int) : (term637 _32062) = (term640 _32062).
Proof. exact (TRANS (@lem3078616 _32062) (@lem3078659 _32062)). Qed.
Lemma lem3078661 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3078662 (_32062 : int) : (term641 _32062) = (term642 _32062).
Proof. exact (MK_COMB (@lem3078661) (@lem3078660 _32062)). Qed.
Lemma lem3078663 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3078664 (_32062 : int) : (term635 _32062) = (term643 _32062).
Proof. exact (MK_COMB (@lem3078662 _32062) (@lem3078663)). Qed.
Lemma lem3078665 (_32062 : int) : (term613 _32062) = (term643 _32062).
Proof. exact (TRANS (@lem3078605 _32062) (@lem3078664 _32062)). Qed.
Lemma lem3078666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078667 (_32062 : int) : (term603 _32062) = (term644 _32062).
Proof. exact (MK_COMB (@lem3078666) (@lem3078604 _32062)). Qed.
Lemma lem3078668 (_32062 : int) : (term614 _32062) = (term645 _32062).
Proof. exact (MK_COMB (@lem3078667 _32062) (@lem3078665 _32062)). Qed.
Lemma lem3078669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3078670 (_32061 : int) : (term620 _32061) = (term668 _32061).
Proof. exact (MK_COMB (@lem3078669) (@lem3078537 _32061)). Qed.
Lemma lem3078671 (_32061 : int) (_32062 : int) : (term622 _32061 _32062) = (term670 _32061 _32062).
Proof. exact (MK_COMB (@lem3078670 _32061) (@lem3078668 _32062)). Qed.
Lemma lem3078672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3078673 (_32061 : int) (_32062 : int) : (term623 _32061 _32062) = (term671 _32061 _32062).
Proof. exact (MK_COMB (@lem3078672) (@lem3078406 _32061 _32062)). Qed.
Lemma lem3078674 (_32061 : int) (_32062 : int) : (term624 _32061 _32062) = (term672 _32061 _32062).
Proof. exact (MK_COMB (@lem3078673 _32061 _32062) (@lem3078671 _32061 _32062)). Qed.
Lemma lem3078675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3078676 (_32062 : int) : (term83 _32062) = (term146 _32062).
Proof. exact (MK_COMB (@lem3078675) (@lem3078102 _32062)). Qed.
Lemma lem3078677 (_32061 : int) (_32062 : int) : (term625 _32061 _32062) = (term673 _32061 _32062).
Proof. exact (MK_COMB (@lem3078676 _32062) (@lem3078674 _32061 _32062)). Qed.
Lemma lem3078678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3078679 (_32061 : int) : (term83 _32061) = (term146 _32061).
Proof. exact (MK_COMB (@lem3078678) (@lem3078054 _32061)). Qed.
Lemma lem3078680 (_32061 : int) (_32062 : int) : (term626 _32061 _32062) = (term674 _32061 _32062).
Proof. exact (MK_COMB (@lem3078679 _32061) (@lem3078677 _32061 _32062)). Qed.
Lemma lem3078687 (_32061 : int) (_32062 : int) : (term627 _32061 _32062) = (term674 _32061 _32062).
Proof. exact (TRANS (@lem3078006 _32061 _32062) (@lem3078680 _32061 _32062)). Qed.
Lemma lem3078701 (_32061 : int) (_32062 : int) : (term670 _32061 _32062) = (term675 _32061 _32062).
Proof. exact (@lem19158 (term634 _32062) (term645 _32061) (term643 _32062)). Qed.
Lemma lem3078708 (_32061 : int) (_32062 : int) : (term676 _32061 _32062) = (term677 _32061 _32062).
Proof. exact (@lem19367 (term634 _32061) (term643 _32061) (term643 _32062)). Qed.
Lemma lem3078715 (_32061 : int) (_32062 : int) : (term678 _32061 _32062) = (term679 _32061 _32062).
Proof. exact (@lem19367 (term634 _32061) (term643 _32061) (term634 _32062)). Qed.
Lemma lem3078716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078717 (_32061 : int) (_32062 : int) : (term680 _32061 _32062) = (term681 _32061 _32062).
Proof. exact (MK_COMB (@lem3078716) (@lem3078715 _32061 _32062)). Qed.
Lemma lem3078718 (_32061 : int) (_32062 : int) : (term675 _32061 _32062) = (term682 _32061 _32062).
Proof. exact (MK_COMB (@lem3078717 _32061 _32062) (@lem3078708 _32061 _32062)). Qed.
Lemma lem3078720 (_32061 : int) (_32062 : int) : (term670 _32061 _32062) = (term682 _32061 _32062).
Proof. exact (TRANS (@lem3078701 _32061 _32062) (@lem3078718 _32061 _32062)). Qed.
Lemma lem3078737 (_32061 : int) (_32062 : int) : (term669 _32061 _32062) = (term683 _32061 _32062).
Proof. exact (@lem19367 (term634 _32061) (term643 _32061) (term667 _32062)). Qed.
Lemma lem3078738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3078739 (_32061 : int) (_32062 : int) : (term671 _32061 _32062) = (term684 _32061 _32062).
Proof. exact (MK_COMB (@lem3078738) (@lem3078737 _32061 _32062)). Qed.
Lemma lem3078740 (_32061 : int) (_32062 : int) : (term672 _32061 _32062) = (term685 _32061 _32062).
Proof. exact (MK_COMB (@lem3078739 _32061 _32062) (@lem3078720 _32061 _32062)). Qed.
Lemma lem3078741 (_32061 : int) (_32062 : int) : (term685 _32061 _32062) = (term686 _32061 _32062).
Proof. exact (@lem19158 (term679 _32061 _32062) (term683 _32061 _32062) (term677 _32061 _32062)). Qed.
Lemma lem3078742 (_32061 : int) (_32062 : int) : (term687 _32061 _32062) = (term688 _32061 _32062).
Proof. exact (@lem19158 (term689 _32061 _32062) (term683 _32061 _32062) (term690 _32061 _32062)). Qed.
Lemma lem3078749 (_32061 : int) (_32062 : int) : (term691 _32061 _32062) = (term692 _32061 _32062).
Proof. exact (@lem19367 (term693 _32061 _32062) (term694 _32061 _32062) (term690 _32061 _32062)). Qed.
Lemma lem3078756 (_32061 : int) (_32062 : int) : (term695 _32061 _32062) = (term696 _32061 _32062).
Proof. exact (@lem19367 (term693 _32061 _32062) (term694 _32061 _32062) (term689 _32061 _32062)). Qed.
Lemma lem3078757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078758 (_32061 : int) (_32062 : int) : (term697 _32061 _32062) = (term698 _32061 _32062).
Proof. exact (MK_COMB (@lem3078757) (@lem3078756 _32061 _32062)). Qed.
Lemma lem3078759 (_32061 : int) (_32062 : int) : (term688 _32061 _32062) = (term699 _32061 _32062).
Proof. exact (MK_COMB (@lem3078758 _32061 _32062) (@lem3078749 _32061 _32062)). Qed.
Lemma lem3078760 (_32061 : int) (_32062 : int) : (term687 _32061 _32062) = (term699 _32061 _32062).
Proof. exact (TRANS (@lem3078742 _32061 _32062) (@lem3078759 _32061 _32062)). Qed.
Lemma lem3078761 (_32061 : int) (_32062 : int) : (term700 _32061 _32062) = (term701 _32061 _32062).
Proof. exact (@lem19158 (term702 _32061 _32062) (term683 _32061 _32062) (term703 _32061 _32062)). Qed.
Lemma lem3078768 (_32061 : int) (_32062 : int) : (term704 _32061 _32062) = (term705 _32061 _32062).
Proof. exact (@lem19367 (term693 _32061 _32062) (term694 _32061 _32062) (term703 _32061 _32062)). Qed.
Lemma lem3078775 (_32061 : int) (_32062 : int) : (term706 _32061 _32062) = (term707 _32061 _32062).
Proof. exact (@lem19367 (term693 _32061 _32062) (term694 _32061 _32062) (term702 _32061 _32062)). Qed.
Lemma lem3078776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078777 (_32061 : int) (_32062 : int) : (term708 _32061 _32062) = (term709 _32061 _32062).
Proof. exact (MK_COMB (@lem3078776) (@lem3078775 _32061 _32062)). Qed.
Lemma lem3078778 (_32061 : int) (_32062 : int) : (term701 _32061 _32062) = (term710 _32061 _32062).
Proof. exact (MK_COMB (@lem3078777 _32061 _32062) (@lem3078768 _32061 _32062)). Qed.
Lemma lem3078779 (_32061 : int) (_32062 : int) : (term700 _32061 _32062) = (term710 _32061 _32062).
Proof. exact (TRANS (@lem3078761 _32061 _32062) (@lem3078778 _32061 _32062)). Qed.
Lemma lem3078780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078781 (_32061 : int) (_32062 : int) : (term711 _32061 _32062) = (term712 _32061 _32062).
Proof. exact (MK_COMB (@lem3078780) (@lem3078779 _32061 _32062)). Qed.
Lemma lem3078782 (_32061 : int) (_32062 : int) : (term686 _32061 _32062) = (term713 _32061 _32062).
Proof. exact (MK_COMB (@lem3078781 _32061 _32062) (@lem3078760 _32061 _32062)). Qed.
Lemma lem3078783 (_32061 : int) (_32062 : int) : (term685 _32061 _32062) = (term713 _32061 _32062).
Proof. exact (TRANS (@lem3078741 _32061 _32062) (@lem3078782 _32061 _32062)). Qed.
Lemma lem3078784 (_32061 : int) (_32062 : int) : (term672 _32061 _32062) = (term713 _32061 _32062).
Proof. exact (TRANS (@lem3078740 _32061 _32062) (@lem3078783 _32061 _32062)). Qed.
Lemma lem3078787 (_32062 : int) : (term146 _32062) = (term146 _32062).
Proof. exact (eq_refl (term146 _32062)). Qed.
Lemma lem3078788 (_32061 : int) (_32062 : int) : (term673 _32061 _32062) = (term714 _32061 _32062).
Proof. exact (MK_COMB (@lem3078787 _32062) (@lem3078784 _32061 _32062)). Qed.
Lemma lem3078789 (_32061 : int) (_32062 : int) : (term714 _32061 _32062) = (term715 _32061 _32062).
Proof. exact (@lem19158 (term710 _32061 _32062) (term115 _32062) (term699 _32061 _32062)). Qed.
Lemma lem3078790 (_32061 : int) (_32062 : int) : (term716 _32061 _32062) = (term717 _32061 _32062).
Proof. exact (@lem19158 (term696 _32061 _32062) (term115 _32062) (term692 _32061 _32062)). Qed.
Lemma lem3078797 (_32061 : int) (_32062 : int) : (term718 _32061 _32062) = (term719 _32061 _32062).
Proof. exact (@lem19158 (term720 _32061 _32062) (term115 _32062) (term721 _32061 _32062)). Qed.
Lemma lem3078804 (_32061 : int) (_32062 : int) : (term722 _32061 _32062) = (term723 _32061 _32062).
Proof. exact (@lem19158 (term724 _32061 _32062) (term115 _32062) (term725 _32061 _32062)). Qed.
Lemma lem3078805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078806 (_32061 : int) (_32062 : int) : (term726 _32061 _32062) = (term727 _32061 _32062).
Proof. exact (MK_COMB (@lem3078805) (@lem3078804 _32061 _32062)). Qed.
Lemma lem3078807 (_32061 : int) (_32062 : int) : (term717 _32061 _32062) = (term728 _32061 _32062).
Proof. exact (MK_COMB (@lem3078806 _32061 _32062) (@lem3078797 _32061 _32062)). Qed.
Lemma lem3078808 (_32061 : int) (_32062 : int) : (term716 _32061 _32062) = (term728 _32061 _32062).
Proof. exact (TRANS (@lem3078790 _32061 _32062) (@lem3078807 _32061 _32062)). Qed.
Lemma lem3078809 (_32061 : int) (_32062 : int) : (term729 _32061 _32062) = (term730 _32061 _32062).
Proof. exact (@lem19158 (term707 _32061 _32062) (term115 _32062) (term705 _32061 _32062)). Qed.
Lemma lem3078816 (_32061 : int) (_32062 : int) : (term731 _32061 _32062) = (term732 _32061 _32062).
Proof. exact (@lem19158 (term733 _32061 _32062) (term115 _32062) (term734 _32061 _32062)). Qed.
Lemma lem3078823 (_32061 : int) (_32062 : int) : (term735 _32061 _32062) = (term736 _32061 _32062).
Proof. exact (@lem19158 (term737 _32061 _32062) (term115 _32062) (term738 _32061 _32062)). Qed.
Lemma lem3078824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078825 (_32061 : int) (_32062 : int) : (term739 _32061 _32062) = (term740 _32061 _32062).
Proof. exact (MK_COMB (@lem3078824) (@lem3078823 _32061 _32062)). Qed.
Lemma lem3078826 (_32061 : int) (_32062 : int) : (term730 _32061 _32062) = (term741 _32061 _32062).
Proof. exact (MK_COMB (@lem3078825 _32061 _32062) (@lem3078816 _32061 _32062)). Qed.
Lemma lem3078827 (_32061 : int) (_32062 : int) : (term729 _32061 _32062) = (term741 _32061 _32062).
Proof. exact (TRANS (@lem3078809 _32061 _32062) (@lem3078826 _32061 _32062)). Qed.
Lemma lem3078828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078829 (_32061 : int) (_32062 : int) : (term742 _32061 _32062) = (term743 _32061 _32062).
Proof. exact (MK_COMB (@lem3078828) (@lem3078827 _32061 _32062)). Qed.
Lemma lem3078830 (_32061 : int) (_32062 : int) : (term715 _32061 _32062) = (term744 _32061 _32062).
Proof. exact (MK_COMB (@lem3078829 _32061 _32062) (@lem3078808 _32061 _32062)). Qed.
Lemma lem3078831 (_32061 : int) (_32062 : int) : (term714 _32061 _32062) = (term744 _32061 _32062).
Proof. exact (TRANS (@lem3078789 _32061 _32062) (@lem3078830 _32061 _32062)). Qed.
Lemma lem3078832 (_32061 : int) (_32062 : int) : (term673 _32061 _32062) = (term744 _32061 _32062).
Proof. exact (TRANS (@lem3078788 _32061 _32062) (@lem3078831 _32061 _32062)). Qed.
Lemma lem3078835 (_32061 : int) : (term146 _32061) = (term146 _32061).
Proof. exact (eq_refl (term146 _32061)). Qed.
Lemma lem3078836 (_32061 : int) (_32062 : int) : (term674 _32061 _32062) = (term745 _32061 _32062).
Proof. exact (MK_COMB (@lem3078835 _32061) (@lem3078832 _32061 _32062)). Qed.
Lemma lem3078837 (_32061 : int) (_32062 : int) : (term745 _32061 _32062) = (term746 _32061 _32062).
Proof. exact (@lem19158 (term741 _32061 _32062) (term115 _32061) (term728 _32061 _32062)). Qed.
Lemma lem3078838 (_32061 : int) (_32062 : int) : (term747 _32061 _32062) = (term748 _32061 _32062).
Proof. exact (@lem19158 (term723 _32061 _32062) (term115 _32061) (term719 _32061 _32062)). Qed.
Lemma lem3078845 (_32061 : int) (_32062 : int) : (term749 _32061 _32062) = (term750 _32061 _32062).
Proof. exact (@lem19158 (term751 _32061 _32062) (term115 _32061) (term752 _32061 _32062)). Qed.
Lemma lem3078852 (_32061 : int) (_32062 : int) : (term753 _32061 _32062) = (term754 _32061 _32062).
Proof. exact (@lem19158 (term755 _32061 _32062) (term115 _32061) (term756 _32061 _32062)). Qed.
Lemma lem3078853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078854 (_32061 : int) (_32062 : int) : (term757 _32061 _32062) = (term758 _32061 _32062).
Proof. exact (MK_COMB (@lem3078853) (@lem3078852 _32061 _32062)). Qed.
Lemma lem3078855 (_32061 : int) (_32062 : int) : (term748 _32061 _32062) = (term759 _32061 _32062).
Proof. exact (MK_COMB (@lem3078854 _32061 _32062) (@lem3078845 _32061 _32062)). Qed.
Lemma lem3078856 (_32061 : int) (_32062 : int) : (term747 _32061 _32062) = (term759 _32061 _32062).
Proof. exact (TRANS (@lem3078838 _32061 _32062) (@lem3078855 _32061 _32062)). Qed.
Lemma lem3078857 (_32061 : int) (_32062 : int) : (term760 _32061 _32062) = (term761 _32061 _32062).
Proof. exact (@lem19158 (term736 _32061 _32062) (term115 _32061) (term732 _32061 _32062)). Qed.
Lemma lem3078864 (_32061 : int) (_32062 : int) : (term762 _32061 _32062) = (term763 _32061 _32062).
Proof. exact (@lem19158 (term764 _32061 _32062) (term115 _32061) (term765 _32061 _32062)). Qed.
Lemma lem3078871 (_32061 : int) (_32062 : int) : (term766 _32061 _32062) = (term767 _32061 _32062).
Proof. exact (@lem19158 (term768 _32061 _32062) (term115 _32061) (term769 _32061 _32062)). Qed.
Lemma lem3078872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078873 (_32061 : int) (_32062 : int) : (term770 _32061 _32062) = (term771 _32061 _32062).
Proof. exact (MK_COMB (@lem3078872) (@lem3078871 _32061 _32062)). Qed.
Lemma lem3078874 (_32061 : int) (_32062 : int) : (term761 _32061 _32062) = (term772 _32061 _32062).
Proof. exact (MK_COMB (@lem3078873 _32061 _32062) (@lem3078864 _32061 _32062)). Qed.
Lemma lem3078875 (_32061 : int) (_32062 : int) : (term760 _32061 _32062) = (term772 _32061 _32062).
Proof. exact (TRANS (@lem3078857 _32061 _32062) (@lem3078874 _32061 _32062)). Qed.
Lemma lem3078876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3078877 (_32061 : int) (_32062 : int) : (term773 _32061 _32062) = (term774 _32061 _32062).
Proof. exact (MK_COMB (@lem3078876) (@lem3078875 _32061 _32062)). Qed.
Lemma lem3078878 (_32061 : int) (_32062 : int) : (term746 _32061 _32062) = (term775 _32061 _32062).
Proof. exact (MK_COMB (@lem3078877 _32061 _32062) (@lem3078856 _32061 _32062)). Qed.
Lemma lem3078879 (_32061 : int) (_32062 : int) : (term745 _32061 _32062) = (term775 _32061 _32062).
Proof. exact (TRANS (@lem3078837 _32061 _32062) (@lem3078878 _32061 _32062)). Qed.
Lemma lem3078880 (_32061 : int) (_32062 : int) : (term674 _32061 _32062) = (term775 _32061 _32062).
Proof. exact (TRANS (@lem3078836 _32061 _32062) (@lem3078879 _32061 _32062)). Qed.
Lemma lem3078881 (_32061 : int) (_32062 : int) : (term627 _32061 _32062) = (term775 _32061 _32062).
Proof. exact (TRANS (@lem3078687 _32061 _32062) (@lem3078880 _32061 _32062)). Qed.
Lemma lem3078927 (_32061 : int) (_32062 : int) (h1 : term775 _32061 _32062) : term775 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3078928 (_32061 : int) (_32062 : int) (h1 : term772 _32061 _32062) : term772 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3078929 (_32061 : int) (_32062 : int) (h1 : term767 _32061 _32062) : term767 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3078930 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term776 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3078931 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term768 _32061 _32062.
Proof. exact (proj2 (@lem3078930 _32061 _32062 h1)). Qed.
Lemma lem3078932 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term115 _32061.
Proof. exact (proj1 (@lem3078930 _32061 _32062 h1)). Qed.
Lemma lem3078933 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term737 _32061 _32062.
Proof. exact (proj2 (@lem3078931 _32061 _32062 h1)). Qed.
Lemma lem3078935 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term702 _32061 _32062.
Proof. exact (proj2 (@lem3078933 _32061 _32062 h1)). Qed.
Lemma lem3078940 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term634 _32061.
Proof. exact (proj1 (@lem3078935 _32061 _32062 h1)). Qed.
Lemma lem3078942 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3078943 : term149 = term150.
Proof. exact (@lem3078942 term61 term74). Qed.
Lemma lem3078945 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078946 : term74 = term121.
Proof. exact (@lem3078945 term75). Qed.
Lemma lem3078948 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3078949 : term61 = term92.
Proof. exact (@lem3078948 (NUMERAL 0)). Qed.
Lemma lem3078950 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3078951 : term151 = term152.
Proof. exact (MK_COMB (@lem3078950) (@lem3078949)). Qed.
Lemma lem3078952 : term150 = term153.
Proof. exact (MK_COMB (@lem3078951) (@lem3078946)). Qed.
Lemma lem3078953 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3078955 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3078956 : term150 = term156.
Proof. exact (@lem3078955 (NUMERAL 0) term75). Qed.
Lemma lem3078957 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3078958 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3078959 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3078958 h1) (fun h1 : term156 = True => @lem3078957)). Qed.
Lemma lem3078960 : term156 = True.
Proof. exact (EQ_MP (@lem3078959) (@lem3078957)). Qed.
Lemma lem3078961 : term150 = True.
Proof. exact (TRANS (@lem3078956) (@lem3078960)). Qed.
Lemma lem3078962 : True = term150.
Proof. exact (SYM (@lem3078961)). Qed.
Lemma lem3078963 : term150.
Proof. exact (EQ_MP (@lem3078962) (@lem0)). Qed.
Lemma lem3078964 : term158.
Proof. exact (@lem3078953 (@lem3078963)). Qed.
Lemma lem3078966 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3078967 : term150 = term156.
Proof. exact (@lem3078966 (NUMERAL 0) term75). Qed.
Lemma lem3078968 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3078969 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3078970 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3078969 h1) (fun h1 : term156 = True => @lem3078968)). Qed.
Lemma lem3078971 : term156 = True.
Proof. exact (EQ_MP (@lem3078970) (@lem3078968)). Qed.
Lemma lem3078972 : term150 = True.
Proof. exact (TRANS (@lem3078967) (@lem3078971)). Qed.
Lemma lem3078973 : True = term150.
Proof. exact (SYM (@lem3078972)). Qed.
Lemma lem3078974 : term150.
Proof. exact (EQ_MP (@lem3078973) (@lem0)). Qed.
Lemma lem3078975 : term153 = term159.
Proof. exact (@lem3078964 (@lem3078974)). Qed.
Lemma lem3078977 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3078978 : term104 = term105.
Proof. exact (@lem3078977 term75 term75). Qed.
Lemma lem3078979 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3078980 : term107 = term75.
Proof. exact (EQ_MP (@lem3078979) (@lem940073)). Qed.
Lemma lem3078981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3078982 : term105 = term74.
Proof. exact (MK_COMB (@lem3078981) (@lem3078980)). Qed.
Lemma lem3078983 : term104 = term74.
Proof. exact (TRANS (@lem3078978) (@lem3078982)). Qed.
Lemma lem3078985 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3078986 : term161 = term61.
Proof. exact (@lem3078985 term75). Qed.
Lemma lem3078987 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3078988 : term162 = term151.
Proof. exact (MK_COMB (@lem3078987) (@lem3078986)). Qed.
Lemma lem3078989 : term159 = term150.
Proof. exact (MK_COMB (@lem3078988) (@lem3078983)). Qed.
Lemma lem3078991 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3078992 : term150 = term156.
Proof. exact (@lem3078991 (NUMERAL 0) term75). Qed.
Lemma lem3078993 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3078994 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3078995 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3078994 h1) (fun h1 : term156 = True => @lem3078993)). Qed.
Lemma lem3078996 : term156 = True.
Proof. exact (EQ_MP (@lem3078995) (@lem3078993)). Qed.
Lemma lem3078997 : term150 = True.
Proof. exact (TRANS (@lem3078992) (@lem3078996)). Qed.
Lemma lem3078998 : term159 = True.
Proof. exact (TRANS (@lem3078989) (@lem3078997)). Qed.
Lemma lem3078999 : term153 = True.
Proof. exact (TRANS (@lem3078975) (@lem3078998)). Qed.
Lemma lem3079000 : term150 = True.
Proof. exact (TRANS (@lem3078952) (@lem3078999)). Qed.
Lemma lem3079001 : term149 = True.
Proof. exact (TRANS (@lem3078943) (@lem3079000)). Qed.
Lemma lem3079002 : True = term149.
Proof. exact (SYM (@lem3079001)). Qed.
Lemma lem3079003 : term149.
Proof. exact (EQ_MP (@lem3079002) (@lem0)). Qed.
Lemma lem3079004 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term777 _32061.
Proof. exact (conj (@lem3079003) (@lem3078932 _32061 _32062 h1)). Qed.
Lemma lem3079006 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3079007 (_32061 : int) : term778 _32061.
Proof. exact (@lem3079006 term74 (real_of_int _32061)). Qed.
Lemma lem3079008 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term779 _32061.
Proof. exact (@lem3079007 _32061 (@lem3079004 _32061 _32062 h1)). Qed.
Lemma lem3079009 (_32061 : int) : (term780 _32061) = (real_of_int _32061).
Proof. exact (@lem1982733 (real_of_int _32061)). Qed.
Lemma lem3079010 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3079011 (_32061 : int) : (term781 _32061) = (term114 _32061).
Proof. exact (MK_COMB (@lem3079010) (@lem3079009 _32061)). Qed.
Lemma lem3079012 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3079013 (_32061 : int) : (term779 _32061) = (term115 _32061).
Proof. exact (MK_COMB (@lem3079011 _32061) (@lem3079012)). Qed.
Lemma lem3079014 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term115 _32061.
Proof. exact (EQ_MP (@lem3079013 _32061) (@lem3079008 _32061 _32062 h1)). Qed.
Lemma lem3079016 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3079017 : term149 = term150.
Proof. exact (@lem3079016 term61 term74). Qed.
Lemma lem3079019 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079020 : term74 = term121.
Proof. exact (@lem3079019 term75). Qed.
Lemma lem3079022 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079023 : term61 = term92.
Proof. exact (@lem3079022 (NUMERAL 0)). Qed.
Lemma lem3079024 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079025 : term151 = term152.
Proof. exact (MK_COMB (@lem3079024) (@lem3079023)). Qed.
Lemma lem3079026 : term150 = term153.
Proof. exact (MK_COMB (@lem3079025) (@lem3079020)). Qed.
Lemma lem3079027 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3079029 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079030 : term150 = term156.
Proof. exact (@lem3079029 (NUMERAL 0) term75). Qed.
Lemma lem3079031 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079032 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079033 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079032 h1) (fun h1 : term156 = True => @lem3079031)). Qed.
Lemma lem3079034 : term156 = True.
Proof. exact (EQ_MP (@lem3079033) (@lem3079031)). Qed.
Lemma lem3079035 : term150 = True.
Proof. exact (TRANS (@lem3079030) (@lem3079034)). Qed.
Lemma lem3079036 : True = term150.
Proof. exact (SYM (@lem3079035)). Qed.
Lemma lem3079037 : term150.
Proof. exact (EQ_MP (@lem3079036) (@lem0)). Qed.
Lemma lem3079038 : term158.
Proof. exact (@lem3079027 (@lem3079037)). Qed.
Lemma lem3079040 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079041 : term150 = term156.
Proof. exact (@lem3079040 (NUMERAL 0) term75). Qed.
Lemma lem3079042 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079043 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079044 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079043 h1) (fun h1 : term156 = True => @lem3079042)). Qed.
Lemma lem3079045 : term156 = True.
Proof. exact (EQ_MP (@lem3079044) (@lem3079042)). Qed.
Lemma lem3079046 : term150 = True.
Proof. exact (TRANS (@lem3079041) (@lem3079045)). Qed.
Lemma lem3079047 : True = term150.
Proof. exact (SYM (@lem3079046)). Qed.
Lemma lem3079048 : term150.
Proof. exact (EQ_MP (@lem3079047) (@lem0)). Qed.
Lemma lem3079049 : term153 = term159.
Proof. exact (@lem3079038 (@lem3079048)). Qed.
Lemma lem3079051 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079052 : term104 = term105.
Proof. exact (@lem3079051 term75 term75). Qed.
Lemma lem3079053 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079054 : term107 = term75.
Proof. exact (EQ_MP (@lem3079053) (@lem940073)). Qed.
Lemma lem3079055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079056 : term105 = term74.
Proof. exact (MK_COMB (@lem3079055) (@lem3079054)). Qed.
Lemma lem3079057 : term104 = term74.
Proof. exact (TRANS (@lem3079052) (@lem3079056)). Qed.
Lemma lem3079059 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079060 : term161 = term61.
Proof. exact (@lem3079059 term75). Qed.
Lemma lem3079061 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079062 : term162 = term151.
Proof. exact (MK_COMB (@lem3079061) (@lem3079060)). Qed.
Lemma lem3079063 : term159 = term150.
Proof. exact (MK_COMB (@lem3079062) (@lem3079057)). Qed.
Lemma lem3079065 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079066 : term150 = term156.
Proof. exact (@lem3079065 (NUMERAL 0) term75). Qed.
Lemma lem3079067 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079068 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079069 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079068 h1) (fun h1 : term156 = True => @lem3079067)). Qed.
Lemma lem3079070 : term156 = True.
Proof. exact (EQ_MP (@lem3079069) (@lem3079067)). Qed.
Lemma lem3079071 : term150 = True.
Proof. exact (TRANS (@lem3079066) (@lem3079070)). Qed.
Lemma lem3079072 : term159 = True.
Proof. exact (TRANS (@lem3079063) (@lem3079071)). Qed.
Lemma lem3079073 : term153 = True.
Proof. exact (TRANS (@lem3079049) (@lem3079072)). Qed.
Lemma lem3079074 : term150 = True.
Proof. exact (TRANS (@lem3079026) (@lem3079073)). Qed.
Lemma lem3079075 : term149 = True.
Proof. exact (TRANS (@lem3079017) (@lem3079074)). Qed.
Lemma lem3079076 : True = term149.
Proof. exact (SYM (@lem3079075)). Qed.
Lemma lem3079077 : term149.
Proof. exact (EQ_MP (@lem3079076) (@lem0)). Qed.
Lemma lem3079078 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term782 _32061.
Proof. exact (conj (@lem3079077) (@lem3078940 _32061 _32062 h1)). Qed.
Lemma lem3079080 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3079081 (_32061 : int) : term783 _32061.
Proof. exact (@lem3079080 term74 (term131 _32061)). Qed.
Lemma lem3079082 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term784 _32061.
Proof. exact (@lem3079081 _32061 (@lem3079078 _32061 _32062 h1)). Qed.
Lemma lem3079083 (_32061 : int) : (term785 _32061) = (term131 _32061).
Proof. exact (@lem1982733 (term131 _32061)). Qed.
Lemma lem3079084 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3079085 (_32061 : int) : (term786 _32061) = (term633 _32061).
Proof. exact (MK_COMB (@lem3079084) (@lem3079083 _32061)). Qed.
Lemma lem3079086 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3079087 (_32061 : int) : (term784 _32061) = (term634 _32061).
Proof. exact (MK_COMB (@lem3079085 _32061) (@lem3079086)). Qed.
Lemma lem3079088 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term634 _32061.
Proof. exact (EQ_MP (@lem3079087 _32061) (@lem3079082 _32061 _32062 h1)). Qed.
Lemma lem3079089 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term787 _32061.
Proof. exact (conj (@lem3079088 _32061 _32062 h1) (@lem3079014 _32061 _32062 h1)). Qed.
Lemma lem3079091 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3079092 (_32061 : int) : term788 _32061.
Proof. exact (@lem3079091 (term131 _32061) (real_of_int _32061)). Qed.
Lemma lem3079093 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term789 _32061.
Proof. exact (@lem3079092 _32061 (@lem3079089 _32061 _32062 h1)). Qed.
Lemma lem3079094 (_32061 : int) : (term790 _32061) = (term791 _32061).
Proof. exact (@lem1982759 (term140 _32061) (real_of_int _32061) term95). Qed.
Lemma lem3079095 (_32061 : int) : (term180 _32061) = (term181 _32061).
Proof. exact (@lem1982713 term95 (real_of_int _32061)). Qed.
Lemma lem3079097 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079098 : term74 = term121.
Proof. exact (@lem3079097 term75). Qed.
Lemma lem3079100 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3079101 : term95 = term96.
Proof. exact (@lem3079100 term75). Qed.
Lemma lem3079102 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079103 : term182 = term183.
Proof. exact (MK_COMB (@lem3079102) (@lem3079101)). Qed.
Lemma lem3079104 : term184 = term185.
Proof. exact (MK_COMB (@lem3079103) (@lem3079098)). Qed.
Lemma lem3079105 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3079107 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079108 : term150 = term156.
Proof. exact (@lem3079107 (NUMERAL 0) term75). Qed.
Lemma lem3079109 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079110 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079111 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079110 h1) (fun h1 : term156 = True => @lem3079109)). Qed.
Lemma lem3079112 : term156 = True.
Proof. exact (EQ_MP (@lem3079111) (@lem3079109)). Qed.
Lemma lem3079113 : term150 = True.
Proof. exact (TRANS (@lem3079108) (@lem3079112)). Qed.
Lemma lem3079114 : True = term150.
Proof. exact (SYM (@lem3079113)). Qed.
Lemma lem3079115 : term150.
Proof. exact (EQ_MP (@lem3079114) (@lem0)). Qed.
Lemma lem3079116 : term187.
Proof. exact (@lem3079105 (@lem3079115)). Qed.
Lemma lem3079118 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079119 : term150 = term156.
Proof. exact (@lem3079118 (NUMERAL 0) term75). Qed.
Lemma lem3079120 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079121 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079122 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079121 h1) (fun h1 : term156 = True => @lem3079120)). Qed.
Lemma lem3079123 : term156 = True.
Proof. exact (EQ_MP (@lem3079122) (@lem3079120)). Qed.
Lemma lem3079124 : term150 = True.
Proof. exact (TRANS (@lem3079119) (@lem3079123)). Qed.
Lemma lem3079125 : True = term150.
Proof. exact (SYM (@lem3079124)). Qed.
Lemma lem3079126 : term150.
Proof. exact (EQ_MP (@lem3079125) (@lem0)). Qed.
Lemma lem3079127 : term188.
Proof. exact (@lem3079116 (@lem3079126)). Qed.
Lemma lem3079129 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079130 : term150 = term156.
Proof. exact (@lem3079129 (NUMERAL 0) term75). Qed.
Lemma lem3079131 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079132 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079133 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079132 h1) (fun h1 : term156 = True => @lem3079131)). Qed.
Lemma lem3079134 : term156 = True.
Proof. exact (EQ_MP (@lem3079133) (@lem3079131)). Qed.
Lemma lem3079135 : term150 = True.
Proof. exact (TRANS (@lem3079130) (@lem3079134)). Qed.
Lemma lem3079136 : True = term150.
Proof. exact (SYM (@lem3079135)). Qed.
Lemma lem3079137 : term150.
Proof. exact (EQ_MP (@lem3079136) (@lem0)). Qed.
Lemma lem3079138 : term189.
Proof. exact (@lem3079127 (@lem3079137)). Qed.
Lemma lem3079140 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079141 : term104 = term105.
Proof. exact (@lem3079140 term75 term75). Qed.
Lemma lem3079142 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079143 : term107 = term75.
Proof. exact (EQ_MP (@lem3079142) (@lem940073)). Qed.
Lemma lem3079144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079145 : term105 = term74.
Proof. exact (MK_COMB (@lem3079144) (@lem3079143)). Qed.
Lemma lem3079146 : term104 = term74.
Proof. exact (TRANS (@lem3079141) (@lem3079145)). Qed.
Lemma lem3079148 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079149 : term122 = term127.
Proof. exact (@lem3079148 term75 term75). Qed.
Lemma lem3079150 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079151 : term107 = term75.
Proof. exact (EQ_MP (@lem3079150) (@lem940073)). Qed.
Lemma lem3079152 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079153 : term105 = term74.
Proof. exact (MK_COMB (@lem3079152) (@lem3079151)). Qed.
Lemma lem3079154 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079155 : term127 = term95.
Proof. exact (MK_COMB (@lem3079154) (@lem3079153)). Qed.
Lemma lem3079156 : term122 = term95.
Proof. exact (TRANS (@lem3079149) (@lem3079155)). Qed.
Lemma lem3079157 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079158 : term190 = term182.
Proof. exact (MK_COMB (@lem3079157) (@lem3079156)). Qed.
Lemma lem3079159 : term191 = term184.
Proof. exact (MK_COMB (@lem3079158) (@lem3079146)). Qed.
Lemma lem3079161 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3079162 : term184 = term61.
Proof. exact (@lem3079161 term75). Qed.
Lemma lem3079163 : term191 = term61.
Proof. exact (TRANS (@lem3079159) (@lem3079162)). Qed.
Lemma lem3079164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3079165 : term193 = term194.
Proof. exact (MK_COMB (@lem3079164) (@lem3079163)). Qed.
Lemma lem3079166 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3079167 : term195 = term161.
Proof. exact (MK_COMB (@lem3079165) (@lem3079166)). Qed.
Lemma lem3079169 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079170 : term161 = term61.
Proof. exact (@lem3079169 term75). Qed.
Lemma lem3079171 : term195 = term61.
Proof. exact (TRANS (@lem3079167) (@lem3079170)). Qed.
Lemma lem3079173 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079174 : term104 = term105.
Proof. exact (@lem3079173 term75 term75). Qed.
Lemma lem3079175 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079176 : term107 = term75.
Proof. exact (EQ_MP (@lem3079175) (@lem940073)). Qed.
Lemma lem3079177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079178 : term105 = term74.
Proof. exact (MK_COMB (@lem3079177) (@lem3079176)). Qed.
Lemma lem3079179 : term104 = term74.
Proof. exact (TRANS (@lem3079174) (@lem3079178)). Qed.
Lemma lem3079180 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3079181 : term196 = term161.
Proof. exact (MK_COMB (@lem3079180) (@lem3079179)). Qed.
Lemma lem3079183 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079184 : term161 = term61.
Proof. exact (@lem3079183 term75). Qed.
Lemma lem3079185 : term196 = term61.
Proof. exact (TRANS (@lem3079181) (@lem3079184)). Qed.
Lemma lem3079186 : term61 = term196.
Proof. exact (SYM (@lem3079185)). Qed.
Lemma lem3079187 : term195 = term196.
Proof. exact (TRANS (@lem3079171) (@lem3079186)). Qed.
Lemma lem3079188 : term185 = term92.
Proof. exact (@lem3079138 (@lem3079187)). Qed.
Lemma lem3079189 : term184 = term92.
Proof. exact (TRANS (@lem3079104) (@lem3079188)). Qed.
Lemma lem3079191 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3079192 : term92 = term61.
Proof. exact (@lem3079191 term61). Qed.
Lemma lem3079193 : term184 = term61.
Proof. exact (TRANS (@lem3079189) (@lem3079192)). Qed.
Lemma lem3079194 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3079195 : term197 = term194.
Proof. exact (MK_COMB (@lem3079194) (@lem3079193)). Qed.
Lemma lem3079196 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3079197 (_32061 : int) : (term181 _32061) = (term198 _32061).
Proof. exact (MK_COMB (@lem3079195) (@lem3079196 _32061)). Qed.
Lemma lem3079198 (_32061 : int) : (term180 _32061) = (term198 _32061).
Proof. exact (TRANS (@lem3079095 _32061) (@lem3079197 _32061)). Qed.
Lemma lem3079199 (_32061 : int) : (term198 _32061) = term61.
Proof. exact (@lem1982719 (real_of_int _32061)). Qed.
Lemma lem3079200 (_32061 : int) : (term180 _32061) = term61.
Proof. exact (TRANS (@lem3079198 _32061) (@lem3079199 _32061)). Qed.
Lemma lem3079201 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079202 (_32061 : int) : (term199 _32061) = term200.
Proof. exact (MK_COMB (@lem3079201) (@lem3079200 _32061)). Qed.
Lemma lem3079203 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3079204 (_32061 : int) : (term791 _32061) = term205.
Proof. exact (MK_COMB (@lem3079202 _32061) (@lem3079203)). Qed.
Lemma lem3079205 (_32061 : int) : (term790 _32061) = term205.
Proof. exact (TRANS (@lem3079094 _32061) (@lem3079204 _32061)). Qed.
Lemma lem3079206 : term205 = term95.
Proof. exact (@lem1982721 term95). Qed.
Lemma lem3079207 (_32061 : int) : (term790 _32061) = term95.
Proof. exact (TRANS (@lem3079205 _32061) (@lem3079206)). Qed.
Lemma lem3079208 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3079209 (_32061 : int) : (term792 _32061) = term207.
Proof. exact (MK_COMB (@lem3079208) (@lem3079207 _32061)). Qed.
Lemma lem3079210 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3079211 (_32061 : int) : (term789 _32061) = term208.
Proof. exact (MK_COMB (@lem3079209 _32061) (@lem3079210)). Qed.
Lemma lem3079212 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : term208.
Proof. exact (EQ_MP (@lem3079211 _32061) (@lem3079093 _32061 _32062 h1)). Qed.
Lemma lem3079214 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3079215 : term208 = term209.
Proof. exact (@lem3079214 term61 term95). Qed.
Lemma lem3079217 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3079218 : term95 = term96.
Proof. exact (@lem3079217 term75). Qed.
Lemma lem3079220 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079221 : term61 = term92.
Proof. exact (@lem3079220 (NUMERAL 0)). Qed.
Lemma lem3079222 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3079223 : term63 = term210.
Proof. exact (MK_COMB (@lem3079222) (@lem3079221)). Qed.
Lemma lem3079224 : term209 = term211.
Proof. exact (MK_COMB (@lem3079223) (@lem3079218)). Qed.
Lemma lem3079225 : term212.
Proof. exact (@lem1980026 term61 term74 term95 term74). Qed.
Lemma lem3079227 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079228 : term150 = term156.
Proof. exact (@lem3079227 (NUMERAL 0) term75). Qed.
Lemma lem3079229 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079230 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079231 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079230 h1) (fun h1 : term156 = True => @lem3079229)). Qed.
Lemma lem3079232 : term156 = True.
Proof. exact (EQ_MP (@lem3079231) (@lem3079229)). Qed.
Lemma lem3079233 : term150 = True.
Proof. exact (TRANS (@lem3079228) (@lem3079232)). Qed.
Lemma lem3079234 : True = term150.
Proof. exact (SYM (@lem3079233)). Qed.
Lemma lem3079235 : term150.
Proof. exact (EQ_MP (@lem3079234) (@lem0)). Qed.
Lemma lem3079236 : term213.
Proof. exact (@lem3079225 (@lem3079235)). Qed.
Lemma lem3079238 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079239 : term150 = term156.
Proof. exact (@lem3079238 (NUMERAL 0) term75). Qed.
Lemma lem3079240 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079241 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079242 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079241 h1) (fun h1 : term156 = True => @lem3079240)). Qed.
Lemma lem3079243 : term156 = True.
Proof. exact (EQ_MP (@lem3079242) (@lem3079240)). Qed.
Lemma lem3079244 : term150 = True.
Proof. exact (TRANS (@lem3079239) (@lem3079243)). Qed.
Lemma lem3079245 : True = term150.
Proof. exact (SYM (@lem3079244)). Qed.
Lemma lem3079246 : term150.
Proof. exact (EQ_MP (@lem3079245) (@lem0)). Qed.
Lemma lem3079247 : term211 = term214.
Proof. exact (@lem3079236 (@lem3079246)). Qed.
Lemma lem3079249 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079250 : term122 = term127.
Proof. exact (@lem3079249 term75 term75). Qed.
Lemma lem3079251 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079252 : term107 = term75.
Proof. exact (EQ_MP (@lem3079251) (@lem940073)). Qed.
Lemma lem3079253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079254 : term105 = term74.
Proof. exact (MK_COMB (@lem3079253) (@lem3079252)). Qed.
Lemma lem3079255 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079256 : term127 = term95.
Proof. exact (MK_COMB (@lem3079255) (@lem3079254)). Qed.
Lemma lem3079257 : term122 = term95.
Proof. exact (TRANS (@lem3079250) (@lem3079256)). Qed.
Lemma lem3079259 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079260 : term161 = term61.
Proof. exact (@lem3079259 term75). Qed.
Lemma lem3079261 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3079262 : term215 = term63.
Proof. exact (MK_COMB (@lem3079261) (@lem3079260)). Qed.
Lemma lem3079263 : term214 = term209.
Proof. exact (MK_COMB (@lem3079262) (@lem3079257)). Qed.
Lemma lem3079265 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3079266 : term209 = term218.
Proof. exact (@lem3079265 (NUMERAL 0) term75). Qed.
Lemma lem3079267 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079268 (h1 : term157 = (BIT1 0)) : (term75 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3079269 : (term157 = (BIT1 0)) = ((term75 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079268 h1) (fun h1 : (term75 = (NUMERAL 0)) = False => @lem3079267)). Qed.
Lemma lem3079270 : (term75 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3079269) (@lem3079267)). Qed.
Lemma lem3079271 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3079272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3079273 : term219 = (and True).
Proof. exact (MK_COMB (@lem3079272) (@lem3079271)). Qed.
Lemma lem3079274 : term218 = (True /\ False).
Proof. exact (MK_COMB (@lem3079273) (@lem3079270)). Qed.
Lemma lem3079276 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3079277 : term218 = False.
Proof. exact (TRANS (@lem3079274) (@lem3079276)). Qed.
Lemma lem3079278 : term209 = False.
Proof. exact (TRANS (@lem3079266) (@lem3079277)). Qed.
Lemma lem3079279 : term214 = False.
Proof. exact (TRANS (@lem3079263) (@lem3079278)). Qed.
Lemma lem3079280 : term211 = False.
Proof. exact (TRANS (@lem3079247) (@lem3079279)). Qed.
Lemma lem3079281 : term209 = False.
Proof. exact (TRANS (@lem3079224) (@lem3079280)). Qed.
Lemma lem3079282 : term208 = False.
Proof. exact (TRANS (@lem3079215) (@lem3079281)). Qed.
Lemma lem3079283 (_32061 : int) (_32062 : int) (h1 : term776 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3079282) (@lem3079212 _32061 _32062 h1)). Qed.
Lemma lem3079284 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term793 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3079285 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term769 _32061 _32062.
Proof. exact (proj2 (@lem3079284 _32061 _32062 h1)). Qed.
Lemma lem3079287 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term738 _32061 _32062.
Proof. exact (proj2 (@lem3079285 _32061 _32062 h1)). Qed.
Lemma lem3079289 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term702 _32061 _32062.
Proof. exact (proj2 (@lem3079287 _32061 _32062 h1)). Qed.
Lemma lem3079290 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term694 _32061 _32062.
Proof. exact (proj1 (@lem3079287 _32061 _32062 h1)). Qed.
Lemma lem3079292 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term643 _32061.
Proof. exact (proj1 (@lem3079290 _32061 _32062 h1)). Qed.
Lemma lem3079294 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term634 _32061.
Proof. exact (proj1 (@lem3079289 _32061 _32062 h1)). Qed.
Lemma lem3079296 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3079297 : term149 = term150.
Proof. exact (@lem3079296 term61 term74). Qed.
Lemma lem3079299 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079300 : term74 = term121.
Proof. exact (@lem3079299 term75). Qed.
Lemma lem3079302 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079303 : term61 = term92.
Proof. exact (@lem3079302 (NUMERAL 0)). Qed.
Lemma lem3079304 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079305 : term151 = term152.
Proof. exact (MK_COMB (@lem3079304) (@lem3079303)). Qed.
Lemma lem3079306 : term150 = term153.
Proof. exact (MK_COMB (@lem3079305) (@lem3079300)). Qed.
Lemma lem3079307 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3079309 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079310 : term150 = term156.
Proof. exact (@lem3079309 (NUMERAL 0) term75). Qed.
Lemma lem3079311 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079312 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079313 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079312 h1) (fun h1 : term156 = True => @lem3079311)). Qed.
Lemma lem3079314 : term156 = True.
Proof. exact (EQ_MP (@lem3079313) (@lem3079311)). Qed.
Lemma lem3079315 : term150 = True.
Proof. exact (TRANS (@lem3079310) (@lem3079314)). Qed.
Lemma lem3079316 : True = term150.
Proof. exact (SYM (@lem3079315)). Qed.
Lemma lem3079317 : term150.
Proof. exact (EQ_MP (@lem3079316) (@lem0)). Qed.
Lemma lem3079318 : term158.
Proof. exact (@lem3079307 (@lem3079317)). Qed.
Lemma lem3079320 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079321 : term150 = term156.
Proof. exact (@lem3079320 (NUMERAL 0) term75). Qed.
Lemma lem3079322 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079323 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079324 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079323 h1) (fun h1 : term156 = True => @lem3079322)). Qed.
Lemma lem3079325 : term156 = True.
Proof. exact (EQ_MP (@lem3079324) (@lem3079322)). Qed.
Lemma lem3079326 : term150 = True.
Proof. exact (TRANS (@lem3079321) (@lem3079325)). Qed.
Lemma lem3079327 : True = term150.
Proof. exact (SYM (@lem3079326)). Qed.
Lemma lem3079328 : term150.
Proof. exact (EQ_MP (@lem3079327) (@lem0)). Qed.
Lemma lem3079329 : term153 = term159.
Proof. exact (@lem3079318 (@lem3079328)). Qed.
Lemma lem3079331 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079332 : term104 = term105.
Proof. exact (@lem3079331 term75 term75). Qed.
Lemma lem3079333 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079334 : term107 = term75.
Proof. exact (EQ_MP (@lem3079333) (@lem940073)). Qed.
Lemma lem3079335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079336 : term105 = term74.
Proof. exact (MK_COMB (@lem3079335) (@lem3079334)). Qed.
Lemma lem3079337 : term104 = term74.
Proof. exact (TRANS (@lem3079332) (@lem3079336)). Qed.
Lemma lem3079339 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079340 : term161 = term61.
Proof. exact (@lem3079339 term75). Qed.
Lemma lem3079341 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079342 : term162 = term151.
Proof. exact (MK_COMB (@lem3079341) (@lem3079340)). Qed.
Lemma lem3079343 : term159 = term150.
Proof. exact (MK_COMB (@lem3079342) (@lem3079337)). Qed.
Lemma lem3079345 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079346 : term150 = term156.
Proof. exact (@lem3079345 (NUMERAL 0) term75). Qed.
Lemma lem3079347 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079348 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079349 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079348 h1) (fun h1 : term156 = True => @lem3079347)). Qed.
Lemma lem3079350 : term156 = True.
Proof. exact (EQ_MP (@lem3079349) (@lem3079347)). Qed.
Lemma lem3079351 : term150 = True.
Proof. exact (TRANS (@lem3079346) (@lem3079350)). Qed.
Lemma lem3079352 : term159 = True.
Proof. exact (TRANS (@lem3079343) (@lem3079351)). Qed.
Lemma lem3079353 : term153 = True.
Proof. exact (TRANS (@lem3079329) (@lem3079352)). Qed.
Lemma lem3079354 : term150 = True.
Proof. exact (TRANS (@lem3079306) (@lem3079353)). Qed.
Lemma lem3079355 : term149 = True.
Proof. exact (TRANS (@lem3079297) (@lem3079354)). Qed.
Lemma lem3079356 : True = term149.
Proof. exact (SYM (@lem3079355)). Qed.
Lemma lem3079357 : term149.
Proof. exact (EQ_MP (@lem3079356) (@lem0)). Qed.
Lemma lem3079358 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term794 _32061.
Proof. exact (conj (@lem3079357) (@lem3079292 _32061 _32062 h1)). Qed.
Lemma lem3079360 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3079361 (_32061 : int) : term795 _32061.
Proof. exact (@lem3079360 term74 (term640 _32061)). Qed.
Lemma lem3079362 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term796 _32061.
Proof. exact (@lem3079361 _32061 (@lem3079358 _32061 _32062 h1)). Qed.
Lemma lem3079363 (_32061 : int) : (term797 _32061) = (term640 _32061).
Proof. exact (@lem1982733 (term640 _32061)). Qed.
Lemma lem3079364 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3079365 (_32061 : int) : (term798 _32061) = (term642 _32061).
Proof. exact (MK_COMB (@lem3079364) (@lem3079363 _32061)). Qed.
Lemma lem3079366 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3079367 (_32061 : int) : (term796 _32061) = (term643 _32061).
Proof. exact (MK_COMB (@lem3079365 _32061) (@lem3079366)). Qed.
Lemma lem3079368 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term643 _32061.
Proof. exact (EQ_MP (@lem3079367 _32061) (@lem3079362 _32061 _32062 h1)). Qed.
Lemma lem3079370 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3079371 : term149 = term150.
Proof. exact (@lem3079370 term61 term74). Qed.
Lemma lem3079373 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079374 : term74 = term121.
Proof. exact (@lem3079373 term75). Qed.
Lemma lem3079376 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079377 : term61 = term92.
Proof. exact (@lem3079376 (NUMERAL 0)). Qed.
Lemma lem3079378 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079379 : term151 = term152.
Proof. exact (MK_COMB (@lem3079378) (@lem3079377)). Qed.
Lemma lem3079380 : term150 = term153.
Proof. exact (MK_COMB (@lem3079379) (@lem3079374)). Qed.
Lemma lem3079381 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3079383 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079384 : term150 = term156.
Proof. exact (@lem3079383 (NUMERAL 0) term75). Qed.
Lemma lem3079385 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079386 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079387 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079386 h1) (fun h1 : term156 = True => @lem3079385)). Qed.
Lemma lem3079388 : term156 = True.
Proof. exact (EQ_MP (@lem3079387) (@lem3079385)). Qed.
Lemma lem3079389 : term150 = True.
Proof. exact (TRANS (@lem3079384) (@lem3079388)). Qed.
Lemma lem3079390 : True = term150.
Proof. exact (SYM (@lem3079389)). Qed.
Lemma lem3079391 : term150.
Proof. exact (EQ_MP (@lem3079390) (@lem0)). Qed.
Lemma lem3079392 : term158.
Proof. exact (@lem3079381 (@lem3079391)). Qed.
Lemma lem3079394 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079395 : term150 = term156.
Proof. exact (@lem3079394 (NUMERAL 0) term75). Qed.
Lemma lem3079396 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079397 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079398 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079397 h1) (fun h1 : term156 = True => @lem3079396)). Qed.
Lemma lem3079399 : term156 = True.
Proof. exact (EQ_MP (@lem3079398) (@lem3079396)). Qed.
Lemma lem3079400 : term150 = True.
Proof. exact (TRANS (@lem3079395) (@lem3079399)). Qed.
Lemma lem3079401 : True = term150.
Proof. exact (SYM (@lem3079400)). Qed.
Lemma lem3079402 : term150.
Proof. exact (EQ_MP (@lem3079401) (@lem0)). Qed.
Lemma lem3079403 : term153 = term159.
Proof. exact (@lem3079392 (@lem3079402)). Qed.
Lemma lem3079405 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079406 : term104 = term105.
Proof. exact (@lem3079405 term75 term75). Qed.
Lemma lem3079407 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079408 : term107 = term75.
Proof. exact (EQ_MP (@lem3079407) (@lem940073)). Qed.
Lemma lem3079409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079410 : term105 = term74.
Proof. exact (MK_COMB (@lem3079409) (@lem3079408)). Qed.
Lemma lem3079411 : term104 = term74.
Proof. exact (TRANS (@lem3079406) (@lem3079410)). Qed.
Lemma lem3079413 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079414 : term161 = term61.
Proof. exact (@lem3079413 term75). Qed.
Lemma lem3079415 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079416 : term162 = term151.
Proof. exact (MK_COMB (@lem3079415) (@lem3079414)). Qed.
Lemma lem3079417 : term159 = term150.
Proof. exact (MK_COMB (@lem3079416) (@lem3079411)). Qed.
Lemma lem3079419 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079420 : term150 = term156.
Proof. exact (@lem3079419 (NUMERAL 0) term75). Qed.
Lemma lem3079421 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079422 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079423 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079422 h1) (fun h1 : term156 = True => @lem3079421)). Qed.
Lemma lem3079424 : term156 = True.
Proof. exact (EQ_MP (@lem3079423) (@lem3079421)). Qed.
Lemma lem3079425 : term150 = True.
Proof. exact (TRANS (@lem3079420) (@lem3079424)). Qed.
Lemma lem3079426 : term159 = True.
Proof. exact (TRANS (@lem3079417) (@lem3079425)). Qed.
Lemma lem3079427 : term153 = True.
Proof. exact (TRANS (@lem3079403) (@lem3079426)). Qed.
Lemma lem3079428 : term150 = True.
Proof. exact (TRANS (@lem3079380) (@lem3079427)). Qed.
Lemma lem3079429 : term149 = True.
Proof. exact (TRANS (@lem3079371) (@lem3079428)). Qed.
Lemma lem3079430 : True = term149.
Proof. exact (SYM (@lem3079429)). Qed.
Lemma lem3079431 : term149.
Proof. exact (EQ_MP (@lem3079430) (@lem0)). Qed.
Lemma lem3079432 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term782 _32061.
Proof. exact (conj (@lem3079431) (@lem3079294 _32061 _32062 h1)). Qed.
Lemma lem3079434 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3079435 (_32061 : int) : term783 _32061.
Proof. exact (@lem3079434 term74 (term131 _32061)). Qed.
Lemma lem3079436 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term784 _32061.
Proof. exact (@lem3079435 _32061 (@lem3079432 _32061 _32062 h1)). Qed.
Lemma lem3079437 (_32061 : int) : (term785 _32061) = (term131 _32061).
Proof. exact (@lem1982733 (term131 _32061)). Qed.
Lemma lem3079438 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3079439 (_32061 : int) : (term786 _32061) = (term633 _32061).
Proof. exact (MK_COMB (@lem3079438) (@lem3079437 _32061)). Qed.
Lemma lem3079440 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3079441 (_32061 : int) : (term784 _32061) = (term634 _32061).
Proof. exact (MK_COMB (@lem3079439 _32061) (@lem3079440)). Qed.
Lemma lem3079442 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term634 _32061.
Proof. exact (EQ_MP (@lem3079441 _32061) (@lem3079436 _32061 _32062 h1)). Qed.
Lemma lem3079443 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term799 _32061.
Proof. exact (conj (@lem3079442 _32061 _32062 h1) (@lem3079368 _32061 _32062 h1)). Qed.
Lemma lem3079445 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3079446 (_32061 : int) : term800 _32061.
Proof. exact (@lem3079445 (term131 _32061) (term640 _32061)). Qed.
Lemma lem3079447 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term801 _32061.
Proof. exact (@lem3079446 _32061 (@lem3079443 _32061 _32062 h1)). Qed.
Lemma lem3079448 (_32061 : int) : (term802 _32061) = (term803 _32061).
Proof. exact (@lem1982753 (term140 _32061) (real_of_int _32061) term95 term95). Qed.
Lemma lem3079449 (_32061 : int) : (term180 _32061) = (term181 _32061).
Proof. exact (@lem1982713 term95 (real_of_int _32061)). Qed.
Lemma lem3079451 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079452 : term74 = term121.
Proof. exact (@lem3079451 term75). Qed.
Lemma lem3079454 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3079455 : term95 = term96.
Proof. exact (@lem3079454 term75). Qed.
Lemma lem3079456 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079457 : term182 = term183.
Proof. exact (MK_COMB (@lem3079456) (@lem3079455)). Qed.
Lemma lem3079458 : term184 = term185.
Proof. exact (MK_COMB (@lem3079457) (@lem3079452)). Qed.
Lemma lem3079459 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3079461 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079462 : term150 = term156.
Proof. exact (@lem3079461 (NUMERAL 0) term75). Qed.
Lemma lem3079463 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079464 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079465 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079464 h1) (fun h1 : term156 = True => @lem3079463)). Qed.
Lemma lem3079466 : term156 = True.
Proof. exact (EQ_MP (@lem3079465) (@lem3079463)). Qed.
Lemma lem3079467 : term150 = True.
Proof. exact (TRANS (@lem3079462) (@lem3079466)). Qed.
Lemma lem3079468 : True = term150.
Proof. exact (SYM (@lem3079467)). Qed.
Lemma lem3079469 : term150.
Proof. exact (EQ_MP (@lem3079468) (@lem0)). Qed.
Lemma lem3079470 : term187.
Proof. exact (@lem3079459 (@lem3079469)). Qed.
Lemma lem3079472 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079473 : term150 = term156.
Proof. exact (@lem3079472 (NUMERAL 0) term75). Qed.
Lemma lem3079474 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079475 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079476 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079475 h1) (fun h1 : term156 = True => @lem3079474)). Qed.
Lemma lem3079477 : term156 = True.
Proof. exact (EQ_MP (@lem3079476) (@lem3079474)). Qed.
Lemma lem3079478 : term150 = True.
Proof. exact (TRANS (@lem3079473) (@lem3079477)). Qed.
Lemma lem3079479 : True = term150.
Proof. exact (SYM (@lem3079478)). Qed.
Lemma lem3079480 : term150.
Proof. exact (EQ_MP (@lem3079479) (@lem0)). Qed.
Lemma lem3079481 : term188.
Proof. exact (@lem3079470 (@lem3079480)). Qed.
Lemma lem3079483 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079484 : term150 = term156.
Proof. exact (@lem3079483 (NUMERAL 0) term75). Qed.
Lemma lem3079485 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079486 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079487 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079486 h1) (fun h1 : term156 = True => @lem3079485)). Qed.
Lemma lem3079488 : term156 = True.
Proof. exact (EQ_MP (@lem3079487) (@lem3079485)). Qed.
Lemma lem3079489 : term150 = True.
Proof. exact (TRANS (@lem3079484) (@lem3079488)). Qed.
Lemma lem3079490 : True = term150.
Proof. exact (SYM (@lem3079489)). Qed.
Lemma lem3079491 : term150.
Proof. exact (EQ_MP (@lem3079490) (@lem0)). Qed.
Lemma lem3079492 : term189.
Proof. exact (@lem3079481 (@lem3079491)). Qed.
Lemma lem3079494 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079495 : term104 = term105.
Proof. exact (@lem3079494 term75 term75). Qed.
Lemma lem3079496 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079497 : term107 = term75.
Proof. exact (EQ_MP (@lem3079496) (@lem940073)). Qed.
Lemma lem3079498 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079499 : term105 = term74.
Proof. exact (MK_COMB (@lem3079498) (@lem3079497)). Qed.
Lemma lem3079500 : term104 = term74.
Proof. exact (TRANS (@lem3079495) (@lem3079499)). Qed.
Lemma lem3079502 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079503 : term122 = term127.
Proof. exact (@lem3079502 term75 term75). Qed.
Lemma lem3079504 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079505 : term107 = term75.
Proof. exact (EQ_MP (@lem3079504) (@lem940073)). Qed.
Lemma lem3079506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079507 : term105 = term74.
Proof. exact (MK_COMB (@lem3079506) (@lem3079505)). Qed.
Lemma lem3079508 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079509 : term127 = term95.
Proof. exact (MK_COMB (@lem3079508) (@lem3079507)). Qed.
Lemma lem3079510 : term122 = term95.
Proof. exact (TRANS (@lem3079503) (@lem3079509)). Qed.
Lemma lem3079511 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079512 : term190 = term182.
Proof. exact (MK_COMB (@lem3079511) (@lem3079510)). Qed.
Lemma lem3079513 : term191 = term184.
Proof. exact (MK_COMB (@lem3079512) (@lem3079500)). Qed.
Lemma lem3079515 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3079516 : term184 = term61.
Proof. exact (@lem3079515 term75). Qed.
Lemma lem3079517 : term191 = term61.
Proof. exact (TRANS (@lem3079513) (@lem3079516)). Qed.
Lemma lem3079518 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3079519 : term193 = term194.
Proof. exact (MK_COMB (@lem3079518) (@lem3079517)). Qed.
Lemma lem3079520 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3079521 : term195 = term161.
Proof. exact (MK_COMB (@lem3079519) (@lem3079520)). Qed.
Lemma lem3079523 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079524 : term161 = term61.
Proof. exact (@lem3079523 term75). Qed.
Lemma lem3079525 : term195 = term61.
Proof. exact (TRANS (@lem3079521) (@lem3079524)). Qed.
Lemma lem3079527 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079528 : term104 = term105.
Proof. exact (@lem3079527 term75 term75). Qed.
Lemma lem3079529 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079530 : term107 = term75.
Proof. exact (EQ_MP (@lem3079529) (@lem940073)). Qed.
Lemma lem3079531 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079532 : term105 = term74.
Proof. exact (MK_COMB (@lem3079531) (@lem3079530)). Qed.
Lemma lem3079533 : term104 = term74.
Proof. exact (TRANS (@lem3079528) (@lem3079532)). Qed.
Lemma lem3079534 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3079535 : term196 = term161.
Proof. exact (MK_COMB (@lem3079534) (@lem3079533)). Qed.
Lemma lem3079537 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079538 : term161 = term61.
Proof. exact (@lem3079537 term75). Qed.
Lemma lem3079539 : term196 = term61.
Proof. exact (TRANS (@lem3079535) (@lem3079538)). Qed.
Lemma lem3079540 : term61 = term196.
Proof. exact (SYM (@lem3079539)). Qed.
Lemma lem3079541 : term195 = term196.
Proof. exact (TRANS (@lem3079525) (@lem3079540)). Qed.
Lemma lem3079542 : term185 = term92.
Proof. exact (@lem3079492 (@lem3079541)). Qed.
Lemma lem3079543 : term184 = term92.
Proof. exact (TRANS (@lem3079458) (@lem3079542)). Qed.
Lemma lem3079545 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3079546 : term92 = term61.
Proof. exact (@lem3079545 term61). Qed.
Lemma lem3079547 : term184 = term61.
Proof. exact (TRANS (@lem3079543) (@lem3079546)). Qed.
Lemma lem3079548 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3079549 : term197 = term194.
Proof. exact (MK_COMB (@lem3079548) (@lem3079547)). Qed.
Lemma lem3079550 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3079551 (_32061 : int) : (term181 _32061) = (term198 _32061).
Proof. exact (MK_COMB (@lem3079549) (@lem3079550 _32061)). Qed.
Lemma lem3079552 (_32061 : int) : (term180 _32061) = (term198 _32061).
Proof. exact (TRANS (@lem3079449 _32061) (@lem3079551 _32061)). Qed.
Lemma lem3079553 (_32061 : int) : (term198 _32061) = term61.
Proof. exact (@lem1982719 (real_of_int _32061)). Qed.
Lemma lem3079554 (_32061 : int) : (term180 _32061) = term61.
Proof. exact (TRANS (@lem3079552 _32061) (@lem3079553 _32061)). Qed.
Lemma lem3079555 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079556 (_32061 : int) : (term199 _32061) = term200.
Proof. exact (MK_COMB (@lem3079555) (@lem3079554 _32061)). Qed.
Lemma lem3079558 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3079559 : term95 = term96.
Proof. exact (@lem3079558 term75). Qed.
Lemma lem3079561 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3079562 : term95 = term96.
Proof. exact (@lem3079561 term75). Qed.
Lemma lem3079563 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079564 : term182 = term183.
Proof. exact (MK_COMB (@lem3079563) (@lem3079562)). Qed.
Lemma lem3079565 : term804 = term805.
Proof. exact (MK_COMB (@lem3079564) (@lem3079559)). Qed.
Lemma lem3079566 : term806.
Proof. exact (@lem1981473 term95 term74 term95 term74 term807 term74). Qed.
Lemma lem3079568 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079569 : term150 = term156.
Proof. exact (@lem3079568 (NUMERAL 0) term75). Qed.
Lemma lem3079570 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079571 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079572 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079571 h1) (fun h1 : term156 = True => @lem3079570)). Qed.
Lemma lem3079573 : term156 = True.
Proof. exact (EQ_MP (@lem3079572) (@lem3079570)). Qed.
Lemma lem3079574 : term150 = True.
Proof. exact (TRANS (@lem3079569) (@lem3079573)). Qed.
Lemma lem3079575 : True = term150.
Proof. exact (SYM (@lem3079574)). Qed.
Lemma lem3079576 : term150.
Proof. exact (EQ_MP (@lem3079575) (@lem0)). Qed.
Lemma lem3079577 : term808.
Proof. exact (@lem3079566 (@lem3079576)). Qed.
Lemma lem3079579 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079580 : term150 = term156.
Proof. exact (@lem3079579 (NUMERAL 0) term75). Qed.
Lemma lem3079581 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079582 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079583 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079582 h1) (fun h1 : term156 = True => @lem3079581)). Qed.
Lemma lem3079584 : term156 = True.
Proof. exact (EQ_MP (@lem3079583) (@lem3079581)). Qed.
Lemma lem3079585 : term150 = True.
Proof. exact (TRANS (@lem3079580) (@lem3079584)). Qed.
Lemma lem3079586 : True = term150.
Proof. exact (SYM (@lem3079585)). Qed.
Lemma lem3079587 : term150.
Proof. exact (EQ_MP (@lem3079586) (@lem0)). Qed.
Lemma lem3079588 : term809.
Proof. exact (@lem3079577 (@lem3079587)). Qed.
Lemma lem3079590 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079591 : term150 = term156.
Proof. exact (@lem3079590 (NUMERAL 0) term75). Qed.
Lemma lem3079592 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079593 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079594 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079593 h1) (fun h1 : term156 = True => @lem3079592)). Qed.
Lemma lem3079595 : term156 = True.
Proof. exact (EQ_MP (@lem3079594) (@lem3079592)). Qed.
Lemma lem3079596 : term150 = True.
Proof. exact (TRANS (@lem3079591) (@lem3079595)). Qed.
Lemma lem3079597 : True = term150.
Proof. exact (SYM (@lem3079596)). Qed.
Lemma lem3079598 : term150.
Proof. exact (EQ_MP (@lem3079597) (@lem0)). Qed.
Lemma lem3079599 : term810.
Proof. exact (@lem3079588 (@lem3079598)). Qed.
Lemma lem3079601 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079602 : term122 = term127.
Proof. exact (@lem3079601 term75 term75). Qed.
Lemma lem3079603 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079604 : term107 = term75.
Proof. exact (EQ_MP (@lem3079603) (@lem940073)). Qed.
Lemma lem3079605 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079606 : term105 = term74.
Proof. exact (MK_COMB (@lem3079605) (@lem3079604)). Qed.
Lemma lem3079607 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079608 : term127 = term95.
Proof. exact (MK_COMB (@lem3079607) (@lem3079606)). Qed.
Lemma lem3079609 : term122 = term95.
Proof. exact (TRANS (@lem3079602) (@lem3079608)). Qed.
Lemma lem3079611 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079612 : term122 = term127.
Proof. exact (@lem3079611 term75 term75). Qed.
Lemma lem3079613 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079614 : term107 = term75.
Proof. exact (EQ_MP (@lem3079613) (@lem940073)). Qed.
Lemma lem3079615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079616 : term105 = term74.
Proof. exact (MK_COMB (@lem3079615) (@lem3079614)). Qed.
Lemma lem3079617 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079618 : term127 = term95.
Proof. exact (MK_COMB (@lem3079617) (@lem3079616)). Qed.
Lemma lem3079619 : term122 = term95.
Proof. exact (TRANS (@lem3079612) (@lem3079618)). Qed.
Lemma lem3079620 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079621 : term190 = term182.
Proof. exact (MK_COMB (@lem3079620) (@lem3079619)). Qed.
Lemma lem3079622 : term811 = term804.
Proof. exact (MK_COMB (@lem3079621) (@lem3079609)). Qed.
Lemma lem3079623 : term804 = term812.
Proof. exact (@lem1367763 term75 term75). Qed.
Lemma lem3079624 : term813 = term814.
Proof. exact (@lem706885). Qed.
Lemma lem3079625 : (term813 = term814) = (term815 = term816).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term814). Qed.
Lemma lem3079626 : term815 = term816.
Proof. exact (EQ_MP (@lem3079625) (@lem3079624)). Qed.
Lemma lem3079627 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079628 : term817 = term818.
Proof. exact (MK_COMB (@lem3079627) (@lem3079626)). Qed.
Lemma lem3079629 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079630 : term812 = term807.
Proof. exact (MK_COMB (@lem3079629) (@lem3079628)). Qed.
Lemma lem3079631 : term804 = term807.
Proof. exact (TRANS (@lem3079623) (@lem3079630)). Qed.
Lemma lem3079632 : term811 = term807.
Proof. exact (TRANS (@lem3079622) (@lem3079631)). Qed.
Lemma lem3079633 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3079634 : term819 = term820.
Proof. exact (MK_COMB (@lem3079633) (@lem3079632)). Qed.
Lemma lem3079635 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3079636 : term821 = term822.
Proof. exact (MK_COMB (@lem3079634) (@lem3079635)). Qed.
Lemma lem3079638 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079639 : term822 = term823.
Proof. exact (@lem3079638 term816 term75). Qed.
Lemma lem3079640 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3079641 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3079642 : term825 = term816.
Proof. exact (EQ_MP (@lem3079641) (@lem3079640)). Qed.
Lemma lem3079643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079644 : term826 = term818.
Proof. exact (MK_COMB (@lem3079643) (@lem3079642)). Qed.
Lemma lem3079645 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079646 : term823 = term807.
Proof. exact (MK_COMB (@lem3079645) (@lem3079644)). Qed.
Lemma lem3079647 : term822 = term807.
Proof. exact (TRANS (@lem3079639) (@lem3079646)). Qed.
Lemma lem3079648 : term821 = term807.
Proof. exact (TRANS (@lem3079636) (@lem3079647)). Qed.
Lemma lem3079650 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079651 : term104 = term105.
Proof. exact (@lem3079650 term75 term75). Qed.
Lemma lem3079652 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079653 : term107 = term75.
Proof. exact (EQ_MP (@lem3079652) (@lem940073)). Qed.
Lemma lem3079654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079655 : term105 = term74.
Proof. exact (MK_COMB (@lem3079654) (@lem3079653)). Qed.
Lemma lem3079656 : term104 = term74.
Proof. exact (TRANS (@lem3079651) (@lem3079655)). Qed.
Lemma lem3079657 : term820 = term820.
Proof. exact (eq_refl term820). Qed.
Lemma lem3079658 : term827 = term822.
Proof. exact (MK_COMB (@lem3079657) (@lem3079656)). Qed.
Lemma lem3079660 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079661 : term822 = term823.
Proof. exact (@lem3079660 term816 term75). Qed.
Lemma lem3079662 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3079663 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3079664 : term825 = term816.
Proof. exact (EQ_MP (@lem3079663) (@lem3079662)). Qed.
Lemma lem3079665 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079666 : term826 = term818.
Proof. exact (MK_COMB (@lem3079665) (@lem3079664)). Qed.
Lemma lem3079667 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079668 : term823 = term807.
Proof. exact (MK_COMB (@lem3079667) (@lem3079666)). Qed.
Lemma lem3079669 : term822 = term807.
Proof. exact (TRANS (@lem3079661) (@lem3079668)). Qed.
Lemma lem3079670 : term827 = term807.
Proof. exact (TRANS (@lem3079658) (@lem3079669)). Qed.
Lemma lem3079671 : term807 = term827.
Proof. exact (SYM (@lem3079670)). Qed.
Lemma lem3079672 : term821 = term827.
Proof. exact (TRANS (@lem3079648) (@lem3079671)). Qed.
Lemma lem3079673 : term805 = term828.
Proof. exact (@lem3079599 (@lem3079672)). Qed.
Lemma lem3079674 : term804 = term828.
Proof. exact (TRANS (@lem3079565) (@lem3079673)). Qed.
Lemma lem3079676 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3079677 : term828 = term807.
Proof. exact (@lem3079676 term807). Qed.
Lemma lem3079678 : term804 = term807.
Proof. exact (TRANS (@lem3079674) (@lem3079677)). Qed.
Lemma lem3079679 (_32061 : int) : (term803 _32061) = term829.
Proof. exact (MK_COMB (@lem3079556 _32061) (@lem3079678)). Qed.
Lemma lem3079680 (_32061 : int) : (term802 _32061) = term829.
Proof. exact (TRANS (@lem3079448 _32061) (@lem3079679 _32061)). Qed.
Lemma lem3079681 : term829 = term807.
Proof. exact (@lem1982721 term807). Qed.
Lemma lem3079682 (_32061 : int) : (term802 _32061) = term807.
Proof. exact (TRANS (@lem3079680 _32061) (@lem3079681)). Qed.
Lemma lem3079683 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3079684 (_32061 : int) : (term830 _32061) = term831.
Proof. exact (MK_COMB (@lem3079683) (@lem3079682 _32061)). Qed.
Lemma lem3079685 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3079686 (_32061 : int) : (term801 _32061) = term832.
Proof. exact (MK_COMB (@lem3079684 _32061) (@lem3079685)). Qed.
Lemma lem3079687 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : term832.
Proof. exact (EQ_MP (@lem3079686 _32061) (@lem3079447 _32061 _32062 h1)). Qed.
Lemma lem3079689 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3079690 : term832 = term833.
Proof. exact (@lem3079689 term61 term807). Qed.
Lemma lem3079692 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3079693 : term807 = term828.
Proof. exact (@lem3079692 term816). Qed.
Lemma lem3079695 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079696 : term61 = term92.
Proof. exact (@lem3079695 (NUMERAL 0)). Qed.
Lemma lem3079697 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3079698 : term63 = term210.
Proof. exact (MK_COMB (@lem3079697) (@lem3079696)). Qed.
Lemma lem3079699 : term833 = term834.
Proof. exact (MK_COMB (@lem3079698) (@lem3079693)). Qed.
Lemma lem3079700 : term835.
Proof. exact (@lem1980026 term61 term74 term807 term74). Qed.
Lemma lem3079702 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079703 : term150 = term156.
Proof. exact (@lem3079702 (NUMERAL 0) term75). Qed.
Lemma lem3079704 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079705 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079706 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079705 h1) (fun h1 : term156 = True => @lem3079704)). Qed.
Lemma lem3079707 : term156 = True.
Proof. exact (EQ_MP (@lem3079706) (@lem3079704)). Qed.
Lemma lem3079708 : term150 = True.
Proof. exact (TRANS (@lem3079703) (@lem3079707)). Qed.
Lemma lem3079709 : True = term150.
Proof. exact (SYM (@lem3079708)). Qed.
Lemma lem3079710 : term150.
Proof. exact (EQ_MP (@lem3079709) (@lem0)). Qed.
Lemma lem3079711 : term836.
Proof. exact (@lem3079700 (@lem3079710)). Qed.
Lemma lem3079713 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079714 : term150 = term156.
Proof. exact (@lem3079713 (NUMERAL 0) term75). Qed.
Lemma lem3079715 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079716 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079717 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079716 h1) (fun h1 : term156 = True => @lem3079715)). Qed.
Lemma lem3079718 : term156 = True.
Proof. exact (EQ_MP (@lem3079717) (@lem3079715)). Qed.
Lemma lem3079719 : term150 = True.
Proof. exact (TRANS (@lem3079714) (@lem3079718)). Qed.
Lemma lem3079720 : True = term150.
Proof. exact (SYM (@lem3079719)). Qed.
Lemma lem3079721 : term150.
Proof. exact (EQ_MP (@lem3079720) (@lem0)). Qed.
Lemma lem3079722 : term834 = term837.
Proof. exact (@lem3079711 (@lem3079721)). Qed.
Lemma lem3079724 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079725 : term822 = term823.
Proof. exact (@lem3079724 term816 term75). Qed.
Lemma lem3079726 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3079727 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3079728 : term825 = term816.
Proof. exact (EQ_MP (@lem3079727) (@lem3079726)). Qed.
Lemma lem3079729 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079730 : term826 = term818.
Proof. exact (MK_COMB (@lem3079729) (@lem3079728)). Qed.
Lemma lem3079731 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079732 : term823 = term807.
Proof. exact (MK_COMB (@lem3079731) (@lem3079730)). Qed.
Lemma lem3079733 : term822 = term807.
Proof. exact (TRANS (@lem3079725) (@lem3079732)). Qed.
Lemma lem3079735 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079736 : term161 = term61.
Proof. exact (@lem3079735 term75). Qed.
Lemma lem3079737 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3079738 : term215 = term63.
Proof. exact (MK_COMB (@lem3079737) (@lem3079736)). Qed.
Lemma lem3079739 : term837 = term833.
Proof. exact (MK_COMB (@lem3079738) (@lem3079733)). Qed.
Lemma lem3079741 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3079742 : term833 = term838.
Proof. exact (@lem3079741 (NUMERAL 0) term816). Qed.
Lemma lem3079743 : term839 = term814.
Proof. exact (@lem912803). Qed.
Lemma lem3079744 (h1 : term839 = term814) : (term816 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term814 h1). Qed.
Lemma lem3079745 : (term839 = term814) = ((term816 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term839 = term814 => @lem3079744 h1) (fun h1 : (term816 = (NUMERAL 0)) = False => @lem3079743)). Qed.
Lemma lem3079746 : (term816 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3079745) (@lem3079743)). Qed.
Lemma lem3079747 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3079748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3079749 : term219 = (and True).
Proof. exact (MK_COMB (@lem3079748) (@lem3079747)). Qed.
Lemma lem3079750 : term838 = (True /\ False).
Proof. exact (MK_COMB (@lem3079749) (@lem3079746)). Qed.
Lemma lem3079752 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3079753 : term838 = False.
Proof. exact (TRANS (@lem3079750) (@lem3079752)). Qed.
Lemma lem3079754 : term833 = False.
Proof. exact (TRANS (@lem3079742) (@lem3079753)). Qed.
Lemma lem3079755 : term837 = False.
Proof. exact (TRANS (@lem3079739) (@lem3079754)). Qed.
Lemma lem3079756 : term834 = False.
Proof. exact (TRANS (@lem3079722) (@lem3079755)). Qed.
Lemma lem3079757 : term833 = False.
Proof. exact (TRANS (@lem3079699) (@lem3079756)). Qed.
Lemma lem3079758 : term832 = False.
Proof. exact (TRANS (@lem3079690) (@lem3079757)). Qed.
Lemma lem3079759 (_32061 : int) (_32062 : int) (h1 : term793 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3079758) (@lem3079687 _32061 _32062 h1)). Qed.
Lemma lem3079760 (_32061 : int) (_32062 : int) (h1 : term767 _32061 _32062) : False.
Proof. exact (or_elim (@lem3078929 _32061 _32062 h1) (fun h0 : term776 _32061 _32062 => @lem3079283 _32061 _32062 h0) (fun h0 : term793 _32061 _32062 => @lem3079759 _32061 _32062 h0)). Qed.
Lemma lem3079761 (_32061 : int) (_32062 : int) (h1 : term763 _32061 _32062) : term763 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3079762 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term840 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3079763 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term764 _32061 _32062.
Proof. exact (proj2 (@lem3079762 _32061 _32062 h1)). Qed.
Lemma lem3079765 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term733 _32061 _32062.
Proof. exact (proj2 (@lem3079763 _32061 _32062 h1)). Qed.
Lemma lem3079767 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term703 _32061 _32062.
Proof. exact (proj2 (@lem3079765 _32061 _32062 h1)). Qed.
Lemma lem3079768 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term693 _32061 _32062.
Proof. exact (proj1 (@lem3079765 _32061 _32062 h1)). Qed.
Lemma lem3079770 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term634 _32061.
Proof. exact (proj1 (@lem3079768 _32061 _32062 h1)). Qed.
Lemma lem3079772 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term643 _32061.
Proof. exact (proj1 (@lem3079767 _32061 _32062 h1)). Qed.
Lemma lem3079774 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3079775 : term149 = term150.
Proof. exact (@lem3079774 term61 term74). Qed.
Lemma lem3079777 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079778 : term74 = term121.
Proof. exact (@lem3079777 term75). Qed.
Lemma lem3079780 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079781 : term61 = term92.
Proof. exact (@lem3079780 (NUMERAL 0)). Qed.
Lemma lem3079782 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079783 : term151 = term152.
Proof. exact (MK_COMB (@lem3079782) (@lem3079781)). Qed.
Lemma lem3079784 : term150 = term153.
Proof. exact (MK_COMB (@lem3079783) (@lem3079778)). Qed.
Lemma lem3079785 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3079787 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079788 : term150 = term156.
Proof. exact (@lem3079787 (NUMERAL 0) term75). Qed.
Lemma lem3079789 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079790 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079791 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079790 h1) (fun h1 : term156 = True => @lem3079789)). Qed.
Lemma lem3079792 : term156 = True.
Proof. exact (EQ_MP (@lem3079791) (@lem3079789)). Qed.
Lemma lem3079793 : term150 = True.
Proof. exact (TRANS (@lem3079788) (@lem3079792)). Qed.
Lemma lem3079794 : True = term150.
Proof. exact (SYM (@lem3079793)). Qed.
Lemma lem3079795 : term150.
Proof. exact (EQ_MP (@lem3079794) (@lem0)). Qed.
Lemma lem3079796 : term158.
Proof. exact (@lem3079785 (@lem3079795)). Qed.
Lemma lem3079798 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079799 : term150 = term156.
Proof. exact (@lem3079798 (NUMERAL 0) term75). Qed.
Lemma lem3079800 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079801 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079802 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079801 h1) (fun h1 : term156 = True => @lem3079800)). Qed.
Lemma lem3079803 : term156 = True.
Proof. exact (EQ_MP (@lem3079802) (@lem3079800)). Qed.
Lemma lem3079804 : term150 = True.
Proof. exact (TRANS (@lem3079799) (@lem3079803)). Qed.
Lemma lem3079805 : True = term150.
Proof. exact (SYM (@lem3079804)). Qed.
Lemma lem3079806 : term150.
Proof. exact (EQ_MP (@lem3079805) (@lem0)). Qed.
Lemma lem3079807 : term153 = term159.
Proof. exact (@lem3079796 (@lem3079806)). Qed.
Lemma lem3079809 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079810 : term104 = term105.
Proof. exact (@lem3079809 term75 term75). Qed.
Lemma lem3079811 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079812 : term107 = term75.
Proof. exact (EQ_MP (@lem3079811) (@lem940073)). Qed.
Lemma lem3079813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079814 : term105 = term74.
Proof. exact (MK_COMB (@lem3079813) (@lem3079812)). Qed.
Lemma lem3079815 : term104 = term74.
Proof. exact (TRANS (@lem3079810) (@lem3079814)). Qed.
Lemma lem3079817 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079818 : term161 = term61.
Proof. exact (@lem3079817 term75). Qed.
Lemma lem3079819 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079820 : term162 = term151.
Proof. exact (MK_COMB (@lem3079819) (@lem3079818)). Qed.
Lemma lem3079821 : term159 = term150.
Proof. exact (MK_COMB (@lem3079820) (@lem3079815)). Qed.
Lemma lem3079823 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079824 : term150 = term156.
Proof. exact (@lem3079823 (NUMERAL 0) term75). Qed.
Lemma lem3079825 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079826 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079827 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079826 h1) (fun h1 : term156 = True => @lem3079825)). Qed.
Lemma lem3079828 : term156 = True.
Proof. exact (EQ_MP (@lem3079827) (@lem3079825)). Qed.
Lemma lem3079829 : term150 = True.
Proof. exact (TRANS (@lem3079824) (@lem3079828)). Qed.
Lemma lem3079830 : term159 = True.
Proof. exact (TRANS (@lem3079821) (@lem3079829)). Qed.
Lemma lem3079831 : term153 = True.
Proof. exact (TRANS (@lem3079807) (@lem3079830)). Qed.
Lemma lem3079832 : term150 = True.
Proof. exact (TRANS (@lem3079784) (@lem3079831)). Qed.
Lemma lem3079833 : term149 = True.
Proof. exact (TRANS (@lem3079775) (@lem3079832)). Qed.
Lemma lem3079834 : True = term149.
Proof. exact (SYM (@lem3079833)). Qed.
Lemma lem3079835 : term149.
Proof. exact (EQ_MP (@lem3079834) (@lem0)). Qed.
Lemma lem3079836 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term794 _32061.
Proof. exact (conj (@lem3079835) (@lem3079772 _32061 _32062 h1)). Qed.
Lemma lem3079838 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3079839 (_32061 : int) : term795 _32061.
Proof. exact (@lem3079838 term74 (term640 _32061)). Qed.
Lemma lem3079840 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term796 _32061.
Proof. exact (@lem3079839 _32061 (@lem3079836 _32061 _32062 h1)). Qed.
Lemma lem3079841 (_32061 : int) : (term797 _32061) = (term640 _32061).
Proof. exact (@lem1982733 (term640 _32061)). Qed.
Lemma lem3079842 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3079843 (_32061 : int) : (term798 _32061) = (term642 _32061).
Proof. exact (MK_COMB (@lem3079842) (@lem3079841 _32061)). Qed.
Lemma lem3079844 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3079845 (_32061 : int) : (term796 _32061) = (term643 _32061).
Proof. exact (MK_COMB (@lem3079843 _32061) (@lem3079844)). Qed.
Lemma lem3079846 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term643 _32061.
Proof. exact (EQ_MP (@lem3079845 _32061) (@lem3079840 _32061 _32062 h1)). Qed.
Lemma lem3079848 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3079849 : term149 = term150.
Proof. exact (@lem3079848 term61 term74). Qed.
Lemma lem3079851 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079852 : term74 = term121.
Proof. exact (@lem3079851 term75). Qed.
Lemma lem3079854 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079855 : term61 = term92.
Proof. exact (@lem3079854 (NUMERAL 0)). Qed.
Lemma lem3079856 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079857 : term151 = term152.
Proof. exact (MK_COMB (@lem3079856) (@lem3079855)). Qed.
Lemma lem3079858 : term150 = term153.
Proof. exact (MK_COMB (@lem3079857) (@lem3079852)). Qed.
Lemma lem3079859 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3079861 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079862 : term150 = term156.
Proof. exact (@lem3079861 (NUMERAL 0) term75). Qed.
Lemma lem3079863 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079864 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079865 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079864 h1) (fun h1 : term156 = True => @lem3079863)). Qed.
Lemma lem3079866 : term156 = True.
Proof. exact (EQ_MP (@lem3079865) (@lem3079863)). Qed.
Lemma lem3079867 : term150 = True.
Proof. exact (TRANS (@lem3079862) (@lem3079866)). Qed.
Lemma lem3079868 : True = term150.
Proof. exact (SYM (@lem3079867)). Qed.
Lemma lem3079869 : term150.
Proof. exact (EQ_MP (@lem3079868) (@lem0)). Qed.
Lemma lem3079870 : term158.
Proof. exact (@lem3079859 (@lem3079869)). Qed.
Lemma lem3079872 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079873 : term150 = term156.
Proof. exact (@lem3079872 (NUMERAL 0) term75). Qed.
Lemma lem3079874 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079875 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079876 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079875 h1) (fun h1 : term156 = True => @lem3079874)). Qed.
Lemma lem3079877 : term156 = True.
Proof. exact (EQ_MP (@lem3079876) (@lem3079874)). Qed.
Lemma lem3079878 : term150 = True.
Proof. exact (TRANS (@lem3079873) (@lem3079877)). Qed.
Lemma lem3079879 : True = term150.
Proof. exact (SYM (@lem3079878)). Qed.
Lemma lem3079880 : term150.
Proof. exact (EQ_MP (@lem3079879) (@lem0)). Qed.
Lemma lem3079881 : term153 = term159.
Proof. exact (@lem3079870 (@lem3079880)). Qed.
Lemma lem3079883 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079884 : term104 = term105.
Proof. exact (@lem3079883 term75 term75). Qed.
Lemma lem3079885 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079886 : term107 = term75.
Proof. exact (EQ_MP (@lem3079885) (@lem940073)). Qed.
Lemma lem3079887 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079888 : term105 = term74.
Proof. exact (MK_COMB (@lem3079887) (@lem3079886)). Qed.
Lemma lem3079889 : term104 = term74.
Proof. exact (TRANS (@lem3079884) (@lem3079888)). Qed.
Lemma lem3079891 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3079892 : term161 = term61.
Proof. exact (@lem3079891 term75). Qed.
Lemma lem3079893 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3079894 : term162 = term151.
Proof. exact (MK_COMB (@lem3079893) (@lem3079892)). Qed.
Lemma lem3079895 : term159 = term150.
Proof. exact (MK_COMB (@lem3079894) (@lem3079889)). Qed.
Lemma lem3079897 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079898 : term150 = term156.
Proof. exact (@lem3079897 (NUMERAL 0) term75). Qed.
Lemma lem3079899 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079900 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079901 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079900 h1) (fun h1 : term156 = True => @lem3079899)). Qed.
Lemma lem3079902 : term156 = True.
Proof. exact (EQ_MP (@lem3079901) (@lem3079899)). Qed.
Lemma lem3079903 : term150 = True.
Proof. exact (TRANS (@lem3079898) (@lem3079902)). Qed.
Lemma lem3079904 : term159 = True.
Proof. exact (TRANS (@lem3079895) (@lem3079903)). Qed.
Lemma lem3079905 : term153 = True.
Proof. exact (TRANS (@lem3079881) (@lem3079904)). Qed.
Lemma lem3079906 : term150 = True.
Proof. exact (TRANS (@lem3079858) (@lem3079905)). Qed.
Lemma lem3079907 : term149 = True.
Proof. exact (TRANS (@lem3079849) (@lem3079906)). Qed.
Lemma lem3079908 : True = term149.
Proof. exact (SYM (@lem3079907)). Qed.
Lemma lem3079909 : term149.
Proof. exact (EQ_MP (@lem3079908) (@lem0)). Qed.
Lemma lem3079910 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term782 _32061.
Proof. exact (conj (@lem3079909) (@lem3079770 _32061 _32062 h1)). Qed.
Lemma lem3079912 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3079913 (_32061 : int) : term783 _32061.
Proof. exact (@lem3079912 term74 (term131 _32061)). Qed.
Lemma lem3079914 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term784 _32061.
Proof. exact (@lem3079913 _32061 (@lem3079910 _32061 _32062 h1)). Qed.
Lemma lem3079915 (_32061 : int) : (term785 _32061) = (term131 _32061).
Proof. exact (@lem1982733 (term131 _32061)). Qed.
Lemma lem3079916 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3079917 (_32061 : int) : (term786 _32061) = (term633 _32061).
Proof. exact (MK_COMB (@lem3079916) (@lem3079915 _32061)). Qed.
Lemma lem3079918 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3079919 (_32061 : int) : (term784 _32061) = (term634 _32061).
Proof. exact (MK_COMB (@lem3079917 _32061) (@lem3079918)). Qed.
Lemma lem3079920 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term634 _32061.
Proof. exact (EQ_MP (@lem3079919 _32061) (@lem3079914 _32061 _32062 h1)). Qed.
Lemma lem3079921 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term799 _32061.
Proof. exact (conj (@lem3079920 _32061 _32062 h1) (@lem3079846 _32061 _32062 h1)). Qed.
Lemma lem3079923 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3079924 (_32061 : int) : term800 _32061.
Proof. exact (@lem3079923 (term131 _32061) (term640 _32061)). Qed.
Lemma lem3079925 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term801 _32061.
Proof. exact (@lem3079924 _32061 (@lem3079921 _32061 _32062 h1)). Qed.
Lemma lem3079926 (_32061 : int) : (term802 _32061) = (term803 _32061).
Proof. exact (@lem1982753 (term140 _32061) (real_of_int _32061) term95 term95). Qed.
Lemma lem3079927 (_32061 : int) : (term180 _32061) = (term181 _32061).
Proof. exact (@lem1982713 term95 (real_of_int _32061)). Qed.
Lemma lem3079929 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3079930 : term74 = term121.
Proof. exact (@lem3079929 term75). Qed.
Lemma lem3079932 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3079933 : term95 = term96.
Proof. exact (@lem3079932 term75). Qed.
Lemma lem3079934 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079935 : term182 = term183.
Proof. exact (MK_COMB (@lem3079934) (@lem3079933)). Qed.
Lemma lem3079936 : term184 = term185.
Proof. exact (MK_COMB (@lem3079935) (@lem3079930)). Qed.
Lemma lem3079937 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3079939 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079940 : term150 = term156.
Proof. exact (@lem3079939 (NUMERAL 0) term75). Qed.
Lemma lem3079941 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079942 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079943 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079942 h1) (fun h1 : term156 = True => @lem3079941)). Qed.
Lemma lem3079944 : term156 = True.
Proof. exact (EQ_MP (@lem3079943) (@lem3079941)). Qed.
Lemma lem3079945 : term150 = True.
Proof. exact (TRANS (@lem3079940) (@lem3079944)). Qed.
Lemma lem3079946 : True = term150.
Proof. exact (SYM (@lem3079945)). Qed.
Lemma lem3079947 : term150.
Proof. exact (EQ_MP (@lem3079946) (@lem0)). Qed.
Lemma lem3079948 : term187.
Proof. exact (@lem3079937 (@lem3079947)). Qed.
Lemma lem3079950 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079951 : term150 = term156.
Proof. exact (@lem3079950 (NUMERAL 0) term75). Qed.
Lemma lem3079952 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079953 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079954 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079953 h1) (fun h1 : term156 = True => @lem3079952)). Qed.
Lemma lem3079955 : term156 = True.
Proof. exact (EQ_MP (@lem3079954) (@lem3079952)). Qed.
Lemma lem3079956 : term150 = True.
Proof. exact (TRANS (@lem3079951) (@lem3079955)). Qed.
Lemma lem3079957 : True = term150.
Proof. exact (SYM (@lem3079956)). Qed.
Lemma lem3079958 : term150.
Proof. exact (EQ_MP (@lem3079957) (@lem0)). Qed.
Lemma lem3079959 : term188.
Proof. exact (@lem3079948 (@lem3079958)). Qed.
Lemma lem3079961 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3079962 : term150 = term156.
Proof. exact (@lem3079961 (NUMERAL 0) term75). Qed.
Lemma lem3079963 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3079964 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3079965 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3079964 h1) (fun h1 : term156 = True => @lem3079963)). Qed.
Lemma lem3079966 : term156 = True.
Proof. exact (EQ_MP (@lem3079965) (@lem3079963)). Qed.
Lemma lem3079967 : term150 = True.
Proof. exact (TRANS (@lem3079962) (@lem3079966)). Qed.
Lemma lem3079968 : True = term150.
Proof. exact (SYM (@lem3079967)). Qed.
Lemma lem3079969 : term150.
Proof. exact (EQ_MP (@lem3079968) (@lem0)). Qed.
Lemma lem3079970 : term189.
Proof. exact (@lem3079959 (@lem3079969)). Qed.
Lemma lem3079972 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3079973 : term104 = term105.
Proof. exact (@lem3079972 term75 term75). Qed.
Lemma lem3079974 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079975 : term107 = term75.
Proof. exact (EQ_MP (@lem3079974) (@lem940073)). Qed.
Lemma lem3079976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079977 : term105 = term74.
Proof. exact (MK_COMB (@lem3079976) (@lem3079975)). Qed.
Lemma lem3079978 : term104 = term74.
Proof. exact (TRANS (@lem3079973) (@lem3079977)). Qed.
Lemma lem3079980 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3079981 : term122 = term127.
Proof. exact (@lem3079980 term75 term75). Qed.
Lemma lem3079982 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3079983 : term107 = term75.
Proof. exact (EQ_MP (@lem3079982) (@lem940073)). Qed.
Lemma lem3079984 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3079985 : term105 = term74.
Proof. exact (MK_COMB (@lem3079984) (@lem3079983)). Qed.
Lemma lem3079986 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3079987 : term127 = term95.
Proof. exact (MK_COMB (@lem3079986) (@lem3079985)). Qed.
Lemma lem3079988 : term122 = term95.
Proof. exact (TRANS (@lem3079981) (@lem3079987)). Qed.
Lemma lem3079989 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3079990 : term190 = term182.
Proof. exact (MK_COMB (@lem3079989) (@lem3079988)). Qed.
Lemma lem3079991 : term191 = term184.
Proof. exact (MK_COMB (@lem3079990) (@lem3079978)). Qed.
Lemma lem3079993 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3079994 : term184 = term61.
Proof. exact (@lem3079993 term75). Qed.
Lemma lem3079995 : term191 = term61.
Proof. exact (TRANS (@lem3079991) (@lem3079994)). Qed.
Lemma lem3079996 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3079997 : term193 = term194.
Proof. exact (MK_COMB (@lem3079996) (@lem3079995)). Qed.
Lemma lem3079998 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3079999 : term195 = term161.
Proof. exact (MK_COMB (@lem3079997) (@lem3079998)). Qed.
Lemma lem3080001 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080002 : term161 = term61.
Proof. exact (@lem3080001 term75). Qed.
Lemma lem3080003 : term195 = term61.
Proof. exact (TRANS (@lem3079999) (@lem3080002)). Qed.
Lemma lem3080005 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080006 : term104 = term105.
Proof. exact (@lem3080005 term75 term75). Qed.
Lemma lem3080007 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080008 : term107 = term75.
Proof. exact (EQ_MP (@lem3080007) (@lem940073)). Qed.
Lemma lem3080009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080010 : term105 = term74.
Proof. exact (MK_COMB (@lem3080009) (@lem3080008)). Qed.
Lemma lem3080011 : term104 = term74.
Proof. exact (TRANS (@lem3080006) (@lem3080010)). Qed.
Lemma lem3080012 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3080013 : term196 = term161.
Proof. exact (MK_COMB (@lem3080012) (@lem3080011)). Qed.
Lemma lem3080015 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080016 : term161 = term61.
Proof. exact (@lem3080015 term75). Qed.
Lemma lem3080017 : term196 = term61.
Proof. exact (TRANS (@lem3080013) (@lem3080016)). Qed.
Lemma lem3080018 : term61 = term196.
Proof. exact (SYM (@lem3080017)). Qed.
Lemma lem3080019 : term195 = term196.
Proof. exact (TRANS (@lem3080003) (@lem3080018)). Qed.
Lemma lem3080020 : term185 = term92.
Proof. exact (@lem3079970 (@lem3080019)). Qed.
Lemma lem3080021 : term184 = term92.
Proof. exact (TRANS (@lem3079936) (@lem3080020)). Qed.
Lemma lem3080023 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3080024 : term92 = term61.
Proof. exact (@lem3080023 term61). Qed.
Lemma lem3080025 : term184 = term61.
Proof. exact (TRANS (@lem3080021) (@lem3080024)). Qed.
Lemma lem3080026 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3080027 : term197 = term194.
Proof. exact (MK_COMB (@lem3080026) (@lem3080025)). Qed.
Lemma lem3080028 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3080029 (_32061 : int) : (term181 _32061) = (term198 _32061).
Proof. exact (MK_COMB (@lem3080027) (@lem3080028 _32061)). Qed.
Lemma lem3080030 (_32061 : int) : (term180 _32061) = (term198 _32061).
Proof. exact (TRANS (@lem3079927 _32061) (@lem3080029 _32061)). Qed.
Lemma lem3080031 (_32061 : int) : (term198 _32061) = term61.
Proof. exact (@lem1982719 (real_of_int _32061)). Qed.
Lemma lem3080032 (_32061 : int) : (term180 _32061) = term61.
Proof. exact (TRANS (@lem3080030 _32061) (@lem3080031 _32061)). Qed.
Lemma lem3080033 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080034 (_32061 : int) : (term199 _32061) = term200.
Proof. exact (MK_COMB (@lem3080033) (@lem3080032 _32061)). Qed.
Lemma lem3080036 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3080037 : term95 = term96.
Proof. exact (@lem3080036 term75). Qed.
Lemma lem3080039 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3080040 : term95 = term96.
Proof. exact (@lem3080039 term75). Qed.
Lemma lem3080041 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080042 : term182 = term183.
Proof. exact (MK_COMB (@lem3080041) (@lem3080040)). Qed.
Lemma lem3080043 : term804 = term805.
Proof. exact (MK_COMB (@lem3080042) (@lem3080037)). Qed.
Lemma lem3080044 : term806.
Proof. exact (@lem1981473 term95 term74 term95 term74 term807 term74). Qed.
Lemma lem3080046 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080047 : term150 = term156.
Proof. exact (@lem3080046 (NUMERAL 0) term75). Qed.
Lemma lem3080048 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080049 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080050 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080049 h1) (fun h1 : term156 = True => @lem3080048)). Qed.
Lemma lem3080051 : term156 = True.
Proof. exact (EQ_MP (@lem3080050) (@lem3080048)). Qed.
Lemma lem3080052 : term150 = True.
Proof. exact (TRANS (@lem3080047) (@lem3080051)). Qed.
Lemma lem3080053 : True = term150.
Proof. exact (SYM (@lem3080052)). Qed.
Lemma lem3080054 : term150.
Proof. exact (EQ_MP (@lem3080053) (@lem0)). Qed.
Lemma lem3080055 : term808.
Proof. exact (@lem3080044 (@lem3080054)). Qed.
Lemma lem3080057 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080058 : term150 = term156.
Proof. exact (@lem3080057 (NUMERAL 0) term75). Qed.
Lemma lem3080059 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080060 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080061 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080060 h1) (fun h1 : term156 = True => @lem3080059)). Qed.
Lemma lem3080062 : term156 = True.
Proof. exact (EQ_MP (@lem3080061) (@lem3080059)). Qed.
Lemma lem3080063 : term150 = True.
Proof. exact (TRANS (@lem3080058) (@lem3080062)). Qed.
Lemma lem3080064 : True = term150.
Proof. exact (SYM (@lem3080063)). Qed.
Lemma lem3080065 : term150.
Proof. exact (EQ_MP (@lem3080064) (@lem0)). Qed.
Lemma lem3080066 : term809.
Proof. exact (@lem3080055 (@lem3080065)). Qed.
Lemma lem3080068 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080069 : term150 = term156.
Proof. exact (@lem3080068 (NUMERAL 0) term75). Qed.
Lemma lem3080070 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080071 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080072 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080071 h1) (fun h1 : term156 = True => @lem3080070)). Qed.
Lemma lem3080073 : term156 = True.
Proof. exact (EQ_MP (@lem3080072) (@lem3080070)). Qed.
Lemma lem3080074 : term150 = True.
Proof. exact (TRANS (@lem3080069) (@lem3080073)). Qed.
Lemma lem3080075 : True = term150.
Proof. exact (SYM (@lem3080074)). Qed.
Lemma lem3080076 : term150.
Proof. exact (EQ_MP (@lem3080075) (@lem0)). Qed.
Lemma lem3080077 : term810.
Proof. exact (@lem3080066 (@lem3080076)). Qed.
Lemma lem3080079 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080080 : term122 = term127.
Proof. exact (@lem3080079 term75 term75). Qed.
Lemma lem3080081 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080082 : term107 = term75.
Proof. exact (EQ_MP (@lem3080081) (@lem940073)). Qed.
Lemma lem3080083 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080084 : term105 = term74.
Proof. exact (MK_COMB (@lem3080083) (@lem3080082)). Qed.
Lemma lem3080085 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080086 : term127 = term95.
Proof. exact (MK_COMB (@lem3080085) (@lem3080084)). Qed.
Lemma lem3080087 : term122 = term95.
Proof. exact (TRANS (@lem3080080) (@lem3080086)). Qed.
Lemma lem3080089 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080090 : term122 = term127.
Proof. exact (@lem3080089 term75 term75). Qed.
Lemma lem3080091 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080092 : term107 = term75.
Proof. exact (EQ_MP (@lem3080091) (@lem940073)). Qed.
Lemma lem3080093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080094 : term105 = term74.
Proof. exact (MK_COMB (@lem3080093) (@lem3080092)). Qed.
Lemma lem3080095 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080096 : term127 = term95.
Proof. exact (MK_COMB (@lem3080095) (@lem3080094)). Qed.
Lemma lem3080097 : term122 = term95.
Proof. exact (TRANS (@lem3080090) (@lem3080096)). Qed.
Lemma lem3080098 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080099 : term190 = term182.
Proof. exact (MK_COMB (@lem3080098) (@lem3080097)). Qed.
Lemma lem3080100 : term811 = term804.
Proof. exact (MK_COMB (@lem3080099) (@lem3080087)). Qed.
Lemma lem3080101 : term804 = term812.
Proof. exact (@lem1367763 term75 term75). Qed.
Lemma lem3080102 : term813 = term814.
Proof. exact (@lem706885). Qed.
Lemma lem3080103 : (term813 = term814) = (term815 = term816).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term814). Qed.
Lemma lem3080104 : term815 = term816.
Proof. exact (EQ_MP (@lem3080103) (@lem3080102)). Qed.
Lemma lem3080105 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080106 : term817 = term818.
Proof. exact (MK_COMB (@lem3080105) (@lem3080104)). Qed.
Lemma lem3080107 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080108 : term812 = term807.
Proof. exact (MK_COMB (@lem3080107) (@lem3080106)). Qed.
Lemma lem3080109 : term804 = term807.
Proof. exact (TRANS (@lem3080101) (@lem3080108)). Qed.
Lemma lem3080110 : term811 = term807.
Proof. exact (TRANS (@lem3080100) (@lem3080109)). Qed.
Lemma lem3080111 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3080112 : term819 = term820.
Proof. exact (MK_COMB (@lem3080111) (@lem3080110)). Qed.
Lemma lem3080113 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3080114 : term821 = term822.
Proof. exact (MK_COMB (@lem3080112) (@lem3080113)). Qed.
Lemma lem3080116 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080117 : term822 = term823.
Proof. exact (@lem3080116 term816 term75). Qed.
Lemma lem3080118 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3080119 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3080120 : term825 = term816.
Proof. exact (EQ_MP (@lem3080119) (@lem3080118)). Qed.
Lemma lem3080121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080122 : term826 = term818.
Proof. exact (MK_COMB (@lem3080121) (@lem3080120)). Qed.
Lemma lem3080123 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080124 : term823 = term807.
Proof. exact (MK_COMB (@lem3080123) (@lem3080122)). Qed.
Lemma lem3080125 : term822 = term807.
Proof. exact (TRANS (@lem3080117) (@lem3080124)). Qed.
Lemma lem3080126 : term821 = term807.
Proof. exact (TRANS (@lem3080114) (@lem3080125)). Qed.
Lemma lem3080128 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080129 : term104 = term105.
Proof. exact (@lem3080128 term75 term75). Qed.
Lemma lem3080130 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080131 : term107 = term75.
Proof. exact (EQ_MP (@lem3080130) (@lem940073)). Qed.
Lemma lem3080132 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080133 : term105 = term74.
Proof. exact (MK_COMB (@lem3080132) (@lem3080131)). Qed.
Lemma lem3080134 : term104 = term74.
Proof. exact (TRANS (@lem3080129) (@lem3080133)). Qed.
Lemma lem3080135 : term820 = term820.
Proof. exact (eq_refl term820). Qed.
Lemma lem3080136 : term827 = term822.
Proof. exact (MK_COMB (@lem3080135) (@lem3080134)). Qed.
Lemma lem3080138 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080139 : term822 = term823.
Proof. exact (@lem3080138 term816 term75). Qed.
Lemma lem3080140 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3080141 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3080142 : term825 = term816.
Proof. exact (EQ_MP (@lem3080141) (@lem3080140)). Qed.
Lemma lem3080143 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080144 : term826 = term818.
Proof. exact (MK_COMB (@lem3080143) (@lem3080142)). Qed.
Lemma lem3080145 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080146 : term823 = term807.
Proof. exact (MK_COMB (@lem3080145) (@lem3080144)). Qed.
Lemma lem3080147 : term822 = term807.
Proof. exact (TRANS (@lem3080139) (@lem3080146)). Qed.
Lemma lem3080148 : term827 = term807.
Proof. exact (TRANS (@lem3080136) (@lem3080147)). Qed.
Lemma lem3080149 : term807 = term827.
Proof. exact (SYM (@lem3080148)). Qed.
Lemma lem3080150 : term821 = term827.
Proof. exact (TRANS (@lem3080126) (@lem3080149)). Qed.
Lemma lem3080151 : term805 = term828.
Proof. exact (@lem3080077 (@lem3080150)). Qed.
Lemma lem3080152 : term804 = term828.
Proof. exact (TRANS (@lem3080043) (@lem3080151)). Qed.
Lemma lem3080154 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3080155 : term828 = term807.
Proof. exact (@lem3080154 term807). Qed.
Lemma lem3080156 : term804 = term807.
Proof. exact (TRANS (@lem3080152) (@lem3080155)). Qed.
Lemma lem3080157 (_32061 : int) : (term803 _32061) = term829.
Proof. exact (MK_COMB (@lem3080034 _32061) (@lem3080156)). Qed.
Lemma lem3080158 (_32061 : int) : (term802 _32061) = term829.
Proof. exact (TRANS (@lem3079926 _32061) (@lem3080157 _32061)). Qed.
Lemma lem3080159 : term829 = term807.
Proof. exact (@lem1982721 term807). Qed.
Lemma lem3080160 (_32061 : int) : (term802 _32061) = term807.
Proof. exact (TRANS (@lem3080158 _32061) (@lem3080159)). Qed.
Lemma lem3080161 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3080162 (_32061 : int) : (term830 _32061) = term831.
Proof. exact (MK_COMB (@lem3080161) (@lem3080160 _32061)). Qed.
Lemma lem3080163 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3080164 (_32061 : int) : (term801 _32061) = term832.
Proof. exact (MK_COMB (@lem3080162 _32061) (@lem3080163)). Qed.
Lemma lem3080165 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : term832.
Proof. exact (EQ_MP (@lem3080164 _32061) (@lem3079925 _32061 _32062 h1)). Qed.
Lemma lem3080167 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3080168 : term832 = term833.
Proof. exact (@lem3080167 term61 term807). Qed.
Lemma lem3080170 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3080171 : term807 = term828.
Proof. exact (@lem3080170 term816). Qed.
Lemma lem3080173 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080174 : term61 = term92.
Proof. exact (@lem3080173 (NUMERAL 0)). Qed.
Lemma lem3080175 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3080176 : term63 = term210.
Proof. exact (MK_COMB (@lem3080175) (@lem3080174)). Qed.
Lemma lem3080177 : term833 = term834.
Proof. exact (MK_COMB (@lem3080176) (@lem3080171)). Qed.
Lemma lem3080178 : term835.
Proof. exact (@lem1980026 term61 term74 term807 term74). Qed.
Lemma lem3080180 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080181 : term150 = term156.
Proof. exact (@lem3080180 (NUMERAL 0) term75). Qed.
Lemma lem3080182 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080183 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080184 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080183 h1) (fun h1 : term156 = True => @lem3080182)). Qed.
Lemma lem3080185 : term156 = True.
Proof. exact (EQ_MP (@lem3080184) (@lem3080182)). Qed.
Lemma lem3080186 : term150 = True.
Proof. exact (TRANS (@lem3080181) (@lem3080185)). Qed.
Lemma lem3080187 : True = term150.
Proof. exact (SYM (@lem3080186)). Qed.
Lemma lem3080188 : term150.
Proof. exact (EQ_MP (@lem3080187) (@lem0)). Qed.
Lemma lem3080189 : term836.
Proof. exact (@lem3080178 (@lem3080188)). Qed.
Lemma lem3080191 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080192 : term150 = term156.
Proof. exact (@lem3080191 (NUMERAL 0) term75). Qed.
Lemma lem3080193 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080194 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080195 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080194 h1) (fun h1 : term156 = True => @lem3080193)). Qed.
Lemma lem3080196 : term156 = True.
Proof. exact (EQ_MP (@lem3080195) (@lem3080193)). Qed.
Lemma lem3080197 : term150 = True.
Proof. exact (TRANS (@lem3080192) (@lem3080196)). Qed.
Lemma lem3080198 : True = term150.
Proof. exact (SYM (@lem3080197)). Qed.
Lemma lem3080199 : term150.
Proof. exact (EQ_MP (@lem3080198) (@lem0)). Qed.
Lemma lem3080200 : term834 = term837.
Proof. exact (@lem3080189 (@lem3080199)). Qed.
Lemma lem3080202 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080203 : term822 = term823.
Proof. exact (@lem3080202 term816 term75). Qed.
Lemma lem3080204 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3080205 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3080206 : term825 = term816.
Proof. exact (EQ_MP (@lem3080205) (@lem3080204)). Qed.
Lemma lem3080207 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080208 : term826 = term818.
Proof. exact (MK_COMB (@lem3080207) (@lem3080206)). Qed.
Lemma lem3080209 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080210 : term823 = term807.
Proof. exact (MK_COMB (@lem3080209) (@lem3080208)). Qed.
Lemma lem3080211 : term822 = term807.
Proof. exact (TRANS (@lem3080203) (@lem3080210)). Qed.
Lemma lem3080213 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080214 : term161 = term61.
Proof. exact (@lem3080213 term75). Qed.
Lemma lem3080215 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3080216 : term215 = term63.
Proof. exact (MK_COMB (@lem3080215) (@lem3080214)). Qed.
Lemma lem3080217 : term837 = term833.
Proof. exact (MK_COMB (@lem3080216) (@lem3080211)). Qed.
Lemma lem3080219 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3080220 : term833 = term838.
Proof. exact (@lem3080219 (NUMERAL 0) term816). Qed.
Lemma lem3080221 : term839 = term814.
Proof. exact (@lem912803). Qed.
Lemma lem3080222 (h1 : term839 = term814) : (term816 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term814 h1). Qed.
Lemma lem3080223 : (term839 = term814) = ((term816 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term839 = term814 => @lem3080222 h1) (fun h1 : (term816 = (NUMERAL 0)) = False => @lem3080221)). Qed.
Lemma lem3080224 : (term816 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3080223) (@lem3080221)). Qed.
Lemma lem3080225 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3080226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3080227 : term219 = (and True).
Proof. exact (MK_COMB (@lem3080226) (@lem3080225)). Qed.
Lemma lem3080228 : term838 = (True /\ False).
Proof. exact (MK_COMB (@lem3080227) (@lem3080224)). Qed.
Lemma lem3080230 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3080231 : term838 = False.
Proof. exact (TRANS (@lem3080228) (@lem3080230)). Qed.
Lemma lem3080232 : term833 = False.
Proof. exact (TRANS (@lem3080220) (@lem3080231)). Qed.
Lemma lem3080233 : term837 = False.
Proof. exact (TRANS (@lem3080217) (@lem3080232)). Qed.
Lemma lem3080234 : term834 = False.
Proof. exact (TRANS (@lem3080200) (@lem3080233)). Qed.
Lemma lem3080235 : term833 = False.
Proof. exact (TRANS (@lem3080177) (@lem3080234)). Qed.
Lemma lem3080236 : term832 = False.
Proof. exact (TRANS (@lem3080168) (@lem3080235)). Qed.
Lemma lem3080237 (_32061 : int) (_32062 : int) (h1 : term840 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3080236) (@lem3080165 _32061 _32062 h1)). Qed.
Lemma lem3080238 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term841 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3080239 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term765 _32061 _32062.
Proof. exact (proj2 (@lem3080238 _32061 _32062 h1)). Qed.
Lemma lem3080241 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term734 _32061 _32062.
Proof. exact (proj2 (@lem3080239 _32061 _32062 h1)). Qed.
Lemma lem3080242 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term115 _32062.
Proof. exact (proj1 (@lem3080239 _32061 _32062 h1)). Qed.
Lemma lem3080243 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term703 _32061 _32062.
Proof. exact (proj2 (@lem3080241 _32061 _32062 h1)). Qed.
Lemma lem3080247 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term634 _32062.
Proof. exact (proj2 (@lem3080243 _32061 _32062 h1)). Qed.
Lemma lem3080250 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3080251 : term149 = term150.
Proof. exact (@lem3080250 term61 term74). Qed.
Lemma lem3080253 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080254 : term74 = term121.
Proof. exact (@lem3080253 term75). Qed.
Lemma lem3080256 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080257 : term61 = term92.
Proof. exact (@lem3080256 (NUMERAL 0)). Qed.
Lemma lem3080258 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080259 : term151 = term152.
Proof. exact (MK_COMB (@lem3080258) (@lem3080257)). Qed.
Lemma lem3080260 : term150 = term153.
Proof. exact (MK_COMB (@lem3080259) (@lem3080254)). Qed.
Lemma lem3080261 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3080263 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080264 : term150 = term156.
Proof. exact (@lem3080263 (NUMERAL 0) term75). Qed.
Lemma lem3080265 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080266 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080267 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080266 h1) (fun h1 : term156 = True => @lem3080265)). Qed.
Lemma lem3080268 : term156 = True.
Proof. exact (EQ_MP (@lem3080267) (@lem3080265)). Qed.
Lemma lem3080269 : term150 = True.
Proof. exact (TRANS (@lem3080264) (@lem3080268)). Qed.
Lemma lem3080270 : True = term150.
Proof. exact (SYM (@lem3080269)). Qed.
Lemma lem3080271 : term150.
Proof. exact (EQ_MP (@lem3080270) (@lem0)). Qed.
Lemma lem3080272 : term158.
Proof. exact (@lem3080261 (@lem3080271)). Qed.
Lemma lem3080274 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080275 : term150 = term156.
Proof. exact (@lem3080274 (NUMERAL 0) term75). Qed.
Lemma lem3080276 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080277 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080278 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080277 h1) (fun h1 : term156 = True => @lem3080276)). Qed.
Lemma lem3080279 : term156 = True.
Proof. exact (EQ_MP (@lem3080278) (@lem3080276)). Qed.
Lemma lem3080280 : term150 = True.
Proof. exact (TRANS (@lem3080275) (@lem3080279)). Qed.
Lemma lem3080281 : True = term150.
Proof. exact (SYM (@lem3080280)). Qed.
Lemma lem3080282 : term150.
Proof. exact (EQ_MP (@lem3080281) (@lem0)). Qed.
Lemma lem3080283 : term153 = term159.
Proof. exact (@lem3080272 (@lem3080282)). Qed.
Lemma lem3080285 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080286 : term104 = term105.
Proof. exact (@lem3080285 term75 term75). Qed.
Lemma lem3080287 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080288 : term107 = term75.
Proof. exact (EQ_MP (@lem3080287) (@lem940073)). Qed.
Lemma lem3080289 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080290 : term105 = term74.
Proof. exact (MK_COMB (@lem3080289) (@lem3080288)). Qed.
Lemma lem3080291 : term104 = term74.
Proof. exact (TRANS (@lem3080286) (@lem3080290)). Qed.
Lemma lem3080293 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080294 : term161 = term61.
Proof. exact (@lem3080293 term75). Qed.
Lemma lem3080295 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080296 : term162 = term151.
Proof. exact (MK_COMB (@lem3080295) (@lem3080294)). Qed.
Lemma lem3080297 : term159 = term150.
Proof. exact (MK_COMB (@lem3080296) (@lem3080291)). Qed.
Lemma lem3080299 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080300 : term150 = term156.
Proof. exact (@lem3080299 (NUMERAL 0) term75). Qed.
Lemma lem3080301 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080302 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080303 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080302 h1) (fun h1 : term156 = True => @lem3080301)). Qed.
Lemma lem3080304 : term156 = True.
Proof. exact (EQ_MP (@lem3080303) (@lem3080301)). Qed.
Lemma lem3080305 : term150 = True.
Proof. exact (TRANS (@lem3080300) (@lem3080304)). Qed.
Lemma lem3080306 : term159 = True.
Proof. exact (TRANS (@lem3080297) (@lem3080305)). Qed.
Lemma lem3080307 : term153 = True.
Proof. exact (TRANS (@lem3080283) (@lem3080306)). Qed.
Lemma lem3080308 : term150 = True.
Proof. exact (TRANS (@lem3080260) (@lem3080307)). Qed.
Lemma lem3080309 : term149 = True.
Proof. exact (TRANS (@lem3080251) (@lem3080308)). Qed.
Lemma lem3080310 : True = term149.
Proof. exact (SYM (@lem3080309)). Qed.
Lemma lem3080311 : term149.
Proof. exact (EQ_MP (@lem3080310) (@lem0)). Qed.
Lemma lem3080312 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term777 _32062.
Proof. exact (conj (@lem3080311) (@lem3080242 _32061 _32062 h1)). Qed.
Lemma lem3080314 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3080315 (_32062 : int) : term778 _32062.
Proof. exact (@lem3080314 term74 (real_of_int _32062)). Qed.
Lemma lem3080316 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term779 _32062.
Proof. exact (@lem3080315 _32062 (@lem3080312 _32061 _32062 h1)). Qed.
Lemma lem3080317 (_32062 : int) : (term780 _32062) = (real_of_int _32062).
Proof. exact (@lem1982733 (real_of_int _32062)). Qed.
Lemma lem3080318 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3080319 (_32062 : int) : (term781 _32062) = (term114 _32062).
Proof. exact (MK_COMB (@lem3080318) (@lem3080317 _32062)). Qed.
Lemma lem3080320 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3080321 (_32062 : int) : (term779 _32062) = (term115 _32062).
Proof. exact (MK_COMB (@lem3080319 _32062) (@lem3080320)). Qed.
Lemma lem3080322 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term115 _32062.
Proof. exact (EQ_MP (@lem3080321 _32062) (@lem3080316 _32061 _32062 h1)). Qed.
Lemma lem3080324 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3080325 : term149 = term150.
Proof. exact (@lem3080324 term61 term74). Qed.
Lemma lem3080327 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080328 : term74 = term121.
Proof. exact (@lem3080327 term75). Qed.
Lemma lem3080330 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080331 : term61 = term92.
Proof. exact (@lem3080330 (NUMERAL 0)). Qed.
Lemma lem3080332 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080333 : term151 = term152.
Proof. exact (MK_COMB (@lem3080332) (@lem3080331)). Qed.
Lemma lem3080334 : term150 = term153.
Proof. exact (MK_COMB (@lem3080333) (@lem3080328)). Qed.
Lemma lem3080335 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3080337 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080338 : term150 = term156.
Proof. exact (@lem3080337 (NUMERAL 0) term75). Qed.
Lemma lem3080339 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080340 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080341 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080340 h1) (fun h1 : term156 = True => @lem3080339)). Qed.
Lemma lem3080342 : term156 = True.
Proof. exact (EQ_MP (@lem3080341) (@lem3080339)). Qed.
Lemma lem3080343 : term150 = True.
Proof. exact (TRANS (@lem3080338) (@lem3080342)). Qed.
Lemma lem3080344 : True = term150.
Proof. exact (SYM (@lem3080343)). Qed.
Lemma lem3080345 : term150.
Proof. exact (EQ_MP (@lem3080344) (@lem0)). Qed.
Lemma lem3080346 : term158.
Proof. exact (@lem3080335 (@lem3080345)). Qed.
Lemma lem3080348 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080349 : term150 = term156.
Proof. exact (@lem3080348 (NUMERAL 0) term75). Qed.
Lemma lem3080350 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080351 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080352 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080351 h1) (fun h1 : term156 = True => @lem3080350)). Qed.
Lemma lem3080353 : term156 = True.
Proof. exact (EQ_MP (@lem3080352) (@lem3080350)). Qed.
Lemma lem3080354 : term150 = True.
Proof. exact (TRANS (@lem3080349) (@lem3080353)). Qed.
Lemma lem3080355 : True = term150.
Proof. exact (SYM (@lem3080354)). Qed.
Lemma lem3080356 : term150.
Proof. exact (EQ_MP (@lem3080355) (@lem0)). Qed.
Lemma lem3080357 : term153 = term159.
Proof. exact (@lem3080346 (@lem3080356)). Qed.
Lemma lem3080359 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080360 : term104 = term105.
Proof. exact (@lem3080359 term75 term75). Qed.
Lemma lem3080361 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080362 : term107 = term75.
Proof. exact (EQ_MP (@lem3080361) (@lem940073)). Qed.
Lemma lem3080363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080364 : term105 = term74.
Proof. exact (MK_COMB (@lem3080363) (@lem3080362)). Qed.
Lemma lem3080365 : term104 = term74.
Proof. exact (TRANS (@lem3080360) (@lem3080364)). Qed.
Lemma lem3080367 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080368 : term161 = term61.
Proof. exact (@lem3080367 term75). Qed.
Lemma lem3080369 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080370 : term162 = term151.
Proof. exact (MK_COMB (@lem3080369) (@lem3080368)). Qed.
Lemma lem3080371 : term159 = term150.
Proof. exact (MK_COMB (@lem3080370) (@lem3080365)). Qed.
Lemma lem3080373 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080374 : term150 = term156.
Proof. exact (@lem3080373 (NUMERAL 0) term75). Qed.
Lemma lem3080375 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080376 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080377 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080376 h1) (fun h1 : term156 = True => @lem3080375)). Qed.
Lemma lem3080378 : term156 = True.
Proof. exact (EQ_MP (@lem3080377) (@lem3080375)). Qed.
Lemma lem3080379 : term150 = True.
Proof. exact (TRANS (@lem3080374) (@lem3080378)). Qed.
Lemma lem3080380 : term159 = True.
Proof. exact (TRANS (@lem3080371) (@lem3080379)). Qed.
Lemma lem3080381 : term153 = True.
Proof. exact (TRANS (@lem3080357) (@lem3080380)). Qed.
Lemma lem3080382 : term150 = True.
Proof. exact (TRANS (@lem3080334) (@lem3080381)). Qed.
Lemma lem3080383 : term149 = True.
Proof. exact (TRANS (@lem3080325) (@lem3080382)). Qed.
Lemma lem3080384 : True = term149.
Proof. exact (SYM (@lem3080383)). Qed.
Lemma lem3080385 : term149.
Proof. exact (EQ_MP (@lem3080384) (@lem0)). Qed.
Lemma lem3080386 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term782 _32062.
Proof. exact (conj (@lem3080385) (@lem3080247 _32061 _32062 h1)). Qed.
Lemma lem3080388 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3080389 (_32062 : int) : term783 _32062.
Proof. exact (@lem3080388 term74 (term131 _32062)). Qed.
Lemma lem3080390 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term784 _32062.
Proof. exact (@lem3080389 _32062 (@lem3080386 _32061 _32062 h1)). Qed.
Lemma lem3080391 (_32062 : int) : (term785 _32062) = (term131 _32062).
Proof. exact (@lem1982733 (term131 _32062)). Qed.
Lemma lem3080392 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3080393 (_32062 : int) : (term786 _32062) = (term633 _32062).
Proof. exact (MK_COMB (@lem3080392) (@lem3080391 _32062)). Qed.
Lemma lem3080394 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3080395 (_32062 : int) : (term784 _32062) = (term634 _32062).
Proof. exact (MK_COMB (@lem3080393 _32062) (@lem3080394)). Qed.
Lemma lem3080396 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term634 _32062.
Proof. exact (EQ_MP (@lem3080395 _32062) (@lem3080390 _32061 _32062 h1)). Qed.
Lemma lem3080397 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term787 _32062.
Proof. exact (conj (@lem3080396 _32061 _32062 h1) (@lem3080322 _32061 _32062 h1)). Qed.
Lemma lem3080399 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3080400 (_32062 : int) : term788 _32062.
Proof. exact (@lem3080399 (term131 _32062) (real_of_int _32062)). Qed.
Lemma lem3080401 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term789 _32062.
Proof. exact (@lem3080400 _32062 (@lem3080397 _32061 _32062 h1)). Qed.
Lemma lem3080402 (_32062 : int) : (term790 _32062) = (term791 _32062).
Proof. exact (@lem1982759 (term140 _32062) (real_of_int _32062) term95). Qed.
Lemma lem3080403 (_32062 : int) : (term180 _32062) = (term181 _32062).
Proof. exact (@lem1982713 term95 (real_of_int _32062)). Qed.
Lemma lem3080405 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080406 : term74 = term121.
Proof. exact (@lem3080405 term75). Qed.
Lemma lem3080408 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3080409 : term95 = term96.
Proof. exact (@lem3080408 term75). Qed.
Lemma lem3080410 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080411 : term182 = term183.
Proof. exact (MK_COMB (@lem3080410) (@lem3080409)). Qed.
Lemma lem3080412 : term184 = term185.
Proof. exact (MK_COMB (@lem3080411) (@lem3080406)). Qed.
Lemma lem3080413 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3080415 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080416 : term150 = term156.
Proof. exact (@lem3080415 (NUMERAL 0) term75). Qed.
Lemma lem3080417 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080418 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080419 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080418 h1) (fun h1 : term156 = True => @lem3080417)). Qed.
Lemma lem3080420 : term156 = True.
Proof. exact (EQ_MP (@lem3080419) (@lem3080417)). Qed.
Lemma lem3080421 : term150 = True.
Proof. exact (TRANS (@lem3080416) (@lem3080420)). Qed.
Lemma lem3080422 : True = term150.
Proof. exact (SYM (@lem3080421)). Qed.
Lemma lem3080423 : term150.
Proof. exact (EQ_MP (@lem3080422) (@lem0)). Qed.
Lemma lem3080424 : term187.
Proof. exact (@lem3080413 (@lem3080423)). Qed.
Lemma lem3080426 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080427 : term150 = term156.
Proof. exact (@lem3080426 (NUMERAL 0) term75). Qed.
Lemma lem3080428 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080429 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080430 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080429 h1) (fun h1 : term156 = True => @lem3080428)). Qed.
Lemma lem3080431 : term156 = True.
Proof. exact (EQ_MP (@lem3080430) (@lem3080428)). Qed.
Lemma lem3080432 : term150 = True.
Proof. exact (TRANS (@lem3080427) (@lem3080431)). Qed.
Lemma lem3080433 : True = term150.
Proof. exact (SYM (@lem3080432)). Qed.
Lemma lem3080434 : term150.
Proof. exact (EQ_MP (@lem3080433) (@lem0)). Qed.
Lemma lem3080435 : term188.
Proof. exact (@lem3080424 (@lem3080434)). Qed.
Lemma lem3080437 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080438 : term150 = term156.
Proof. exact (@lem3080437 (NUMERAL 0) term75). Qed.
Lemma lem3080439 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080440 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080441 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080440 h1) (fun h1 : term156 = True => @lem3080439)). Qed.
Lemma lem3080442 : term156 = True.
Proof. exact (EQ_MP (@lem3080441) (@lem3080439)). Qed.
Lemma lem3080443 : term150 = True.
Proof. exact (TRANS (@lem3080438) (@lem3080442)). Qed.
Lemma lem3080444 : True = term150.
Proof. exact (SYM (@lem3080443)). Qed.
Lemma lem3080445 : term150.
Proof. exact (EQ_MP (@lem3080444) (@lem0)). Qed.
Lemma lem3080446 : term189.
Proof. exact (@lem3080435 (@lem3080445)). Qed.
Lemma lem3080448 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080449 : term104 = term105.
Proof. exact (@lem3080448 term75 term75). Qed.
Lemma lem3080450 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080451 : term107 = term75.
Proof. exact (EQ_MP (@lem3080450) (@lem940073)). Qed.
Lemma lem3080452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080453 : term105 = term74.
Proof. exact (MK_COMB (@lem3080452) (@lem3080451)). Qed.
Lemma lem3080454 : term104 = term74.
Proof. exact (TRANS (@lem3080449) (@lem3080453)). Qed.
Lemma lem3080456 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080457 : term122 = term127.
Proof. exact (@lem3080456 term75 term75). Qed.
Lemma lem3080458 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080459 : term107 = term75.
Proof. exact (EQ_MP (@lem3080458) (@lem940073)). Qed.
Lemma lem3080460 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080461 : term105 = term74.
Proof. exact (MK_COMB (@lem3080460) (@lem3080459)). Qed.
Lemma lem3080462 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080463 : term127 = term95.
Proof. exact (MK_COMB (@lem3080462) (@lem3080461)). Qed.
Lemma lem3080464 : term122 = term95.
Proof. exact (TRANS (@lem3080457) (@lem3080463)). Qed.
Lemma lem3080465 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080466 : term190 = term182.
Proof. exact (MK_COMB (@lem3080465) (@lem3080464)). Qed.
Lemma lem3080467 : term191 = term184.
Proof. exact (MK_COMB (@lem3080466) (@lem3080454)). Qed.
Lemma lem3080469 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3080470 : term184 = term61.
Proof. exact (@lem3080469 term75). Qed.
Lemma lem3080471 : term191 = term61.
Proof. exact (TRANS (@lem3080467) (@lem3080470)). Qed.
Lemma lem3080472 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3080473 : term193 = term194.
Proof. exact (MK_COMB (@lem3080472) (@lem3080471)). Qed.
Lemma lem3080474 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3080475 : term195 = term161.
Proof. exact (MK_COMB (@lem3080473) (@lem3080474)). Qed.
Lemma lem3080477 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080478 : term161 = term61.
Proof. exact (@lem3080477 term75). Qed.
Lemma lem3080479 : term195 = term61.
Proof. exact (TRANS (@lem3080475) (@lem3080478)). Qed.
Lemma lem3080481 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080482 : term104 = term105.
Proof. exact (@lem3080481 term75 term75). Qed.
Lemma lem3080483 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080484 : term107 = term75.
Proof. exact (EQ_MP (@lem3080483) (@lem940073)). Qed.
Lemma lem3080485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080486 : term105 = term74.
Proof. exact (MK_COMB (@lem3080485) (@lem3080484)). Qed.
Lemma lem3080487 : term104 = term74.
Proof. exact (TRANS (@lem3080482) (@lem3080486)). Qed.
Lemma lem3080488 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3080489 : term196 = term161.
Proof. exact (MK_COMB (@lem3080488) (@lem3080487)). Qed.
Lemma lem3080491 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080492 : term161 = term61.
Proof. exact (@lem3080491 term75). Qed.
Lemma lem3080493 : term196 = term61.
Proof. exact (TRANS (@lem3080489) (@lem3080492)). Qed.
Lemma lem3080494 : term61 = term196.
Proof. exact (SYM (@lem3080493)). Qed.
Lemma lem3080495 : term195 = term196.
Proof. exact (TRANS (@lem3080479) (@lem3080494)). Qed.
Lemma lem3080496 : term185 = term92.
Proof. exact (@lem3080446 (@lem3080495)). Qed.
Lemma lem3080497 : term184 = term92.
Proof. exact (TRANS (@lem3080412) (@lem3080496)). Qed.
Lemma lem3080499 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3080500 : term92 = term61.
Proof. exact (@lem3080499 term61). Qed.
Lemma lem3080501 : term184 = term61.
Proof. exact (TRANS (@lem3080497) (@lem3080500)). Qed.
Lemma lem3080502 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3080503 : term197 = term194.
Proof. exact (MK_COMB (@lem3080502) (@lem3080501)). Qed.
Lemma lem3080504 (_32062 : int) : (real_of_int _32062) = (real_of_int _32062).
Proof. exact (eq_refl (real_of_int _32062)). Qed.
Lemma lem3080505 (_32062 : int) : (term181 _32062) = (term198 _32062).
Proof. exact (MK_COMB (@lem3080503) (@lem3080504 _32062)). Qed.
Lemma lem3080506 (_32062 : int) : (term180 _32062) = (term198 _32062).
Proof. exact (TRANS (@lem3080403 _32062) (@lem3080505 _32062)). Qed.
Lemma lem3080507 (_32062 : int) : (term198 _32062) = term61.
Proof. exact (@lem1982719 (real_of_int _32062)). Qed.
Lemma lem3080508 (_32062 : int) : (term180 _32062) = term61.
Proof. exact (TRANS (@lem3080506 _32062) (@lem3080507 _32062)). Qed.
Lemma lem3080509 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080510 (_32062 : int) : (term199 _32062) = term200.
Proof. exact (MK_COMB (@lem3080509) (@lem3080508 _32062)). Qed.
Lemma lem3080511 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3080512 (_32062 : int) : (term791 _32062) = term205.
Proof. exact (MK_COMB (@lem3080510 _32062) (@lem3080511)). Qed.
Lemma lem3080513 (_32062 : int) : (term790 _32062) = term205.
Proof. exact (TRANS (@lem3080402 _32062) (@lem3080512 _32062)). Qed.
Lemma lem3080514 : term205 = term95.
Proof. exact (@lem1982721 term95). Qed.
Lemma lem3080515 (_32062 : int) : (term790 _32062) = term95.
Proof. exact (TRANS (@lem3080513 _32062) (@lem3080514)). Qed.
Lemma lem3080516 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3080517 (_32062 : int) : (term792 _32062) = term207.
Proof. exact (MK_COMB (@lem3080516) (@lem3080515 _32062)). Qed.
Lemma lem3080518 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3080519 (_32062 : int) : (term789 _32062) = term208.
Proof. exact (MK_COMB (@lem3080517 _32062) (@lem3080518)). Qed.
Lemma lem3080520 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : term208.
Proof. exact (EQ_MP (@lem3080519 _32062) (@lem3080401 _32061 _32062 h1)). Qed.
Lemma lem3080522 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3080523 : term208 = term209.
Proof. exact (@lem3080522 term61 term95). Qed.
Lemma lem3080525 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3080526 : term95 = term96.
Proof. exact (@lem3080525 term75). Qed.
Lemma lem3080528 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080529 : term61 = term92.
Proof. exact (@lem3080528 (NUMERAL 0)). Qed.
Lemma lem3080530 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3080531 : term63 = term210.
Proof. exact (MK_COMB (@lem3080530) (@lem3080529)). Qed.
Lemma lem3080532 : term209 = term211.
Proof. exact (MK_COMB (@lem3080531) (@lem3080526)). Qed.
Lemma lem3080533 : term212.
Proof. exact (@lem1980026 term61 term74 term95 term74). Qed.
Lemma lem3080535 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080536 : term150 = term156.
Proof. exact (@lem3080535 (NUMERAL 0) term75). Qed.
Lemma lem3080537 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080538 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080539 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080538 h1) (fun h1 : term156 = True => @lem3080537)). Qed.
Lemma lem3080540 : term156 = True.
Proof. exact (EQ_MP (@lem3080539) (@lem3080537)). Qed.
Lemma lem3080541 : term150 = True.
Proof. exact (TRANS (@lem3080536) (@lem3080540)). Qed.
Lemma lem3080542 : True = term150.
Proof. exact (SYM (@lem3080541)). Qed.
Lemma lem3080543 : term150.
Proof. exact (EQ_MP (@lem3080542) (@lem0)). Qed.
Lemma lem3080544 : term213.
Proof. exact (@lem3080533 (@lem3080543)). Qed.
Lemma lem3080546 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080547 : term150 = term156.
Proof. exact (@lem3080546 (NUMERAL 0) term75). Qed.
Lemma lem3080548 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080549 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080550 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080549 h1) (fun h1 : term156 = True => @lem3080548)). Qed.
Lemma lem3080551 : term156 = True.
Proof. exact (EQ_MP (@lem3080550) (@lem3080548)). Qed.
Lemma lem3080552 : term150 = True.
Proof. exact (TRANS (@lem3080547) (@lem3080551)). Qed.
Lemma lem3080553 : True = term150.
Proof. exact (SYM (@lem3080552)). Qed.
Lemma lem3080554 : term150.
Proof. exact (EQ_MP (@lem3080553) (@lem0)). Qed.
Lemma lem3080555 : term211 = term214.
Proof. exact (@lem3080544 (@lem3080554)). Qed.
Lemma lem3080557 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080558 : term122 = term127.
Proof. exact (@lem3080557 term75 term75). Qed.
Lemma lem3080559 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080560 : term107 = term75.
Proof. exact (EQ_MP (@lem3080559) (@lem940073)). Qed.
Lemma lem3080561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080562 : term105 = term74.
Proof. exact (MK_COMB (@lem3080561) (@lem3080560)). Qed.
Lemma lem3080563 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080564 : term127 = term95.
Proof. exact (MK_COMB (@lem3080563) (@lem3080562)). Qed.
Lemma lem3080565 : term122 = term95.
Proof. exact (TRANS (@lem3080558) (@lem3080564)). Qed.
Lemma lem3080567 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080568 : term161 = term61.
Proof. exact (@lem3080567 term75). Qed.
Lemma lem3080569 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3080570 : term215 = term63.
Proof. exact (MK_COMB (@lem3080569) (@lem3080568)). Qed.
Lemma lem3080571 : term214 = term209.
Proof. exact (MK_COMB (@lem3080570) (@lem3080565)). Qed.
Lemma lem3080573 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3080574 : term209 = term218.
Proof. exact (@lem3080573 (NUMERAL 0) term75). Qed.
Lemma lem3080575 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080576 (h1 : term157 = (BIT1 0)) : (term75 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3080577 : (term157 = (BIT1 0)) = ((term75 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080576 h1) (fun h1 : (term75 = (NUMERAL 0)) = False => @lem3080575)). Qed.
Lemma lem3080578 : (term75 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3080577) (@lem3080575)). Qed.
Lemma lem3080579 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3080580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3080581 : term219 = (and True).
Proof. exact (MK_COMB (@lem3080580) (@lem3080579)). Qed.
Lemma lem3080582 : term218 = (True /\ False).
Proof. exact (MK_COMB (@lem3080581) (@lem3080578)). Qed.
Lemma lem3080584 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3080585 : term218 = False.
Proof. exact (TRANS (@lem3080582) (@lem3080584)). Qed.
Lemma lem3080586 : term209 = False.
Proof. exact (TRANS (@lem3080574) (@lem3080585)). Qed.
Lemma lem3080587 : term214 = False.
Proof. exact (TRANS (@lem3080571) (@lem3080586)). Qed.
Lemma lem3080588 : term211 = False.
Proof. exact (TRANS (@lem3080555) (@lem3080587)). Qed.
Lemma lem3080589 : term209 = False.
Proof. exact (TRANS (@lem3080532) (@lem3080588)). Qed.
Lemma lem3080590 : term208 = False.
Proof. exact (TRANS (@lem3080523) (@lem3080589)). Qed.
Lemma lem3080591 (_32061 : int) (_32062 : int) (h1 : term841 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3080590) (@lem3080520 _32061 _32062 h1)). Qed.
Lemma lem3080592 (_32061 : int) (_32062 : int) (h1 : term763 _32061 _32062) : False.
Proof. exact (or_elim (@lem3079761 _32061 _32062 h1) (fun h0 : term840 _32061 _32062 => @lem3080237 _32061 _32062 h0) (fun h0 : term841 _32061 _32062 => @lem3080591 _32061 _32062 h0)). Qed.
Lemma lem3080593 (_32061 : int) (_32062 : int) (h1 : term772 _32061 _32062) : False.
Proof. exact (or_elim (@lem3078928 _32061 _32062 h1) (fun h0 : term767 _32061 _32062 => @lem3079760 _32061 _32062 h0) (fun h0 : term763 _32061 _32062 => @lem3080592 _32061 _32062 h0)). Qed.
Lemma lem3080594 (_32061 : int) (_32062 : int) (h1 : term759 _32061 _32062) : term759 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3080595 (_32061 : int) (_32062 : int) (h1 : term754 _32061 _32062) : term754 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3080596 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term842 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3080597 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term755 _32061 _32062.
Proof. exact (proj2 (@lem3080596 _32061 _32062 h1)). Qed.
Lemma lem3080598 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term115 _32061.
Proof. exact (proj1 (@lem3080596 _32061 _32062 h1)). Qed.
Lemma lem3080599 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term724 _32061 _32062.
Proof. exact (proj2 (@lem3080597 _32061 _32062 h1)). Qed.
Lemma lem3080601 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term689 _32061 _32062.
Proof. exact (proj2 (@lem3080599 _32061 _32062 h1)). Qed.
Lemma lem3080606 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term634 _32061.
Proof. exact (proj1 (@lem3080601 _32061 _32062 h1)). Qed.
Lemma lem3080608 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3080609 : term149 = term150.
Proof. exact (@lem3080608 term61 term74). Qed.
Lemma lem3080611 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080612 : term74 = term121.
Proof. exact (@lem3080611 term75). Qed.
Lemma lem3080614 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080615 : term61 = term92.
Proof. exact (@lem3080614 (NUMERAL 0)). Qed.
Lemma lem3080616 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080617 : term151 = term152.
Proof. exact (MK_COMB (@lem3080616) (@lem3080615)). Qed.
Lemma lem3080618 : term150 = term153.
Proof. exact (MK_COMB (@lem3080617) (@lem3080612)). Qed.
Lemma lem3080619 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3080621 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080622 : term150 = term156.
Proof. exact (@lem3080621 (NUMERAL 0) term75). Qed.
Lemma lem3080623 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080624 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080625 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080624 h1) (fun h1 : term156 = True => @lem3080623)). Qed.
Lemma lem3080626 : term156 = True.
Proof. exact (EQ_MP (@lem3080625) (@lem3080623)). Qed.
Lemma lem3080627 : term150 = True.
Proof. exact (TRANS (@lem3080622) (@lem3080626)). Qed.
Lemma lem3080628 : True = term150.
Proof. exact (SYM (@lem3080627)). Qed.
Lemma lem3080629 : term150.
Proof. exact (EQ_MP (@lem3080628) (@lem0)). Qed.
Lemma lem3080630 : term158.
Proof. exact (@lem3080619 (@lem3080629)). Qed.
Lemma lem3080632 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080633 : term150 = term156.
Proof. exact (@lem3080632 (NUMERAL 0) term75). Qed.
Lemma lem3080634 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080635 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080636 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080635 h1) (fun h1 : term156 = True => @lem3080634)). Qed.
Lemma lem3080637 : term156 = True.
Proof. exact (EQ_MP (@lem3080636) (@lem3080634)). Qed.
Lemma lem3080638 : term150 = True.
Proof. exact (TRANS (@lem3080633) (@lem3080637)). Qed.
Lemma lem3080639 : True = term150.
Proof. exact (SYM (@lem3080638)). Qed.
Lemma lem3080640 : term150.
Proof. exact (EQ_MP (@lem3080639) (@lem0)). Qed.
Lemma lem3080641 : term153 = term159.
Proof. exact (@lem3080630 (@lem3080640)). Qed.
Lemma lem3080643 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080644 : term104 = term105.
Proof. exact (@lem3080643 term75 term75). Qed.
Lemma lem3080645 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080646 : term107 = term75.
Proof. exact (EQ_MP (@lem3080645) (@lem940073)). Qed.
Lemma lem3080647 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080648 : term105 = term74.
Proof. exact (MK_COMB (@lem3080647) (@lem3080646)). Qed.
Lemma lem3080649 : term104 = term74.
Proof. exact (TRANS (@lem3080644) (@lem3080648)). Qed.
Lemma lem3080651 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080652 : term161 = term61.
Proof. exact (@lem3080651 term75). Qed.
Lemma lem3080653 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080654 : term162 = term151.
Proof. exact (MK_COMB (@lem3080653) (@lem3080652)). Qed.
Lemma lem3080655 : term159 = term150.
Proof. exact (MK_COMB (@lem3080654) (@lem3080649)). Qed.
Lemma lem3080657 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080658 : term150 = term156.
Proof. exact (@lem3080657 (NUMERAL 0) term75). Qed.
Lemma lem3080659 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080660 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080661 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080660 h1) (fun h1 : term156 = True => @lem3080659)). Qed.
Lemma lem3080662 : term156 = True.
Proof. exact (EQ_MP (@lem3080661) (@lem3080659)). Qed.
Lemma lem3080663 : term150 = True.
Proof. exact (TRANS (@lem3080658) (@lem3080662)). Qed.
Lemma lem3080664 : term159 = True.
Proof. exact (TRANS (@lem3080655) (@lem3080663)). Qed.
Lemma lem3080665 : term153 = True.
Proof. exact (TRANS (@lem3080641) (@lem3080664)). Qed.
Lemma lem3080666 : term150 = True.
Proof. exact (TRANS (@lem3080618) (@lem3080665)). Qed.
Lemma lem3080667 : term149 = True.
Proof. exact (TRANS (@lem3080609) (@lem3080666)). Qed.
Lemma lem3080668 : True = term149.
Proof. exact (SYM (@lem3080667)). Qed.
Lemma lem3080669 : term149.
Proof. exact (EQ_MP (@lem3080668) (@lem0)). Qed.
Lemma lem3080670 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term777 _32061.
Proof. exact (conj (@lem3080669) (@lem3080598 _32061 _32062 h1)). Qed.
Lemma lem3080672 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3080673 (_32061 : int) : term778 _32061.
Proof. exact (@lem3080672 term74 (real_of_int _32061)). Qed.
Lemma lem3080674 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term779 _32061.
Proof. exact (@lem3080673 _32061 (@lem3080670 _32061 _32062 h1)). Qed.
Lemma lem3080675 (_32061 : int) : (term780 _32061) = (real_of_int _32061).
Proof. exact (@lem1982733 (real_of_int _32061)). Qed.
Lemma lem3080676 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3080677 (_32061 : int) : (term781 _32061) = (term114 _32061).
Proof. exact (MK_COMB (@lem3080676) (@lem3080675 _32061)). Qed.
Lemma lem3080678 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3080679 (_32061 : int) : (term779 _32061) = (term115 _32061).
Proof. exact (MK_COMB (@lem3080677 _32061) (@lem3080678)). Qed.
Lemma lem3080680 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term115 _32061.
Proof. exact (EQ_MP (@lem3080679 _32061) (@lem3080674 _32061 _32062 h1)). Qed.
Lemma lem3080682 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3080683 : term149 = term150.
Proof. exact (@lem3080682 term61 term74). Qed.
Lemma lem3080685 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080686 : term74 = term121.
Proof. exact (@lem3080685 term75). Qed.
Lemma lem3080688 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080689 : term61 = term92.
Proof. exact (@lem3080688 (NUMERAL 0)). Qed.
Lemma lem3080690 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080691 : term151 = term152.
Proof. exact (MK_COMB (@lem3080690) (@lem3080689)). Qed.
Lemma lem3080692 : term150 = term153.
Proof. exact (MK_COMB (@lem3080691) (@lem3080686)). Qed.
Lemma lem3080693 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3080695 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080696 : term150 = term156.
Proof. exact (@lem3080695 (NUMERAL 0) term75). Qed.
Lemma lem3080697 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080698 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080699 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080698 h1) (fun h1 : term156 = True => @lem3080697)). Qed.
Lemma lem3080700 : term156 = True.
Proof. exact (EQ_MP (@lem3080699) (@lem3080697)). Qed.
Lemma lem3080701 : term150 = True.
Proof. exact (TRANS (@lem3080696) (@lem3080700)). Qed.
Lemma lem3080702 : True = term150.
Proof. exact (SYM (@lem3080701)). Qed.
Lemma lem3080703 : term150.
Proof. exact (EQ_MP (@lem3080702) (@lem0)). Qed.
Lemma lem3080704 : term158.
Proof. exact (@lem3080693 (@lem3080703)). Qed.
Lemma lem3080706 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080707 : term150 = term156.
Proof. exact (@lem3080706 (NUMERAL 0) term75). Qed.
Lemma lem3080708 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080709 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080710 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080709 h1) (fun h1 : term156 = True => @lem3080708)). Qed.
Lemma lem3080711 : term156 = True.
Proof. exact (EQ_MP (@lem3080710) (@lem3080708)). Qed.
Lemma lem3080712 : term150 = True.
Proof. exact (TRANS (@lem3080707) (@lem3080711)). Qed.
Lemma lem3080713 : True = term150.
Proof. exact (SYM (@lem3080712)). Qed.
Lemma lem3080714 : term150.
Proof. exact (EQ_MP (@lem3080713) (@lem0)). Qed.
Lemma lem3080715 : term153 = term159.
Proof. exact (@lem3080704 (@lem3080714)). Qed.
Lemma lem3080717 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080718 : term104 = term105.
Proof. exact (@lem3080717 term75 term75). Qed.
Lemma lem3080719 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080720 : term107 = term75.
Proof. exact (EQ_MP (@lem3080719) (@lem940073)). Qed.
Lemma lem3080721 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080722 : term105 = term74.
Proof. exact (MK_COMB (@lem3080721) (@lem3080720)). Qed.
Lemma lem3080723 : term104 = term74.
Proof. exact (TRANS (@lem3080718) (@lem3080722)). Qed.
Lemma lem3080725 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080726 : term161 = term61.
Proof. exact (@lem3080725 term75). Qed.
Lemma lem3080727 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080728 : term162 = term151.
Proof. exact (MK_COMB (@lem3080727) (@lem3080726)). Qed.
Lemma lem3080729 : term159 = term150.
Proof. exact (MK_COMB (@lem3080728) (@lem3080723)). Qed.
Lemma lem3080731 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080732 : term150 = term156.
Proof. exact (@lem3080731 (NUMERAL 0) term75). Qed.
Lemma lem3080733 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080734 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080735 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080734 h1) (fun h1 : term156 = True => @lem3080733)). Qed.
Lemma lem3080736 : term156 = True.
Proof. exact (EQ_MP (@lem3080735) (@lem3080733)). Qed.
Lemma lem3080737 : term150 = True.
Proof. exact (TRANS (@lem3080732) (@lem3080736)). Qed.
Lemma lem3080738 : term159 = True.
Proof. exact (TRANS (@lem3080729) (@lem3080737)). Qed.
Lemma lem3080739 : term153 = True.
Proof. exact (TRANS (@lem3080715) (@lem3080738)). Qed.
Lemma lem3080740 : term150 = True.
Proof. exact (TRANS (@lem3080692) (@lem3080739)). Qed.
Lemma lem3080741 : term149 = True.
Proof. exact (TRANS (@lem3080683) (@lem3080740)). Qed.
Lemma lem3080742 : True = term149.
Proof. exact (SYM (@lem3080741)). Qed.
Lemma lem3080743 : term149.
Proof. exact (EQ_MP (@lem3080742) (@lem0)). Qed.
Lemma lem3080744 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term782 _32061.
Proof. exact (conj (@lem3080743) (@lem3080606 _32061 _32062 h1)). Qed.
Lemma lem3080746 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3080747 (_32061 : int) : term783 _32061.
Proof. exact (@lem3080746 term74 (term131 _32061)). Qed.
Lemma lem3080748 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term784 _32061.
Proof. exact (@lem3080747 _32061 (@lem3080744 _32061 _32062 h1)). Qed.
Lemma lem3080749 (_32061 : int) : (term785 _32061) = (term131 _32061).
Proof. exact (@lem1982733 (term131 _32061)). Qed.
Lemma lem3080750 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3080751 (_32061 : int) : (term786 _32061) = (term633 _32061).
Proof. exact (MK_COMB (@lem3080750) (@lem3080749 _32061)). Qed.
Lemma lem3080752 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3080753 (_32061 : int) : (term784 _32061) = (term634 _32061).
Proof. exact (MK_COMB (@lem3080751 _32061) (@lem3080752)). Qed.
Lemma lem3080754 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term634 _32061.
Proof. exact (EQ_MP (@lem3080753 _32061) (@lem3080748 _32061 _32062 h1)). Qed.
Lemma lem3080755 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term787 _32061.
Proof. exact (conj (@lem3080754 _32061 _32062 h1) (@lem3080680 _32061 _32062 h1)). Qed.
Lemma lem3080757 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3080758 (_32061 : int) : term788 _32061.
Proof. exact (@lem3080757 (term131 _32061) (real_of_int _32061)). Qed.
Lemma lem3080759 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term789 _32061.
Proof. exact (@lem3080758 _32061 (@lem3080755 _32061 _32062 h1)). Qed.
Lemma lem3080760 (_32061 : int) : (term790 _32061) = (term791 _32061).
Proof. exact (@lem1982759 (term140 _32061) (real_of_int _32061) term95). Qed.
Lemma lem3080761 (_32061 : int) : (term180 _32061) = (term181 _32061).
Proof. exact (@lem1982713 term95 (real_of_int _32061)). Qed.
Lemma lem3080763 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080764 : term74 = term121.
Proof. exact (@lem3080763 term75). Qed.
Lemma lem3080766 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3080767 : term95 = term96.
Proof. exact (@lem3080766 term75). Qed.
Lemma lem3080768 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080769 : term182 = term183.
Proof. exact (MK_COMB (@lem3080768) (@lem3080767)). Qed.
Lemma lem3080770 : term184 = term185.
Proof. exact (MK_COMB (@lem3080769) (@lem3080764)). Qed.
Lemma lem3080771 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3080773 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080774 : term150 = term156.
Proof. exact (@lem3080773 (NUMERAL 0) term75). Qed.
Lemma lem3080775 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080776 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080777 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080776 h1) (fun h1 : term156 = True => @lem3080775)). Qed.
Lemma lem3080778 : term156 = True.
Proof. exact (EQ_MP (@lem3080777) (@lem3080775)). Qed.
Lemma lem3080779 : term150 = True.
Proof. exact (TRANS (@lem3080774) (@lem3080778)). Qed.
Lemma lem3080780 : True = term150.
Proof. exact (SYM (@lem3080779)). Qed.
Lemma lem3080781 : term150.
Proof. exact (EQ_MP (@lem3080780) (@lem0)). Qed.
Lemma lem3080782 : term187.
Proof. exact (@lem3080771 (@lem3080781)). Qed.
Lemma lem3080784 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080785 : term150 = term156.
Proof. exact (@lem3080784 (NUMERAL 0) term75). Qed.
Lemma lem3080786 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080787 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080788 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080787 h1) (fun h1 : term156 = True => @lem3080786)). Qed.
Lemma lem3080789 : term156 = True.
Proof. exact (EQ_MP (@lem3080788) (@lem3080786)). Qed.
Lemma lem3080790 : term150 = True.
Proof. exact (TRANS (@lem3080785) (@lem3080789)). Qed.
Lemma lem3080791 : True = term150.
Proof. exact (SYM (@lem3080790)). Qed.
Lemma lem3080792 : term150.
Proof. exact (EQ_MP (@lem3080791) (@lem0)). Qed.
Lemma lem3080793 : term188.
Proof. exact (@lem3080782 (@lem3080792)). Qed.
Lemma lem3080795 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080796 : term150 = term156.
Proof. exact (@lem3080795 (NUMERAL 0) term75). Qed.
Lemma lem3080797 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080798 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080799 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080798 h1) (fun h1 : term156 = True => @lem3080797)). Qed.
Lemma lem3080800 : term156 = True.
Proof. exact (EQ_MP (@lem3080799) (@lem3080797)). Qed.
Lemma lem3080801 : term150 = True.
Proof. exact (TRANS (@lem3080796) (@lem3080800)). Qed.
Lemma lem3080802 : True = term150.
Proof. exact (SYM (@lem3080801)). Qed.
Lemma lem3080803 : term150.
Proof. exact (EQ_MP (@lem3080802) (@lem0)). Qed.
Lemma lem3080804 : term189.
Proof. exact (@lem3080793 (@lem3080803)). Qed.
Lemma lem3080806 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080807 : term104 = term105.
Proof. exact (@lem3080806 term75 term75). Qed.
Lemma lem3080808 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080809 : term107 = term75.
Proof. exact (EQ_MP (@lem3080808) (@lem940073)). Qed.
Lemma lem3080810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080811 : term105 = term74.
Proof. exact (MK_COMB (@lem3080810) (@lem3080809)). Qed.
Lemma lem3080812 : term104 = term74.
Proof. exact (TRANS (@lem3080807) (@lem3080811)). Qed.
Lemma lem3080814 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080815 : term122 = term127.
Proof. exact (@lem3080814 term75 term75). Qed.
Lemma lem3080816 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080817 : term107 = term75.
Proof. exact (EQ_MP (@lem3080816) (@lem940073)). Qed.
Lemma lem3080818 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080819 : term105 = term74.
Proof. exact (MK_COMB (@lem3080818) (@lem3080817)). Qed.
Lemma lem3080820 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080821 : term127 = term95.
Proof. exact (MK_COMB (@lem3080820) (@lem3080819)). Qed.
Lemma lem3080822 : term122 = term95.
Proof. exact (TRANS (@lem3080815) (@lem3080821)). Qed.
Lemma lem3080823 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080824 : term190 = term182.
Proof. exact (MK_COMB (@lem3080823) (@lem3080822)). Qed.
Lemma lem3080825 : term191 = term184.
Proof. exact (MK_COMB (@lem3080824) (@lem3080812)). Qed.
Lemma lem3080827 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3080828 : term184 = term61.
Proof. exact (@lem3080827 term75). Qed.
Lemma lem3080829 : term191 = term61.
Proof. exact (TRANS (@lem3080825) (@lem3080828)). Qed.
Lemma lem3080830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3080831 : term193 = term194.
Proof. exact (MK_COMB (@lem3080830) (@lem3080829)). Qed.
Lemma lem3080832 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3080833 : term195 = term161.
Proof. exact (MK_COMB (@lem3080831) (@lem3080832)). Qed.
Lemma lem3080835 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080836 : term161 = term61.
Proof. exact (@lem3080835 term75). Qed.
Lemma lem3080837 : term195 = term61.
Proof. exact (TRANS (@lem3080833) (@lem3080836)). Qed.
Lemma lem3080839 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080840 : term104 = term105.
Proof. exact (@lem3080839 term75 term75). Qed.
Lemma lem3080841 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080842 : term107 = term75.
Proof. exact (EQ_MP (@lem3080841) (@lem940073)). Qed.
Lemma lem3080843 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080844 : term105 = term74.
Proof. exact (MK_COMB (@lem3080843) (@lem3080842)). Qed.
Lemma lem3080845 : term104 = term74.
Proof. exact (TRANS (@lem3080840) (@lem3080844)). Qed.
Lemma lem3080846 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3080847 : term196 = term161.
Proof. exact (MK_COMB (@lem3080846) (@lem3080845)). Qed.
Lemma lem3080849 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080850 : term161 = term61.
Proof. exact (@lem3080849 term75). Qed.
Lemma lem3080851 : term196 = term61.
Proof. exact (TRANS (@lem3080847) (@lem3080850)). Qed.
Lemma lem3080852 : term61 = term196.
Proof. exact (SYM (@lem3080851)). Qed.
Lemma lem3080853 : term195 = term196.
Proof. exact (TRANS (@lem3080837) (@lem3080852)). Qed.
Lemma lem3080854 : term185 = term92.
Proof. exact (@lem3080804 (@lem3080853)). Qed.
Lemma lem3080855 : term184 = term92.
Proof. exact (TRANS (@lem3080770) (@lem3080854)). Qed.
Lemma lem3080857 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3080858 : term92 = term61.
Proof. exact (@lem3080857 term61). Qed.
Lemma lem3080859 : term184 = term61.
Proof. exact (TRANS (@lem3080855) (@lem3080858)). Qed.
Lemma lem3080860 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3080861 : term197 = term194.
Proof. exact (MK_COMB (@lem3080860) (@lem3080859)). Qed.
Lemma lem3080862 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3080863 (_32061 : int) : (term181 _32061) = (term198 _32061).
Proof. exact (MK_COMB (@lem3080861) (@lem3080862 _32061)). Qed.
Lemma lem3080864 (_32061 : int) : (term180 _32061) = (term198 _32061).
Proof. exact (TRANS (@lem3080761 _32061) (@lem3080863 _32061)). Qed.
Lemma lem3080865 (_32061 : int) : (term198 _32061) = term61.
Proof. exact (@lem1982719 (real_of_int _32061)). Qed.
Lemma lem3080866 (_32061 : int) : (term180 _32061) = term61.
Proof. exact (TRANS (@lem3080864 _32061) (@lem3080865 _32061)). Qed.
Lemma lem3080867 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3080868 (_32061 : int) : (term199 _32061) = term200.
Proof. exact (MK_COMB (@lem3080867) (@lem3080866 _32061)). Qed.
Lemma lem3080869 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3080870 (_32061 : int) : (term791 _32061) = term205.
Proof. exact (MK_COMB (@lem3080868 _32061) (@lem3080869)). Qed.
Lemma lem3080871 (_32061 : int) : (term790 _32061) = term205.
Proof. exact (TRANS (@lem3080760 _32061) (@lem3080870 _32061)). Qed.
Lemma lem3080872 : term205 = term95.
Proof. exact (@lem1982721 term95). Qed.
Lemma lem3080873 (_32061 : int) : (term790 _32061) = term95.
Proof. exact (TRANS (@lem3080871 _32061) (@lem3080872)). Qed.
Lemma lem3080874 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3080875 (_32061 : int) : (term792 _32061) = term207.
Proof. exact (MK_COMB (@lem3080874) (@lem3080873 _32061)). Qed.
Lemma lem3080876 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3080877 (_32061 : int) : (term789 _32061) = term208.
Proof. exact (MK_COMB (@lem3080875 _32061) (@lem3080876)). Qed.
Lemma lem3080878 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : term208.
Proof. exact (EQ_MP (@lem3080877 _32061) (@lem3080759 _32061 _32062 h1)). Qed.
Lemma lem3080880 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3080881 : term208 = term209.
Proof. exact (@lem3080880 term61 term95). Qed.
Lemma lem3080883 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3080884 : term95 = term96.
Proof. exact (@lem3080883 term75). Qed.
Lemma lem3080886 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080887 : term61 = term92.
Proof. exact (@lem3080886 (NUMERAL 0)). Qed.
Lemma lem3080888 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3080889 : term63 = term210.
Proof. exact (MK_COMB (@lem3080888) (@lem3080887)). Qed.
Lemma lem3080890 : term209 = term211.
Proof. exact (MK_COMB (@lem3080889) (@lem3080884)). Qed.
Lemma lem3080891 : term212.
Proof. exact (@lem1980026 term61 term74 term95 term74). Qed.
Lemma lem3080893 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080894 : term150 = term156.
Proof. exact (@lem3080893 (NUMERAL 0) term75). Qed.
Lemma lem3080895 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080896 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080897 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080896 h1) (fun h1 : term156 = True => @lem3080895)). Qed.
Lemma lem3080898 : term156 = True.
Proof. exact (EQ_MP (@lem3080897) (@lem3080895)). Qed.
Lemma lem3080899 : term150 = True.
Proof. exact (TRANS (@lem3080894) (@lem3080898)). Qed.
Lemma lem3080900 : True = term150.
Proof. exact (SYM (@lem3080899)). Qed.
Lemma lem3080901 : term150.
Proof. exact (EQ_MP (@lem3080900) (@lem0)). Qed.
Lemma lem3080902 : term213.
Proof. exact (@lem3080891 (@lem3080901)). Qed.
Lemma lem3080904 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080905 : term150 = term156.
Proof. exact (@lem3080904 (NUMERAL 0) term75). Qed.
Lemma lem3080906 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080907 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080908 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080907 h1) (fun h1 : term156 = True => @lem3080906)). Qed.
Lemma lem3080909 : term156 = True.
Proof. exact (EQ_MP (@lem3080908) (@lem3080906)). Qed.
Lemma lem3080910 : term150 = True.
Proof. exact (TRANS (@lem3080905) (@lem3080909)). Qed.
Lemma lem3080911 : True = term150.
Proof. exact (SYM (@lem3080910)). Qed.
Lemma lem3080912 : term150.
Proof. exact (EQ_MP (@lem3080911) (@lem0)). Qed.
Lemma lem3080913 : term211 = term214.
Proof. exact (@lem3080902 (@lem3080912)). Qed.
Lemma lem3080915 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3080916 : term122 = term127.
Proof. exact (@lem3080915 term75 term75). Qed.
Lemma lem3080917 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3080918 : term107 = term75.
Proof. exact (EQ_MP (@lem3080917) (@lem940073)). Qed.
Lemma lem3080919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3080920 : term105 = term74.
Proof. exact (MK_COMB (@lem3080919) (@lem3080918)). Qed.
Lemma lem3080921 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3080922 : term127 = term95.
Proof. exact (MK_COMB (@lem3080921) (@lem3080920)). Qed.
Lemma lem3080923 : term122 = term95.
Proof. exact (TRANS (@lem3080916) (@lem3080922)). Qed.
Lemma lem3080925 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3080926 : term161 = term61.
Proof. exact (@lem3080925 term75). Qed.
Lemma lem3080927 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3080928 : term215 = term63.
Proof. exact (MK_COMB (@lem3080927) (@lem3080926)). Qed.
Lemma lem3080929 : term214 = term209.
Proof. exact (MK_COMB (@lem3080928) (@lem3080923)). Qed.
Lemma lem3080931 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3080932 : term209 = term218.
Proof. exact (@lem3080931 (NUMERAL 0) term75). Qed.
Lemma lem3080933 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080934 (h1 : term157 = (BIT1 0)) : (term75 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3080935 : (term157 = (BIT1 0)) = ((term75 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080934 h1) (fun h1 : (term75 = (NUMERAL 0)) = False => @lem3080933)). Qed.
Lemma lem3080936 : (term75 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3080935) (@lem3080933)). Qed.
Lemma lem3080937 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3080938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3080939 : term219 = (and True).
Proof. exact (MK_COMB (@lem3080938) (@lem3080937)). Qed.
Lemma lem3080940 : term218 = (True /\ False).
Proof. exact (MK_COMB (@lem3080939) (@lem3080936)). Qed.
Lemma lem3080942 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3080943 : term218 = False.
Proof. exact (TRANS (@lem3080940) (@lem3080942)). Qed.
Lemma lem3080944 : term209 = False.
Proof. exact (TRANS (@lem3080932) (@lem3080943)). Qed.
Lemma lem3080945 : term214 = False.
Proof. exact (TRANS (@lem3080929) (@lem3080944)). Qed.
Lemma lem3080946 : term211 = False.
Proof. exact (TRANS (@lem3080913) (@lem3080945)). Qed.
Lemma lem3080947 : term209 = False.
Proof. exact (TRANS (@lem3080890) (@lem3080946)). Qed.
Lemma lem3080948 : term208 = False.
Proof. exact (TRANS (@lem3080881) (@lem3080947)). Qed.
Lemma lem3080949 (_32061 : int) (_32062 : int) (h1 : term842 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3080948) (@lem3080878 _32061 _32062 h1)). Qed.
Lemma lem3080950 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term843 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3080951 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term756 _32061 _32062.
Proof. exact (proj2 (@lem3080950 _32061 _32062 h1)). Qed.
Lemma lem3080953 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term725 _32061 _32062.
Proof. exact (proj2 (@lem3080951 _32061 _32062 h1)). Qed.
Lemma lem3080955 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term689 _32061 _32062.
Proof. exact (proj2 (@lem3080953 _32061 _32062 h1)). Qed.
Lemma lem3080956 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term694 _32061 _32062.
Proof. exact (proj1 (@lem3080953 _32061 _32062 h1)). Qed.
Lemma lem3080958 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term643 _32061.
Proof. exact (proj1 (@lem3080956 _32061 _32062 h1)). Qed.
Lemma lem3080960 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term634 _32061.
Proof. exact (proj1 (@lem3080955 _32061 _32062 h1)). Qed.
Lemma lem3080962 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3080963 : term149 = term150.
Proof. exact (@lem3080962 term61 term74). Qed.
Lemma lem3080965 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080966 : term74 = term121.
Proof. exact (@lem3080965 term75). Qed.
Lemma lem3080968 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3080969 : term61 = term92.
Proof. exact (@lem3080968 (NUMERAL 0)). Qed.
Lemma lem3080970 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3080971 : term151 = term152.
Proof. exact (MK_COMB (@lem3080970) (@lem3080969)). Qed.
Lemma lem3080972 : term150 = term153.
Proof. exact (MK_COMB (@lem3080971) (@lem3080966)). Qed.
Lemma lem3080973 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3080975 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080976 : term150 = term156.
Proof. exact (@lem3080975 (NUMERAL 0) term75). Qed.
Lemma lem3080977 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080978 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080979 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080978 h1) (fun h1 : term156 = True => @lem3080977)). Qed.
Lemma lem3080980 : term156 = True.
Proof. exact (EQ_MP (@lem3080979) (@lem3080977)). Qed.
Lemma lem3080981 : term150 = True.
Proof. exact (TRANS (@lem3080976) (@lem3080980)). Qed.
Lemma lem3080982 : True = term150.
Proof. exact (SYM (@lem3080981)). Qed.
Lemma lem3080983 : term150.
Proof. exact (EQ_MP (@lem3080982) (@lem0)). Qed.
Lemma lem3080984 : term158.
Proof. exact (@lem3080973 (@lem3080983)). Qed.
Lemma lem3080986 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3080987 : term150 = term156.
Proof. exact (@lem3080986 (NUMERAL 0) term75). Qed.
Lemma lem3080988 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3080989 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3080990 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3080989 h1) (fun h1 : term156 = True => @lem3080988)). Qed.
Lemma lem3080991 : term156 = True.
Proof. exact (EQ_MP (@lem3080990) (@lem3080988)). Qed.
Lemma lem3080992 : term150 = True.
Proof. exact (TRANS (@lem3080987) (@lem3080991)). Qed.
Lemma lem3080993 : True = term150.
Proof. exact (SYM (@lem3080992)). Qed.
Lemma lem3080994 : term150.
Proof. exact (EQ_MP (@lem3080993) (@lem0)). Qed.
Lemma lem3080995 : term153 = term159.
Proof. exact (@lem3080984 (@lem3080994)). Qed.
Lemma lem3080997 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3080998 : term104 = term105.
Proof. exact (@lem3080997 term75 term75). Qed.
Lemma lem3080999 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081000 : term107 = term75.
Proof. exact (EQ_MP (@lem3080999) (@lem940073)). Qed.
Lemma lem3081001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081002 : term105 = term74.
Proof. exact (MK_COMB (@lem3081001) (@lem3081000)). Qed.
Lemma lem3081003 : term104 = term74.
Proof. exact (TRANS (@lem3080998) (@lem3081002)). Qed.
Lemma lem3081005 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081006 : term161 = term61.
Proof. exact (@lem3081005 term75). Qed.
Lemma lem3081007 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081008 : term162 = term151.
Proof. exact (MK_COMB (@lem3081007) (@lem3081006)). Qed.
Lemma lem3081009 : term159 = term150.
Proof. exact (MK_COMB (@lem3081008) (@lem3081003)). Qed.
Lemma lem3081011 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081012 : term150 = term156.
Proof. exact (@lem3081011 (NUMERAL 0) term75). Qed.
Lemma lem3081013 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081014 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081015 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081014 h1) (fun h1 : term156 = True => @lem3081013)). Qed.
Lemma lem3081016 : term156 = True.
Proof. exact (EQ_MP (@lem3081015) (@lem3081013)). Qed.
Lemma lem3081017 : term150 = True.
Proof. exact (TRANS (@lem3081012) (@lem3081016)). Qed.
Lemma lem3081018 : term159 = True.
Proof. exact (TRANS (@lem3081009) (@lem3081017)). Qed.
Lemma lem3081019 : term153 = True.
Proof. exact (TRANS (@lem3080995) (@lem3081018)). Qed.
Lemma lem3081020 : term150 = True.
Proof. exact (TRANS (@lem3080972) (@lem3081019)). Qed.
Lemma lem3081021 : term149 = True.
Proof. exact (TRANS (@lem3080963) (@lem3081020)). Qed.
Lemma lem3081022 : True = term149.
Proof. exact (SYM (@lem3081021)). Qed.
Lemma lem3081023 : term149.
Proof. exact (EQ_MP (@lem3081022) (@lem0)). Qed.
Lemma lem3081024 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term794 _32061.
Proof. exact (conj (@lem3081023) (@lem3080958 _32061 _32062 h1)). Qed.
Lemma lem3081026 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3081027 (_32061 : int) : term795 _32061.
Proof. exact (@lem3081026 term74 (term640 _32061)). Qed.
Lemma lem3081028 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term796 _32061.
Proof. exact (@lem3081027 _32061 (@lem3081024 _32061 _32062 h1)). Qed.
Lemma lem3081029 (_32061 : int) : (term797 _32061) = (term640 _32061).
Proof. exact (@lem1982733 (term640 _32061)). Qed.
Lemma lem3081030 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3081031 (_32061 : int) : (term798 _32061) = (term642 _32061).
Proof. exact (MK_COMB (@lem3081030) (@lem3081029 _32061)). Qed.
Lemma lem3081032 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3081033 (_32061 : int) : (term796 _32061) = (term643 _32061).
Proof. exact (MK_COMB (@lem3081031 _32061) (@lem3081032)). Qed.
Lemma lem3081034 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term643 _32061.
Proof. exact (EQ_MP (@lem3081033 _32061) (@lem3081028 _32061 _32062 h1)). Qed.
Lemma lem3081036 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3081037 : term149 = term150.
Proof. exact (@lem3081036 term61 term74). Qed.
Lemma lem3081039 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081040 : term74 = term121.
Proof. exact (@lem3081039 term75). Qed.
Lemma lem3081042 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081043 : term61 = term92.
Proof. exact (@lem3081042 (NUMERAL 0)). Qed.
Lemma lem3081044 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081045 : term151 = term152.
Proof. exact (MK_COMB (@lem3081044) (@lem3081043)). Qed.
Lemma lem3081046 : term150 = term153.
Proof. exact (MK_COMB (@lem3081045) (@lem3081040)). Qed.
Lemma lem3081047 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3081049 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081050 : term150 = term156.
Proof. exact (@lem3081049 (NUMERAL 0) term75). Qed.
Lemma lem3081051 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081052 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081053 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081052 h1) (fun h1 : term156 = True => @lem3081051)). Qed.
Lemma lem3081054 : term156 = True.
Proof. exact (EQ_MP (@lem3081053) (@lem3081051)). Qed.
Lemma lem3081055 : term150 = True.
Proof. exact (TRANS (@lem3081050) (@lem3081054)). Qed.
Lemma lem3081056 : True = term150.
Proof. exact (SYM (@lem3081055)). Qed.
Lemma lem3081057 : term150.
Proof. exact (EQ_MP (@lem3081056) (@lem0)). Qed.
Lemma lem3081058 : term158.
Proof. exact (@lem3081047 (@lem3081057)). Qed.
Lemma lem3081060 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081061 : term150 = term156.
Proof. exact (@lem3081060 (NUMERAL 0) term75). Qed.
Lemma lem3081062 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081063 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081064 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081063 h1) (fun h1 : term156 = True => @lem3081062)). Qed.
Lemma lem3081065 : term156 = True.
Proof. exact (EQ_MP (@lem3081064) (@lem3081062)). Qed.
Lemma lem3081066 : term150 = True.
Proof. exact (TRANS (@lem3081061) (@lem3081065)). Qed.
Lemma lem3081067 : True = term150.
Proof. exact (SYM (@lem3081066)). Qed.
Lemma lem3081068 : term150.
Proof. exact (EQ_MP (@lem3081067) (@lem0)). Qed.
Lemma lem3081069 : term153 = term159.
Proof. exact (@lem3081058 (@lem3081068)). Qed.
Lemma lem3081071 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081072 : term104 = term105.
Proof. exact (@lem3081071 term75 term75). Qed.
Lemma lem3081073 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081074 : term107 = term75.
Proof. exact (EQ_MP (@lem3081073) (@lem940073)). Qed.
Lemma lem3081075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081076 : term105 = term74.
Proof. exact (MK_COMB (@lem3081075) (@lem3081074)). Qed.
Lemma lem3081077 : term104 = term74.
Proof. exact (TRANS (@lem3081072) (@lem3081076)). Qed.
Lemma lem3081079 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081080 : term161 = term61.
Proof. exact (@lem3081079 term75). Qed.
Lemma lem3081081 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081082 : term162 = term151.
Proof. exact (MK_COMB (@lem3081081) (@lem3081080)). Qed.
Lemma lem3081083 : term159 = term150.
Proof. exact (MK_COMB (@lem3081082) (@lem3081077)). Qed.
Lemma lem3081085 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081086 : term150 = term156.
Proof. exact (@lem3081085 (NUMERAL 0) term75). Qed.
Lemma lem3081087 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081088 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081089 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081088 h1) (fun h1 : term156 = True => @lem3081087)). Qed.
Lemma lem3081090 : term156 = True.
Proof. exact (EQ_MP (@lem3081089) (@lem3081087)). Qed.
Lemma lem3081091 : term150 = True.
Proof. exact (TRANS (@lem3081086) (@lem3081090)). Qed.
Lemma lem3081092 : term159 = True.
Proof. exact (TRANS (@lem3081083) (@lem3081091)). Qed.
Lemma lem3081093 : term153 = True.
Proof. exact (TRANS (@lem3081069) (@lem3081092)). Qed.
Lemma lem3081094 : term150 = True.
Proof. exact (TRANS (@lem3081046) (@lem3081093)). Qed.
Lemma lem3081095 : term149 = True.
Proof. exact (TRANS (@lem3081037) (@lem3081094)). Qed.
Lemma lem3081096 : True = term149.
Proof. exact (SYM (@lem3081095)). Qed.
Lemma lem3081097 : term149.
Proof. exact (EQ_MP (@lem3081096) (@lem0)). Qed.
Lemma lem3081098 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term782 _32061.
Proof. exact (conj (@lem3081097) (@lem3080960 _32061 _32062 h1)). Qed.
Lemma lem3081100 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3081101 (_32061 : int) : term783 _32061.
Proof. exact (@lem3081100 term74 (term131 _32061)). Qed.
Lemma lem3081102 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term784 _32061.
Proof. exact (@lem3081101 _32061 (@lem3081098 _32061 _32062 h1)). Qed.
Lemma lem3081103 (_32061 : int) : (term785 _32061) = (term131 _32061).
Proof. exact (@lem1982733 (term131 _32061)). Qed.
Lemma lem3081104 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3081105 (_32061 : int) : (term786 _32061) = (term633 _32061).
Proof. exact (MK_COMB (@lem3081104) (@lem3081103 _32061)). Qed.
Lemma lem3081106 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3081107 (_32061 : int) : (term784 _32061) = (term634 _32061).
Proof. exact (MK_COMB (@lem3081105 _32061) (@lem3081106)). Qed.
Lemma lem3081108 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term634 _32061.
Proof. exact (EQ_MP (@lem3081107 _32061) (@lem3081102 _32061 _32062 h1)). Qed.
Lemma lem3081109 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term799 _32061.
Proof. exact (conj (@lem3081108 _32061 _32062 h1) (@lem3081034 _32061 _32062 h1)). Qed.
Lemma lem3081111 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3081112 (_32061 : int) : term800 _32061.
Proof. exact (@lem3081111 (term131 _32061) (term640 _32061)). Qed.
Lemma lem3081113 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term801 _32061.
Proof. exact (@lem3081112 _32061 (@lem3081109 _32061 _32062 h1)). Qed.
Lemma lem3081114 (_32061 : int) : (term802 _32061) = (term803 _32061).
Proof. exact (@lem1982753 (term140 _32061) (real_of_int _32061) term95 term95). Qed.
Lemma lem3081115 (_32061 : int) : (term180 _32061) = (term181 _32061).
Proof. exact (@lem1982713 term95 (real_of_int _32061)). Qed.
Lemma lem3081117 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081118 : term74 = term121.
Proof. exact (@lem3081117 term75). Qed.
Lemma lem3081120 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3081121 : term95 = term96.
Proof. exact (@lem3081120 term75). Qed.
Lemma lem3081122 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081123 : term182 = term183.
Proof. exact (MK_COMB (@lem3081122) (@lem3081121)). Qed.
Lemma lem3081124 : term184 = term185.
Proof. exact (MK_COMB (@lem3081123) (@lem3081118)). Qed.
Lemma lem3081125 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3081127 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081128 : term150 = term156.
Proof. exact (@lem3081127 (NUMERAL 0) term75). Qed.
Lemma lem3081129 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081130 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081131 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081130 h1) (fun h1 : term156 = True => @lem3081129)). Qed.
Lemma lem3081132 : term156 = True.
Proof. exact (EQ_MP (@lem3081131) (@lem3081129)). Qed.
Lemma lem3081133 : term150 = True.
Proof. exact (TRANS (@lem3081128) (@lem3081132)). Qed.
Lemma lem3081134 : True = term150.
Proof. exact (SYM (@lem3081133)). Qed.
Lemma lem3081135 : term150.
Proof. exact (EQ_MP (@lem3081134) (@lem0)). Qed.
Lemma lem3081136 : term187.
Proof. exact (@lem3081125 (@lem3081135)). Qed.
Lemma lem3081138 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081139 : term150 = term156.
Proof. exact (@lem3081138 (NUMERAL 0) term75). Qed.
Lemma lem3081140 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081141 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081142 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081141 h1) (fun h1 : term156 = True => @lem3081140)). Qed.
Lemma lem3081143 : term156 = True.
Proof. exact (EQ_MP (@lem3081142) (@lem3081140)). Qed.
Lemma lem3081144 : term150 = True.
Proof. exact (TRANS (@lem3081139) (@lem3081143)). Qed.
Lemma lem3081145 : True = term150.
Proof. exact (SYM (@lem3081144)). Qed.
Lemma lem3081146 : term150.
Proof. exact (EQ_MP (@lem3081145) (@lem0)). Qed.
Lemma lem3081147 : term188.
Proof. exact (@lem3081136 (@lem3081146)). Qed.
Lemma lem3081149 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081150 : term150 = term156.
Proof. exact (@lem3081149 (NUMERAL 0) term75). Qed.
Lemma lem3081151 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081152 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081153 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081152 h1) (fun h1 : term156 = True => @lem3081151)). Qed.
Lemma lem3081154 : term156 = True.
Proof. exact (EQ_MP (@lem3081153) (@lem3081151)). Qed.
Lemma lem3081155 : term150 = True.
Proof. exact (TRANS (@lem3081150) (@lem3081154)). Qed.
Lemma lem3081156 : True = term150.
Proof. exact (SYM (@lem3081155)). Qed.
Lemma lem3081157 : term150.
Proof. exact (EQ_MP (@lem3081156) (@lem0)). Qed.
Lemma lem3081158 : term189.
Proof. exact (@lem3081147 (@lem3081157)). Qed.
Lemma lem3081160 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081161 : term104 = term105.
Proof. exact (@lem3081160 term75 term75). Qed.
Lemma lem3081162 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081163 : term107 = term75.
Proof. exact (EQ_MP (@lem3081162) (@lem940073)). Qed.
Lemma lem3081164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081165 : term105 = term74.
Proof. exact (MK_COMB (@lem3081164) (@lem3081163)). Qed.
Lemma lem3081166 : term104 = term74.
Proof. exact (TRANS (@lem3081161) (@lem3081165)). Qed.
Lemma lem3081168 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081169 : term122 = term127.
Proof. exact (@lem3081168 term75 term75). Qed.
Lemma lem3081170 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081171 : term107 = term75.
Proof. exact (EQ_MP (@lem3081170) (@lem940073)). Qed.
Lemma lem3081172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081173 : term105 = term74.
Proof. exact (MK_COMB (@lem3081172) (@lem3081171)). Qed.
Lemma lem3081174 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081175 : term127 = term95.
Proof. exact (MK_COMB (@lem3081174) (@lem3081173)). Qed.
Lemma lem3081176 : term122 = term95.
Proof. exact (TRANS (@lem3081169) (@lem3081175)). Qed.
Lemma lem3081177 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081178 : term190 = term182.
Proof. exact (MK_COMB (@lem3081177) (@lem3081176)). Qed.
Lemma lem3081179 : term191 = term184.
Proof. exact (MK_COMB (@lem3081178) (@lem3081166)). Qed.
Lemma lem3081181 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3081182 : term184 = term61.
Proof. exact (@lem3081181 term75). Qed.
Lemma lem3081183 : term191 = term61.
Proof. exact (TRANS (@lem3081179) (@lem3081182)). Qed.
Lemma lem3081184 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3081185 : term193 = term194.
Proof. exact (MK_COMB (@lem3081184) (@lem3081183)). Qed.
Lemma lem3081186 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3081187 : term195 = term161.
Proof. exact (MK_COMB (@lem3081185) (@lem3081186)). Qed.
Lemma lem3081189 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081190 : term161 = term61.
Proof. exact (@lem3081189 term75). Qed.
Lemma lem3081191 : term195 = term61.
Proof. exact (TRANS (@lem3081187) (@lem3081190)). Qed.
Lemma lem3081193 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081194 : term104 = term105.
Proof. exact (@lem3081193 term75 term75). Qed.
Lemma lem3081195 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081196 : term107 = term75.
Proof. exact (EQ_MP (@lem3081195) (@lem940073)). Qed.
Lemma lem3081197 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081198 : term105 = term74.
Proof. exact (MK_COMB (@lem3081197) (@lem3081196)). Qed.
Lemma lem3081199 : term104 = term74.
Proof. exact (TRANS (@lem3081194) (@lem3081198)). Qed.
Lemma lem3081200 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3081201 : term196 = term161.
Proof. exact (MK_COMB (@lem3081200) (@lem3081199)). Qed.
Lemma lem3081203 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081204 : term161 = term61.
Proof. exact (@lem3081203 term75). Qed.
Lemma lem3081205 : term196 = term61.
Proof. exact (TRANS (@lem3081201) (@lem3081204)). Qed.
Lemma lem3081206 : term61 = term196.
Proof. exact (SYM (@lem3081205)). Qed.
Lemma lem3081207 : term195 = term196.
Proof. exact (TRANS (@lem3081191) (@lem3081206)). Qed.
Lemma lem3081208 : term185 = term92.
Proof. exact (@lem3081158 (@lem3081207)). Qed.
Lemma lem3081209 : term184 = term92.
Proof. exact (TRANS (@lem3081124) (@lem3081208)). Qed.
Lemma lem3081211 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3081212 : term92 = term61.
Proof. exact (@lem3081211 term61). Qed.
Lemma lem3081213 : term184 = term61.
Proof. exact (TRANS (@lem3081209) (@lem3081212)). Qed.
Lemma lem3081214 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3081215 : term197 = term194.
Proof. exact (MK_COMB (@lem3081214) (@lem3081213)). Qed.
Lemma lem3081216 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3081217 (_32061 : int) : (term181 _32061) = (term198 _32061).
Proof. exact (MK_COMB (@lem3081215) (@lem3081216 _32061)). Qed.
Lemma lem3081218 (_32061 : int) : (term180 _32061) = (term198 _32061).
Proof. exact (TRANS (@lem3081115 _32061) (@lem3081217 _32061)). Qed.
Lemma lem3081219 (_32061 : int) : (term198 _32061) = term61.
Proof. exact (@lem1982719 (real_of_int _32061)). Qed.
Lemma lem3081220 (_32061 : int) : (term180 _32061) = term61.
Proof. exact (TRANS (@lem3081218 _32061) (@lem3081219 _32061)). Qed.
Lemma lem3081221 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081222 (_32061 : int) : (term199 _32061) = term200.
Proof. exact (MK_COMB (@lem3081221) (@lem3081220 _32061)). Qed.
Lemma lem3081224 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3081225 : term95 = term96.
Proof. exact (@lem3081224 term75). Qed.
Lemma lem3081227 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3081228 : term95 = term96.
Proof. exact (@lem3081227 term75). Qed.
Lemma lem3081229 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081230 : term182 = term183.
Proof. exact (MK_COMB (@lem3081229) (@lem3081228)). Qed.
Lemma lem3081231 : term804 = term805.
Proof. exact (MK_COMB (@lem3081230) (@lem3081225)). Qed.
Lemma lem3081232 : term806.
Proof. exact (@lem1981473 term95 term74 term95 term74 term807 term74). Qed.
Lemma lem3081234 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081235 : term150 = term156.
Proof. exact (@lem3081234 (NUMERAL 0) term75). Qed.
Lemma lem3081236 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081237 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081238 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081237 h1) (fun h1 : term156 = True => @lem3081236)). Qed.
Lemma lem3081239 : term156 = True.
Proof. exact (EQ_MP (@lem3081238) (@lem3081236)). Qed.
Lemma lem3081240 : term150 = True.
Proof. exact (TRANS (@lem3081235) (@lem3081239)). Qed.
Lemma lem3081241 : True = term150.
Proof. exact (SYM (@lem3081240)). Qed.
Lemma lem3081242 : term150.
Proof. exact (EQ_MP (@lem3081241) (@lem0)). Qed.
Lemma lem3081243 : term808.
Proof. exact (@lem3081232 (@lem3081242)). Qed.
Lemma lem3081245 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081246 : term150 = term156.
Proof. exact (@lem3081245 (NUMERAL 0) term75). Qed.
Lemma lem3081247 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081248 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081249 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081248 h1) (fun h1 : term156 = True => @lem3081247)). Qed.
Lemma lem3081250 : term156 = True.
Proof. exact (EQ_MP (@lem3081249) (@lem3081247)). Qed.
Lemma lem3081251 : term150 = True.
Proof. exact (TRANS (@lem3081246) (@lem3081250)). Qed.
Lemma lem3081252 : True = term150.
Proof. exact (SYM (@lem3081251)). Qed.
Lemma lem3081253 : term150.
Proof. exact (EQ_MP (@lem3081252) (@lem0)). Qed.
Lemma lem3081254 : term809.
Proof. exact (@lem3081243 (@lem3081253)). Qed.
Lemma lem3081256 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081257 : term150 = term156.
Proof. exact (@lem3081256 (NUMERAL 0) term75). Qed.
Lemma lem3081258 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081259 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081260 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081259 h1) (fun h1 : term156 = True => @lem3081258)). Qed.
Lemma lem3081261 : term156 = True.
Proof. exact (EQ_MP (@lem3081260) (@lem3081258)). Qed.
Lemma lem3081262 : term150 = True.
Proof. exact (TRANS (@lem3081257) (@lem3081261)). Qed.
Lemma lem3081263 : True = term150.
Proof. exact (SYM (@lem3081262)). Qed.
Lemma lem3081264 : term150.
Proof. exact (EQ_MP (@lem3081263) (@lem0)). Qed.
Lemma lem3081265 : term810.
Proof. exact (@lem3081254 (@lem3081264)). Qed.
Lemma lem3081267 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081268 : term122 = term127.
Proof. exact (@lem3081267 term75 term75). Qed.
Lemma lem3081269 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081270 : term107 = term75.
Proof. exact (EQ_MP (@lem3081269) (@lem940073)). Qed.
Lemma lem3081271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081272 : term105 = term74.
Proof. exact (MK_COMB (@lem3081271) (@lem3081270)). Qed.
Lemma lem3081273 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081274 : term127 = term95.
Proof. exact (MK_COMB (@lem3081273) (@lem3081272)). Qed.
Lemma lem3081275 : term122 = term95.
Proof. exact (TRANS (@lem3081268) (@lem3081274)). Qed.
Lemma lem3081277 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081278 : term122 = term127.
Proof. exact (@lem3081277 term75 term75). Qed.
Lemma lem3081279 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081280 : term107 = term75.
Proof. exact (EQ_MP (@lem3081279) (@lem940073)). Qed.
Lemma lem3081281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081282 : term105 = term74.
Proof. exact (MK_COMB (@lem3081281) (@lem3081280)). Qed.
Lemma lem3081283 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081284 : term127 = term95.
Proof. exact (MK_COMB (@lem3081283) (@lem3081282)). Qed.
Lemma lem3081285 : term122 = term95.
Proof. exact (TRANS (@lem3081278) (@lem3081284)). Qed.
Lemma lem3081286 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081287 : term190 = term182.
Proof. exact (MK_COMB (@lem3081286) (@lem3081285)). Qed.
Lemma lem3081288 : term811 = term804.
Proof. exact (MK_COMB (@lem3081287) (@lem3081275)). Qed.
Lemma lem3081289 : term804 = term812.
Proof. exact (@lem1367763 term75 term75). Qed.
Lemma lem3081290 : term813 = term814.
Proof. exact (@lem706885). Qed.
Lemma lem3081291 : (term813 = term814) = (term815 = term816).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term814). Qed.
Lemma lem3081292 : term815 = term816.
Proof. exact (EQ_MP (@lem3081291) (@lem3081290)). Qed.
Lemma lem3081293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081294 : term817 = term818.
Proof. exact (MK_COMB (@lem3081293) (@lem3081292)). Qed.
Lemma lem3081295 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081296 : term812 = term807.
Proof. exact (MK_COMB (@lem3081295) (@lem3081294)). Qed.
Lemma lem3081297 : term804 = term807.
Proof. exact (TRANS (@lem3081289) (@lem3081296)). Qed.
Lemma lem3081298 : term811 = term807.
Proof. exact (TRANS (@lem3081288) (@lem3081297)). Qed.
Lemma lem3081299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3081300 : term819 = term820.
Proof. exact (MK_COMB (@lem3081299) (@lem3081298)). Qed.
Lemma lem3081301 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3081302 : term821 = term822.
Proof. exact (MK_COMB (@lem3081300) (@lem3081301)). Qed.
Lemma lem3081304 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081305 : term822 = term823.
Proof. exact (@lem3081304 term816 term75). Qed.
Lemma lem3081306 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3081307 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3081308 : term825 = term816.
Proof. exact (EQ_MP (@lem3081307) (@lem3081306)). Qed.
Lemma lem3081309 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081310 : term826 = term818.
Proof. exact (MK_COMB (@lem3081309) (@lem3081308)). Qed.
Lemma lem3081311 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081312 : term823 = term807.
Proof. exact (MK_COMB (@lem3081311) (@lem3081310)). Qed.
Lemma lem3081313 : term822 = term807.
Proof. exact (TRANS (@lem3081305) (@lem3081312)). Qed.
Lemma lem3081314 : term821 = term807.
Proof. exact (TRANS (@lem3081302) (@lem3081313)). Qed.
Lemma lem3081316 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081317 : term104 = term105.
Proof. exact (@lem3081316 term75 term75). Qed.
Lemma lem3081318 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081319 : term107 = term75.
Proof. exact (EQ_MP (@lem3081318) (@lem940073)). Qed.
Lemma lem3081320 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081321 : term105 = term74.
Proof. exact (MK_COMB (@lem3081320) (@lem3081319)). Qed.
Lemma lem3081322 : term104 = term74.
Proof. exact (TRANS (@lem3081317) (@lem3081321)). Qed.
Lemma lem3081323 : term820 = term820.
Proof. exact (eq_refl term820). Qed.
Lemma lem3081324 : term827 = term822.
Proof. exact (MK_COMB (@lem3081323) (@lem3081322)). Qed.
Lemma lem3081326 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081327 : term822 = term823.
Proof. exact (@lem3081326 term816 term75). Qed.
Lemma lem3081328 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3081329 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3081330 : term825 = term816.
Proof. exact (EQ_MP (@lem3081329) (@lem3081328)). Qed.
Lemma lem3081331 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081332 : term826 = term818.
Proof. exact (MK_COMB (@lem3081331) (@lem3081330)). Qed.
Lemma lem3081333 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081334 : term823 = term807.
Proof. exact (MK_COMB (@lem3081333) (@lem3081332)). Qed.
Lemma lem3081335 : term822 = term807.
Proof. exact (TRANS (@lem3081327) (@lem3081334)). Qed.
Lemma lem3081336 : term827 = term807.
Proof. exact (TRANS (@lem3081324) (@lem3081335)). Qed.
Lemma lem3081337 : term807 = term827.
Proof. exact (SYM (@lem3081336)). Qed.
Lemma lem3081338 : term821 = term827.
Proof. exact (TRANS (@lem3081314) (@lem3081337)). Qed.
Lemma lem3081339 : term805 = term828.
Proof. exact (@lem3081265 (@lem3081338)). Qed.
Lemma lem3081340 : term804 = term828.
Proof. exact (TRANS (@lem3081231) (@lem3081339)). Qed.
Lemma lem3081342 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3081343 : term828 = term807.
Proof. exact (@lem3081342 term807). Qed.
Lemma lem3081344 : term804 = term807.
Proof. exact (TRANS (@lem3081340) (@lem3081343)). Qed.
Lemma lem3081345 (_32061 : int) : (term803 _32061) = term829.
Proof. exact (MK_COMB (@lem3081222 _32061) (@lem3081344)). Qed.
Lemma lem3081346 (_32061 : int) : (term802 _32061) = term829.
Proof. exact (TRANS (@lem3081114 _32061) (@lem3081345 _32061)). Qed.
Lemma lem3081347 : term829 = term807.
Proof. exact (@lem1982721 term807). Qed.
Lemma lem3081348 (_32061 : int) : (term802 _32061) = term807.
Proof. exact (TRANS (@lem3081346 _32061) (@lem3081347)). Qed.
Lemma lem3081349 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3081350 (_32061 : int) : (term830 _32061) = term831.
Proof. exact (MK_COMB (@lem3081349) (@lem3081348 _32061)). Qed.
Lemma lem3081351 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3081352 (_32061 : int) : (term801 _32061) = term832.
Proof. exact (MK_COMB (@lem3081350 _32061) (@lem3081351)). Qed.
Lemma lem3081353 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : term832.
Proof. exact (EQ_MP (@lem3081352 _32061) (@lem3081113 _32061 _32062 h1)). Qed.
Lemma lem3081355 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3081356 : term832 = term833.
Proof. exact (@lem3081355 term61 term807). Qed.
Lemma lem3081358 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3081359 : term807 = term828.
Proof. exact (@lem3081358 term816). Qed.
Lemma lem3081361 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081362 : term61 = term92.
Proof. exact (@lem3081361 (NUMERAL 0)). Qed.
Lemma lem3081363 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3081364 : term63 = term210.
Proof. exact (MK_COMB (@lem3081363) (@lem3081362)). Qed.
Lemma lem3081365 : term833 = term834.
Proof. exact (MK_COMB (@lem3081364) (@lem3081359)). Qed.
Lemma lem3081366 : term835.
Proof. exact (@lem1980026 term61 term74 term807 term74). Qed.
Lemma lem3081368 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081369 : term150 = term156.
Proof. exact (@lem3081368 (NUMERAL 0) term75). Qed.
Lemma lem3081370 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081371 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081372 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081371 h1) (fun h1 : term156 = True => @lem3081370)). Qed.
Lemma lem3081373 : term156 = True.
Proof. exact (EQ_MP (@lem3081372) (@lem3081370)). Qed.
Lemma lem3081374 : term150 = True.
Proof. exact (TRANS (@lem3081369) (@lem3081373)). Qed.
Lemma lem3081375 : True = term150.
Proof. exact (SYM (@lem3081374)). Qed.
Lemma lem3081376 : term150.
Proof. exact (EQ_MP (@lem3081375) (@lem0)). Qed.
Lemma lem3081377 : term836.
Proof. exact (@lem3081366 (@lem3081376)). Qed.
Lemma lem3081379 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081380 : term150 = term156.
Proof. exact (@lem3081379 (NUMERAL 0) term75). Qed.
Lemma lem3081381 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081382 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081383 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081382 h1) (fun h1 : term156 = True => @lem3081381)). Qed.
Lemma lem3081384 : term156 = True.
Proof. exact (EQ_MP (@lem3081383) (@lem3081381)). Qed.
Lemma lem3081385 : term150 = True.
Proof. exact (TRANS (@lem3081380) (@lem3081384)). Qed.
Lemma lem3081386 : True = term150.
Proof. exact (SYM (@lem3081385)). Qed.
Lemma lem3081387 : term150.
Proof. exact (EQ_MP (@lem3081386) (@lem0)). Qed.
Lemma lem3081388 : term834 = term837.
Proof. exact (@lem3081377 (@lem3081387)). Qed.
Lemma lem3081390 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081391 : term822 = term823.
Proof. exact (@lem3081390 term816 term75). Qed.
Lemma lem3081392 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3081393 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3081394 : term825 = term816.
Proof. exact (EQ_MP (@lem3081393) (@lem3081392)). Qed.
Lemma lem3081395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081396 : term826 = term818.
Proof. exact (MK_COMB (@lem3081395) (@lem3081394)). Qed.
Lemma lem3081397 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081398 : term823 = term807.
Proof. exact (MK_COMB (@lem3081397) (@lem3081396)). Qed.
Lemma lem3081399 : term822 = term807.
Proof. exact (TRANS (@lem3081391) (@lem3081398)). Qed.
Lemma lem3081401 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081402 : term161 = term61.
Proof. exact (@lem3081401 term75). Qed.
Lemma lem3081403 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3081404 : term215 = term63.
Proof. exact (MK_COMB (@lem3081403) (@lem3081402)). Qed.
Lemma lem3081405 : term837 = term833.
Proof. exact (MK_COMB (@lem3081404) (@lem3081399)). Qed.
Lemma lem3081407 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3081408 : term833 = term838.
Proof. exact (@lem3081407 (NUMERAL 0) term816). Qed.
Lemma lem3081409 : term839 = term814.
Proof. exact (@lem912803). Qed.
Lemma lem3081410 (h1 : term839 = term814) : (term816 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term814 h1). Qed.
Lemma lem3081411 : (term839 = term814) = ((term816 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term839 = term814 => @lem3081410 h1) (fun h1 : (term816 = (NUMERAL 0)) = False => @lem3081409)). Qed.
Lemma lem3081412 : (term816 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3081411) (@lem3081409)). Qed.
Lemma lem3081413 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3081414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3081415 : term219 = (and True).
Proof. exact (MK_COMB (@lem3081414) (@lem3081413)). Qed.
Lemma lem3081416 : term838 = (True /\ False).
Proof. exact (MK_COMB (@lem3081415) (@lem3081412)). Qed.
Lemma lem3081418 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3081419 : term838 = False.
Proof. exact (TRANS (@lem3081416) (@lem3081418)). Qed.
Lemma lem3081420 : term833 = False.
Proof. exact (TRANS (@lem3081408) (@lem3081419)). Qed.
Lemma lem3081421 : term837 = False.
Proof. exact (TRANS (@lem3081405) (@lem3081420)). Qed.
Lemma lem3081422 : term834 = False.
Proof. exact (TRANS (@lem3081388) (@lem3081421)). Qed.
Lemma lem3081423 : term833 = False.
Proof. exact (TRANS (@lem3081365) (@lem3081422)). Qed.
Lemma lem3081424 : term832 = False.
Proof. exact (TRANS (@lem3081356) (@lem3081423)). Qed.
Lemma lem3081425 (_32061 : int) (_32062 : int) (h1 : term843 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3081424) (@lem3081353 _32061 _32062 h1)). Qed.
Lemma lem3081426 (_32061 : int) (_32062 : int) (h1 : term754 _32061 _32062) : False.
Proof. exact (or_elim (@lem3080595 _32061 _32062 h1) (fun h0 : term842 _32061 _32062 => @lem3080949 _32061 _32062 h0) (fun h0 : term843 _32061 _32062 => @lem3081425 _32061 _32062 h0)). Qed.
Lemma lem3081427 (_32061 : int) (_32062 : int) (h1 : term750 _32061 _32062) : term750 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3081428 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term844 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3081429 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term751 _32061 _32062.
Proof. exact (proj2 (@lem3081428 _32061 _32062 h1)). Qed.
Lemma lem3081431 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term720 _32061 _32062.
Proof. exact (proj2 (@lem3081429 _32061 _32062 h1)). Qed.
Lemma lem3081433 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term690 _32061 _32062.
Proof. exact (proj2 (@lem3081431 _32061 _32062 h1)). Qed.
Lemma lem3081434 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term693 _32061 _32062.
Proof. exact (proj1 (@lem3081431 _32061 _32062 h1)). Qed.
Lemma lem3081436 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term634 _32061.
Proof. exact (proj1 (@lem3081434 _32061 _32062 h1)). Qed.
Lemma lem3081438 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term643 _32061.
Proof. exact (proj1 (@lem3081433 _32061 _32062 h1)). Qed.
Lemma lem3081440 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3081441 : term149 = term150.
Proof. exact (@lem3081440 term61 term74). Qed.
Lemma lem3081443 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081444 : term74 = term121.
Proof. exact (@lem3081443 term75). Qed.
Lemma lem3081446 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081447 : term61 = term92.
Proof. exact (@lem3081446 (NUMERAL 0)). Qed.
Lemma lem3081448 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081449 : term151 = term152.
Proof. exact (MK_COMB (@lem3081448) (@lem3081447)). Qed.
Lemma lem3081450 : term150 = term153.
Proof. exact (MK_COMB (@lem3081449) (@lem3081444)). Qed.
Lemma lem3081451 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3081453 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081454 : term150 = term156.
Proof. exact (@lem3081453 (NUMERAL 0) term75). Qed.
Lemma lem3081455 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081456 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081457 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081456 h1) (fun h1 : term156 = True => @lem3081455)). Qed.
Lemma lem3081458 : term156 = True.
Proof. exact (EQ_MP (@lem3081457) (@lem3081455)). Qed.
Lemma lem3081459 : term150 = True.
Proof. exact (TRANS (@lem3081454) (@lem3081458)). Qed.
Lemma lem3081460 : True = term150.
Proof. exact (SYM (@lem3081459)). Qed.
Lemma lem3081461 : term150.
Proof. exact (EQ_MP (@lem3081460) (@lem0)). Qed.
Lemma lem3081462 : term158.
Proof. exact (@lem3081451 (@lem3081461)). Qed.
Lemma lem3081464 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081465 : term150 = term156.
Proof. exact (@lem3081464 (NUMERAL 0) term75). Qed.
Lemma lem3081466 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081467 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081468 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081467 h1) (fun h1 : term156 = True => @lem3081466)). Qed.
Lemma lem3081469 : term156 = True.
Proof. exact (EQ_MP (@lem3081468) (@lem3081466)). Qed.
Lemma lem3081470 : term150 = True.
Proof. exact (TRANS (@lem3081465) (@lem3081469)). Qed.
Lemma lem3081471 : True = term150.
Proof. exact (SYM (@lem3081470)). Qed.
Lemma lem3081472 : term150.
Proof. exact (EQ_MP (@lem3081471) (@lem0)). Qed.
Lemma lem3081473 : term153 = term159.
Proof. exact (@lem3081462 (@lem3081472)). Qed.
Lemma lem3081475 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081476 : term104 = term105.
Proof. exact (@lem3081475 term75 term75). Qed.
Lemma lem3081477 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081478 : term107 = term75.
Proof. exact (EQ_MP (@lem3081477) (@lem940073)). Qed.
Lemma lem3081479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081480 : term105 = term74.
Proof. exact (MK_COMB (@lem3081479) (@lem3081478)). Qed.
Lemma lem3081481 : term104 = term74.
Proof. exact (TRANS (@lem3081476) (@lem3081480)). Qed.
Lemma lem3081483 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081484 : term161 = term61.
Proof. exact (@lem3081483 term75). Qed.
Lemma lem3081485 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081486 : term162 = term151.
Proof. exact (MK_COMB (@lem3081485) (@lem3081484)). Qed.
Lemma lem3081487 : term159 = term150.
Proof. exact (MK_COMB (@lem3081486) (@lem3081481)). Qed.
Lemma lem3081489 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081490 : term150 = term156.
Proof. exact (@lem3081489 (NUMERAL 0) term75). Qed.
Lemma lem3081491 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081492 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081493 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081492 h1) (fun h1 : term156 = True => @lem3081491)). Qed.
Lemma lem3081494 : term156 = True.
Proof. exact (EQ_MP (@lem3081493) (@lem3081491)). Qed.
Lemma lem3081495 : term150 = True.
Proof. exact (TRANS (@lem3081490) (@lem3081494)). Qed.
Lemma lem3081496 : term159 = True.
Proof. exact (TRANS (@lem3081487) (@lem3081495)). Qed.
Lemma lem3081497 : term153 = True.
Proof. exact (TRANS (@lem3081473) (@lem3081496)). Qed.
Lemma lem3081498 : term150 = True.
Proof. exact (TRANS (@lem3081450) (@lem3081497)). Qed.
Lemma lem3081499 : term149 = True.
Proof. exact (TRANS (@lem3081441) (@lem3081498)). Qed.
Lemma lem3081500 : True = term149.
Proof. exact (SYM (@lem3081499)). Qed.
Lemma lem3081501 : term149.
Proof. exact (EQ_MP (@lem3081500) (@lem0)). Qed.
Lemma lem3081502 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term794 _32061.
Proof. exact (conj (@lem3081501) (@lem3081438 _32061 _32062 h1)). Qed.
Lemma lem3081504 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3081505 (_32061 : int) : term795 _32061.
Proof. exact (@lem3081504 term74 (term640 _32061)). Qed.
Lemma lem3081506 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term796 _32061.
Proof. exact (@lem3081505 _32061 (@lem3081502 _32061 _32062 h1)). Qed.
Lemma lem3081507 (_32061 : int) : (term797 _32061) = (term640 _32061).
Proof. exact (@lem1982733 (term640 _32061)). Qed.
Lemma lem3081508 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3081509 (_32061 : int) : (term798 _32061) = (term642 _32061).
Proof. exact (MK_COMB (@lem3081508) (@lem3081507 _32061)). Qed.
Lemma lem3081510 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3081511 (_32061 : int) : (term796 _32061) = (term643 _32061).
Proof. exact (MK_COMB (@lem3081509 _32061) (@lem3081510)). Qed.
Lemma lem3081512 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term643 _32061.
Proof. exact (EQ_MP (@lem3081511 _32061) (@lem3081506 _32061 _32062 h1)). Qed.
Lemma lem3081514 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3081515 : term149 = term150.
Proof. exact (@lem3081514 term61 term74). Qed.
Lemma lem3081517 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081518 : term74 = term121.
Proof. exact (@lem3081517 term75). Qed.
Lemma lem3081520 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081521 : term61 = term92.
Proof. exact (@lem3081520 (NUMERAL 0)). Qed.
Lemma lem3081522 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081523 : term151 = term152.
Proof. exact (MK_COMB (@lem3081522) (@lem3081521)). Qed.
Lemma lem3081524 : term150 = term153.
Proof. exact (MK_COMB (@lem3081523) (@lem3081518)). Qed.
Lemma lem3081525 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3081527 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081528 : term150 = term156.
Proof. exact (@lem3081527 (NUMERAL 0) term75). Qed.
Lemma lem3081529 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081530 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081531 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081530 h1) (fun h1 : term156 = True => @lem3081529)). Qed.
Lemma lem3081532 : term156 = True.
Proof. exact (EQ_MP (@lem3081531) (@lem3081529)). Qed.
Lemma lem3081533 : term150 = True.
Proof. exact (TRANS (@lem3081528) (@lem3081532)). Qed.
Lemma lem3081534 : True = term150.
Proof. exact (SYM (@lem3081533)). Qed.
Lemma lem3081535 : term150.
Proof. exact (EQ_MP (@lem3081534) (@lem0)). Qed.
Lemma lem3081536 : term158.
Proof. exact (@lem3081525 (@lem3081535)). Qed.
Lemma lem3081538 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081539 : term150 = term156.
Proof. exact (@lem3081538 (NUMERAL 0) term75). Qed.
Lemma lem3081540 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081541 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081542 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081541 h1) (fun h1 : term156 = True => @lem3081540)). Qed.
Lemma lem3081543 : term156 = True.
Proof. exact (EQ_MP (@lem3081542) (@lem3081540)). Qed.
Lemma lem3081544 : term150 = True.
Proof. exact (TRANS (@lem3081539) (@lem3081543)). Qed.
Lemma lem3081545 : True = term150.
Proof. exact (SYM (@lem3081544)). Qed.
Lemma lem3081546 : term150.
Proof. exact (EQ_MP (@lem3081545) (@lem0)). Qed.
Lemma lem3081547 : term153 = term159.
Proof. exact (@lem3081536 (@lem3081546)). Qed.
Lemma lem3081549 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081550 : term104 = term105.
Proof. exact (@lem3081549 term75 term75). Qed.
Lemma lem3081551 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081552 : term107 = term75.
Proof. exact (EQ_MP (@lem3081551) (@lem940073)). Qed.
Lemma lem3081553 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081554 : term105 = term74.
Proof. exact (MK_COMB (@lem3081553) (@lem3081552)). Qed.
Lemma lem3081555 : term104 = term74.
Proof. exact (TRANS (@lem3081550) (@lem3081554)). Qed.
Lemma lem3081557 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081558 : term161 = term61.
Proof. exact (@lem3081557 term75). Qed.
Lemma lem3081559 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081560 : term162 = term151.
Proof. exact (MK_COMB (@lem3081559) (@lem3081558)). Qed.
Lemma lem3081561 : term159 = term150.
Proof. exact (MK_COMB (@lem3081560) (@lem3081555)). Qed.
Lemma lem3081563 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081564 : term150 = term156.
Proof. exact (@lem3081563 (NUMERAL 0) term75). Qed.
Lemma lem3081565 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081566 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081567 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081566 h1) (fun h1 : term156 = True => @lem3081565)). Qed.
Lemma lem3081568 : term156 = True.
Proof. exact (EQ_MP (@lem3081567) (@lem3081565)). Qed.
Lemma lem3081569 : term150 = True.
Proof. exact (TRANS (@lem3081564) (@lem3081568)). Qed.
Lemma lem3081570 : term159 = True.
Proof. exact (TRANS (@lem3081561) (@lem3081569)). Qed.
Lemma lem3081571 : term153 = True.
Proof. exact (TRANS (@lem3081547) (@lem3081570)). Qed.
Lemma lem3081572 : term150 = True.
Proof. exact (TRANS (@lem3081524) (@lem3081571)). Qed.
Lemma lem3081573 : term149 = True.
Proof. exact (TRANS (@lem3081515) (@lem3081572)). Qed.
Lemma lem3081574 : True = term149.
Proof. exact (SYM (@lem3081573)). Qed.
Lemma lem3081575 : term149.
Proof. exact (EQ_MP (@lem3081574) (@lem0)). Qed.
Lemma lem3081576 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term782 _32061.
Proof. exact (conj (@lem3081575) (@lem3081436 _32061 _32062 h1)). Qed.
Lemma lem3081578 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3081579 (_32061 : int) : term783 _32061.
Proof. exact (@lem3081578 term74 (term131 _32061)). Qed.
Lemma lem3081580 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term784 _32061.
Proof. exact (@lem3081579 _32061 (@lem3081576 _32061 _32062 h1)). Qed.
Lemma lem3081581 (_32061 : int) : (term785 _32061) = (term131 _32061).
Proof. exact (@lem1982733 (term131 _32061)). Qed.
Lemma lem3081582 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3081583 (_32061 : int) : (term786 _32061) = (term633 _32061).
Proof. exact (MK_COMB (@lem3081582) (@lem3081581 _32061)). Qed.
Lemma lem3081584 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3081585 (_32061 : int) : (term784 _32061) = (term634 _32061).
Proof. exact (MK_COMB (@lem3081583 _32061) (@lem3081584)). Qed.
Lemma lem3081586 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term634 _32061.
Proof. exact (EQ_MP (@lem3081585 _32061) (@lem3081580 _32061 _32062 h1)). Qed.
Lemma lem3081587 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term799 _32061.
Proof. exact (conj (@lem3081586 _32061 _32062 h1) (@lem3081512 _32061 _32062 h1)). Qed.
Lemma lem3081589 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3081590 (_32061 : int) : term800 _32061.
Proof. exact (@lem3081589 (term131 _32061) (term640 _32061)). Qed.
Lemma lem3081591 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term801 _32061.
Proof. exact (@lem3081590 _32061 (@lem3081587 _32061 _32062 h1)). Qed.
Lemma lem3081592 (_32061 : int) : (term802 _32061) = (term803 _32061).
Proof. exact (@lem1982753 (term140 _32061) (real_of_int _32061) term95 term95). Qed.
Lemma lem3081593 (_32061 : int) : (term180 _32061) = (term181 _32061).
Proof. exact (@lem1982713 term95 (real_of_int _32061)). Qed.
Lemma lem3081595 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081596 : term74 = term121.
Proof. exact (@lem3081595 term75). Qed.
Lemma lem3081598 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3081599 : term95 = term96.
Proof. exact (@lem3081598 term75). Qed.
Lemma lem3081600 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081601 : term182 = term183.
Proof. exact (MK_COMB (@lem3081600) (@lem3081599)). Qed.
Lemma lem3081602 : term184 = term185.
Proof. exact (MK_COMB (@lem3081601) (@lem3081596)). Qed.
Lemma lem3081603 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3081605 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081606 : term150 = term156.
Proof. exact (@lem3081605 (NUMERAL 0) term75). Qed.
Lemma lem3081607 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081608 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081609 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081608 h1) (fun h1 : term156 = True => @lem3081607)). Qed.
Lemma lem3081610 : term156 = True.
Proof. exact (EQ_MP (@lem3081609) (@lem3081607)). Qed.
Lemma lem3081611 : term150 = True.
Proof. exact (TRANS (@lem3081606) (@lem3081610)). Qed.
Lemma lem3081612 : True = term150.
Proof. exact (SYM (@lem3081611)). Qed.
Lemma lem3081613 : term150.
Proof. exact (EQ_MP (@lem3081612) (@lem0)). Qed.
Lemma lem3081614 : term187.
Proof. exact (@lem3081603 (@lem3081613)). Qed.
Lemma lem3081616 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081617 : term150 = term156.
Proof. exact (@lem3081616 (NUMERAL 0) term75). Qed.
Lemma lem3081618 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081619 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081620 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081619 h1) (fun h1 : term156 = True => @lem3081618)). Qed.
Lemma lem3081621 : term156 = True.
Proof. exact (EQ_MP (@lem3081620) (@lem3081618)). Qed.
Lemma lem3081622 : term150 = True.
Proof. exact (TRANS (@lem3081617) (@lem3081621)). Qed.
Lemma lem3081623 : True = term150.
Proof. exact (SYM (@lem3081622)). Qed.
Lemma lem3081624 : term150.
Proof. exact (EQ_MP (@lem3081623) (@lem0)). Qed.
Lemma lem3081625 : term188.
Proof. exact (@lem3081614 (@lem3081624)). Qed.
Lemma lem3081627 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081628 : term150 = term156.
Proof. exact (@lem3081627 (NUMERAL 0) term75). Qed.
Lemma lem3081629 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081630 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081631 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081630 h1) (fun h1 : term156 = True => @lem3081629)). Qed.
Lemma lem3081632 : term156 = True.
Proof. exact (EQ_MP (@lem3081631) (@lem3081629)). Qed.
Lemma lem3081633 : term150 = True.
Proof. exact (TRANS (@lem3081628) (@lem3081632)). Qed.
Lemma lem3081634 : True = term150.
Proof. exact (SYM (@lem3081633)). Qed.
Lemma lem3081635 : term150.
Proof. exact (EQ_MP (@lem3081634) (@lem0)). Qed.
Lemma lem3081636 : term189.
Proof. exact (@lem3081625 (@lem3081635)). Qed.
Lemma lem3081638 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081639 : term104 = term105.
Proof. exact (@lem3081638 term75 term75). Qed.
Lemma lem3081640 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081641 : term107 = term75.
Proof. exact (EQ_MP (@lem3081640) (@lem940073)). Qed.
Lemma lem3081642 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081643 : term105 = term74.
Proof. exact (MK_COMB (@lem3081642) (@lem3081641)). Qed.
Lemma lem3081644 : term104 = term74.
Proof. exact (TRANS (@lem3081639) (@lem3081643)). Qed.
Lemma lem3081646 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081647 : term122 = term127.
Proof. exact (@lem3081646 term75 term75). Qed.
Lemma lem3081648 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081649 : term107 = term75.
Proof. exact (EQ_MP (@lem3081648) (@lem940073)). Qed.
Lemma lem3081650 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081651 : term105 = term74.
Proof. exact (MK_COMB (@lem3081650) (@lem3081649)). Qed.
Lemma lem3081652 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081653 : term127 = term95.
Proof. exact (MK_COMB (@lem3081652) (@lem3081651)). Qed.
Lemma lem3081654 : term122 = term95.
Proof. exact (TRANS (@lem3081647) (@lem3081653)). Qed.
Lemma lem3081655 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081656 : term190 = term182.
Proof. exact (MK_COMB (@lem3081655) (@lem3081654)). Qed.
Lemma lem3081657 : term191 = term184.
Proof. exact (MK_COMB (@lem3081656) (@lem3081644)). Qed.
Lemma lem3081659 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3081660 : term184 = term61.
Proof. exact (@lem3081659 term75). Qed.
Lemma lem3081661 : term191 = term61.
Proof. exact (TRANS (@lem3081657) (@lem3081660)). Qed.
Lemma lem3081662 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3081663 : term193 = term194.
Proof. exact (MK_COMB (@lem3081662) (@lem3081661)). Qed.
Lemma lem3081664 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3081665 : term195 = term161.
Proof. exact (MK_COMB (@lem3081663) (@lem3081664)). Qed.
Lemma lem3081667 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081668 : term161 = term61.
Proof. exact (@lem3081667 term75). Qed.
Lemma lem3081669 : term195 = term61.
Proof. exact (TRANS (@lem3081665) (@lem3081668)). Qed.
Lemma lem3081671 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081672 : term104 = term105.
Proof. exact (@lem3081671 term75 term75). Qed.
Lemma lem3081673 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081674 : term107 = term75.
Proof. exact (EQ_MP (@lem3081673) (@lem940073)). Qed.
Lemma lem3081675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081676 : term105 = term74.
Proof. exact (MK_COMB (@lem3081675) (@lem3081674)). Qed.
Lemma lem3081677 : term104 = term74.
Proof. exact (TRANS (@lem3081672) (@lem3081676)). Qed.
Lemma lem3081678 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3081679 : term196 = term161.
Proof. exact (MK_COMB (@lem3081678) (@lem3081677)). Qed.
Lemma lem3081681 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081682 : term161 = term61.
Proof. exact (@lem3081681 term75). Qed.
Lemma lem3081683 : term196 = term61.
Proof. exact (TRANS (@lem3081679) (@lem3081682)). Qed.
Lemma lem3081684 : term61 = term196.
Proof. exact (SYM (@lem3081683)). Qed.
Lemma lem3081685 : term195 = term196.
Proof. exact (TRANS (@lem3081669) (@lem3081684)). Qed.
Lemma lem3081686 : term185 = term92.
Proof. exact (@lem3081636 (@lem3081685)). Qed.
Lemma lem3081687 : term184 = term92.
Proof. exact (TRANS (@lem3081602) (@lem3081686)). Qed.
Lemma lem3081689 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3081690 : term92 = term61.
Proof. exact (@lem3081689 term61). Qed.
Lemma lem3081691 : term184 = term61.
Proof. exact (TRANS (@lem3081687) (@lem3081690)). Qed.
Lemma lem3081692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3081693 : term197 = term194.
Proof. exact (MK_COMB (@lem3081692) (@lem3081691)). Qed.
Lemma lem3081694 (_32061 : int) : (real_of_int _32061) = (real_of_int _32061).
Proof. exact (eq_refl (real_of_int _32061)). Qed.
Lemma lem3081695 (_32061 : int) : (term181 _32061) = (term198 _32061).
Proof. exact (MK_COMB (@lem3081693) (@lem3081694 _32061)). Qed.
Lemma lem3081696 (_32061 : int) : (term180 _32061) = (term198 _32061).
Proof. exact (TRANS (@lem3081593 _32061) (@lem3081695 _32061)). Qed.
Lemma lem3081697 (_32061 : int) : (term198 _32061) = term61.
Proof. exact (@lem1982719 (real_of_int _32061)). Qed.
Lemma lem3081698 (_32061 : int) : (term180 _32061) = term61.
Proof. exact (TRANS (@lem3081696 _32061) (@lem3081697 _32061)). Qed.
Lemma lem3081699 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081700 (_32061 : int) : (term199 _32061) = term200.
Proof. exact (MK_COMB (@lem3081699) (@lem3081698 _32061)). Qed.
Lemma lem3081702 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3081703 : term95 = term96.
Proof. exact (@lem3081702 term75). Qed.
Lemma lem3081705 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3081706 : term95 = term96.
Proof. exact (@lem3081705 term75). Qed.
Lemma lem3081707 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081708 : term182 = term183.
Proof. exact (MK_COMB (@lem3081707) (@lem3081706)). Qed.
Lemma lem3081709 : term804 = term805.
Proof. exact (MK_COMB (@lem3081708) (@lem3081703)). Qed.
Lemma lem3081710 : term806.
Proof. exact (@lem1981473 term95 term74 term95 term74 term807 term74). Qed.
Lemma lem3081712 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081713 : term150 = term156.
Proof. exact (@lem3081712 (NUMERAL 0) term75). Qed.
Lemma lem3081714 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081715 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081716 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081715 h1) (fun h1 : term156 = True => @lem3081714)). Qed.
Lemma lem3081717 : term156 = True.
Proof. exact (EQ_MP (@lem3081716) (@lem3081714)). Qed.
Lemma lem3081718 : term150 = True.
Proof. exact (TRANS (@lem3081713) (@lem3081717)). Qed.
Lemma lem3081719 : True = term150.
Proof. exact (SYM (@lem3081718)). Qed.
Lemma lem3081720 : term150.
Proof. exact (EQ_MP (@lem3081719) (@lem0)). Qed.
Lemma lem3081721 : term808.
Proof. exact (@lem3081710 (@lem3081720)). Qed.
Lemma lem3081723 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081724 : term150 = term156.
Proof. exact (@lem3081723 (NUMERAL 0) term75). Qed.
Lemma lem3081725 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081726 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081727 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081726 h1) (fun h1 : term156 = True => @lem3081725)). Qed.
Lemma lem3081728 : term156 = True.
Proof. exact (EQ_MP (@lem3081727) (@lem3081725)). Qed.
Lemma lem3081729 : term150 = True.
Proof. exact (TRANS (@lem3081724) (@lem3081728)). Qed.
Lemma lem3081730 : True = term150.
Proof. exact (SYM (@lem3081729)). Qed.
Lemma lem3081731 : term150.
Proof. exact (EQ_MP (@lem3081730) (@lem0)). Qed.
Lemma lem3081732 : term809.
Proof. exact (@lem3081721 (@lem3081731)). Qed.
Lemma lem3081734 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081735 : term150 = term156.
Proof. exact (@lem3081734 (NUMERAL 0) term75). Qed.
Lemma lem3081736 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081737 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081738 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081737 h1) (fun h1 : term156 = True => @lem3081736)). Qed.
Lemma lem3081739 : term156 = True.
Proof. exact (EQ_MP (@lem3081738) (@lem3081736)). Qed.
Lemma lem3081740 : term150 = True.
Proof. exact (TRANS (@lem3081735) (@lem3081739)). Qed.
Lemma lem3081741 : True = term150.
Proof. exact (SYM (@lem3081740)). Qed.
Lemma lem3081742 : term150.
Proof. exact (EQ_MP (@lem3081741) (@lem0)). Qed.
Lemma lem3081743 : term810.
Proof. exact (@lem3081732 (@lem3081742)). Qed.
Lemma lem3081745 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081746 : term122 = term127.
Proof. exact (@lem3081745 term75 term75). Qed.
Lemma lem3081747 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081748 : term107 = term75.
Proof. exact (EQ_MP (@lem3081747) (@lem940073)). Qed.
Lemma lem3081749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081750 : term105 = term74.
Proof. exact (MK_COMB (@lem3081749) (@lem3081748)). Qed.
Lemma lem3081751 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081752 : term127 = term95.
Proof. exact (MK_COMB (@lem3081751) (@lem3081750)). Qed.
Lemma lem3081753 : term122 = term95.
Proof. exact (TRANS (@lem3081746) (@lem3081752)). Qed.
Lemma lem3081755 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081756 : term122 = term127.
Proof. exact (@lem3081755 term75 term75). Qed.
Lemma lem3081757 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081758 : term107 = term75.
Proof. exact (EQ_MP (@lem3081757) (@lem940073)). Qed.
Lemma lem3081759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081760 : term105 = term74.
Proof. exact (MK_COMB (@lem3081759) (@lem3081758)). Qed.
Lemma lem3081761 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081762 : term127 = term95.
Proof. exact (MK_COMB (@lem3081761) (@lem3081760)). Qed.
Lemma lem3081763 : term122 = term95.
Proof. exact (TRANS (@lem3081756) (@lem3081762)). Qed.
Lemma lem3081764 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3081765 : term190 = term182.
Proof. exact (MK_COMB (@lem3081764) (@lem3081763)). Qed.
Lemma lem3081766 : term811 = term804.
Proof. exact (MK_COMB (@lem3081765) (@lem3081753)). Qed.
Lemma lem3081767 : term804 = term812.
Proof. exact (@lem1367763 term75 term75). Qed.
Lemma lem3081768 : term813 = term814.
Proof. exact (@lem706885). Qed.
Lemma lem3081769 : (term813 = term814) = (term815 = term816).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term814). Qed.
Lemma lem3081770 : term815 = term816.
Proof. exact (EQ_MP (@lem3081769) (@lem3081768)). Qed.
Lemma lem3081771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081772 : term817 = term818.
Proof. exact (MK_COMB (@lem3081771) (@lem3081770)). Qed.
Lemma lem3081773 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081774 : term812 = term807.
Proof. exact (MK_COMB (@lem3081773) (@lem3081772)). Qed.
Lemma lem3081775 : term804 = term807.
Proof. exact (TRANS (@lem3081767) (@lem3081774)). Qed.
Lemma lem3081776 : term811 = term807.
Proof. exact (TRANS (@lem3081766) (@lem3081775)). Qed.
Lemma lem3081777 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3081778 : term819 = term820.
Proof. exact (MK_COMB (@lem3081777) (@lem3081776)). Qed.
Lemma lem3081779 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3081780 : term821 = term822.
Proof. exact (MK_COMB (@lem3081778) (@lem3081779)). Qed.
Lemma lem3081782 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081783 : term822 = term823.
Proof. exact (@lem3081782 term816 term75). Qed.
Lemma lem3081784 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3081785 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3081786 : term825 = term816.
Proof. exact (EQ_MP (@lem3081785) (@lem3081784)). Qed.
Lemma lem3081787 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081788 : term826 = term818.
Proof. exact (MK_COMB (@lem3081787) (@lem3081786)). Qed.
Lemma lem3081789 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081790 : term823 = term807.
Proof. exact (MK_COMB (@lem3081789) (@lem3081788)). Qed.
Lemma lem3081791 : term822 = term807.
Proof. exact (TRANS (@lem3081783) (@lem3081790)). Qed.
Lemma lem3081792 : term821 = term807.
Proof. exact (TRANS (@lem3081780) (@lem3081791)). Qed.
Lemma lem3081794 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081795 : term104 = term105.
Proof. exact (@lem3081794 term75 term75). Qed.
Lemma lem3081796 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081797 : term107 = term75.
Proof. exact (EQ_MP (@lem3081796) (@lem940073)). Qed.
Lemma lem3081798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081799 : term105 = term74.
Proof. exact (MK_COMB (@lem3081798) (@lem3081797)). Qed.
Lemma lem3081800 : term104 = term74.
Proof. exact (TRANS (@lem3081795) (@lem3081799)). Qed.
Lemma lem3081801 : term820 = term820.
Proof. exact (eq_refl term820). Qed.
Lemma lem3081802 : term827 = term822.
Proof. exact (MK_COMB (@lem3081801) (@lem3081800)). Qed.
Lemma lem3081804 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081805 : term822 = term823.
Proof. exact (@lem3081804 term816 term75). Qed.
Lemma lem3081806 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3081807 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3081808 : term825 = term816.
Proof. exact (EQ_MP (@lem3081807) (@lem3081806)). Qed.
Lemma lem3081809 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081810 : term826 = term818.
Proof. exact (MK_COMB (@lem3081809) (@lem3081808)). Qed.
Lemma lem3081811 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081812 : term823 = term807.
Proof. exact (MK_COMB (@lem3081811) (@lem3081810)). Qed.
Lemma lem3081813 : term822 = term807.
Proof. exact (TRANS (@lem3081805) (@lem3081812)). Qed.
Lemma lem3081814 : term827 = term807.
Proof. exact (TRANS (@lem3081802) (@lem3081813)). Qed.
Lemma lem3081815 : term807 = term827.
Proof. exact (SYM (@lem3081814)). Qed.
Lemma lem3081816 : term821 = term827.
Proof. exact (TRANS (@lem3081792) (@lem3081815)). Qed.
Lemma lem3081817 : term805 = term828.
Proof. exact (@lem3081743 (@lem3081816)). Qed.
Lemma lem3081818 : term804 = term828.
Proof. exact (TRANS (@lem3081709) (@lem3081817)). Qed.
Lemma lem3081820 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3081821 : term828 = term807.
Proof. exact (@lem3081820 term807). Qed.
Lemma lem3081822 : term804 = term807.
Proof. exact (TRANS (@lem3081818) (@lem3081821)). Qed.
Lemma lem3081823 (_32061 : int) : (term803 _32061) = term829.
Proof. exact (MK_COMB (@lem3081700 _32061) (@lem3081822)). Qed.
Lemma lem3081824 (_32061 : int) : (term802 _32061) = term829.
Proof. exact (TRANS (@lem3081592 _32061) (@lem3081823 _32061)). Qed.
Lemma lem3081825 : term829 = term807.
Proof. exact (@lem1982721 term807). Qed.
Lemma lem3081826 (_32061 : int) : (term802 _32061) = term807.
Proof. exact (TRANS (@lem3081824 _32061) (@lem3081825)). Qed.
Lemma lem3081827 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3081828 (_32061 : int) : (term830 _32061) = term831.
Proof. exact (MK_COMB (@lem3081827) (@lem3081826 _32061)). Qed.
Lemma lem3081829 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3081830 (_32061 : int) : (term801 _32061) = term832.
Proof. exact (MK_COMB (@lem3081828 _32061) (@lem3081829)). Qed.
Lemma lem3081831 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : term832.
Proof. exact (EQ_MP (@lem3081830 _32061) (@lem3081591 _32061 _32062 h1)). Qed.
Lemma lem3081833 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3081834 : term832 = term833.
Proof. exact (@lem3081833 term61 term807). Qed.
Lemma lem3081836 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3081837 : term807 = term828.
Proof. exact (@lem3081836 term816). Qed.
Lemma lem3081839 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081840 : term61 = term92.
Proof. exact (@lem3081839 (NUMERAL 0)). Qed.
Lemma lem3081841 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3081842 : term63 = term210.
Proof. exact (MK_COMB (@lem3081841) (@lem3081840)). Qed.
Lemma lem3081843 : term833 = term834.
Proof. exact (MK_COMB (@lem3081842) (@lem3081837)). Qed.
Lemma lem3081844 : term835.
Proof. exact (@lem1980026 term61 term74 term807 term74). Qed.
Lemma lem3081846 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081847 : term150 = term156.
Proof. exact (@lem3081846 (NUMERAL 0) term75). Qed.
Lemma lem3081848 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081849 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081850 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081849 h1) (fun h1 : term156 = True => @lem3081848)). Qed.
Lemma lem3081851 : term156 = True.
Proof. exact (EQ_MP (@lem3081850) (@lem3081848)). Qed.
Lemma lem3081852 : term150 = True.
Proof. exact (TRANS (@lem3081847) (@lem3081851)). Qed.
Lemma lem3081853 : True = term150.
Proof. exact (SYM (@lem3081852)). Qed.
Lemma lem3081854 : term150.
Proof. exact (EQ_MP (@lem3081853) (@lem0)). Qed.
Lemma lem3081855 : term836.
Proof. exact (@lem3081844 (@lem3081854)). Qed.
Lemma lem3081857 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081858 : term150 = term156.
Proof. exact (@lem3081857 (NUMERAL 0) term75). Qed.
Lemma lem3081859 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081860 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081861 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081860 h1) (fun h1 : term156 = True => @lem3081859)). Qed.
Lemma lem3081862 : term156 = True.
Proof. exact (EQ_MP (@lem3081861) (@lem3081859)). Qed.
Lemma lem3081863 : term150 = True.
Proof. exact (TRANS (@lem3081858) (@lem3081862)). Qed.
Lemma lem3081864 : True = term150.
Proof. exact (SYM (@lem3081863)). Qed.
Lemma lem3081865 : term150.
Proof. exact (EQ_MP (@lem3081864) (@lem0)). Qed.
Lemma lem3081866 : term834 = term837.
Proof. exact (@lem3081855 (@lem3081865)). Qed.
Lemma lem3081868 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3081869 : term822 = term823.
Proof. exact (@lem3081868 term816 term75). Qed.
Lemma lem3081870 : term824 = term814.
Proof. exact (@lem996237 term814). Qed.
Lemma lem3081871 : (term824 = term814) = (term825 = term816).
Proof. exact (@lem1007663 term814 (BIT1 0) term814). Qed.
Lemma lem3081872 : term825 = term816.
Proof. exact (EQ_MP (@lem3081871) (@lem3081870)). Qed.
Lemma lem3081873 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081874 : term826 = term818.
Proof. exact (MK_COMB (@lem3081873) (@lem3081872)). Qed.
Lemma lem3081875 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3081876 : term823 = term807.
Proof. exact (MK_COMB (@lem3081875) (@lem3081874)). Qed.
Lemma lem3081877 : term822 = term807.
Proof. exact (TRANS (@lem3081869) (@lem3081876)). Qed.
Lemma lem3081879 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081880 : term161 = term61.
Proof. exact (@lem3081879 term75). Qed.
Lemma lem3081881 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3081882 : term215 = term63.
Proof. exact (MK_COMB (@lem3081881) (@lem3081880)). Qed.
Lemma lem3081883 : term837 = term833.
Proof. exact (MK_COMB (@lem3081882) (@lem3081877)). Qed.
Lemma lem3081885 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3081886 : term833 = term838.
Proof. exact (@lem3081885 (NUMERAL 0) term816). Qed.
Lemma lem3081887 : term839 = term814.
Proof. exact (@lem912803). Qed.
Lemma lem3081888 (h1 : term839 = term814) : (term816 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term814 h1). Qed.
Lemma lem3081889 : (term839 = term814) = ((term816 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term839 = term814 => @lem3081888 h1) (fun h1 : (term816 = (NUMERAL 0)) = False => @lem3081887)). Qed.
Lemma lem3081890 : (term816 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3081889) (@lem3081887)). Qed.
Lemma lem3081891 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3081892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3081893 : term219 = (and True).
Proof. exact (MK_COMB (@lem3081892) (@lem3081891)). Qed.
Lemma lem3081894 : term838 = (True /\ False).
Proof. exact (MK_COMB (@lem3081893) (@lem3081890)). Qed.
Lemma lem3081896 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3081897 : term838 = False.
Proof. exact (TRANS (@lem3081894) (@lem3081896)). Qed.
Lemma lem3081898 : term833 = False.
Proof. exact (TRANS (@lem3081886) (@lem3081897)). Qed.
Lemma lem3081899 : term837 = False.
Proof. exact (TRANS (@lem3081883) (@lem3081898)). Qed.
Lemma lem3081900 : term834 = False.
Proof. exact (TRANS (@lem3081866) (@lem3081899)). Qed.
Lemma lem3081901 : term833 = False.
Proof. exact (TRANS (@lem3081843) (@lem3081900)). Qed.
Lemma lem3081902 : term832 = False.
Proof. exact (TRANS (@lem3081834) (@lem3081901)). Qed.
Lemma lem3081903 (_32061 : int) (_32062 : int) (h1 : term844 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3081902) (@lem3081831 _32061 _32062 h1)). Qed.
Lemma lem3081904 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term845 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3081905 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term752 _32061 _32062.
Proof. exact (proj2 (@lem3081904 _32061 _32062 h1)). Qed.
Lemma lem3081907 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term721 _32061 _32062.
Proof. exact (proj2 (@lem3081905 _32061 _32062 h1)). Qed.
Lemma lem3081909 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term690 _32061 _32062.
Proof. exact (proj2 (@lem3081907 _32061 _32062 h1)). Qed.
Lemma lem3081910 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term694 _32061 _32062.
Proof. exact (proj1 (@lem3081907 _32061 _32062 h1)). Qed.
Lemma lem3081911 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term667 _32062.
Proof. exact (proj2 (@lem3081910 _32061 _32062 h1)). Qed.
Lemma lem3081913 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term643 _32062.
Proof. exact (proj2 (@lem3081909 _32061 _32062 h1)). Qed.
Lemma lem3081916 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3081917 : term149 = term150.
Proof. exact (@lem3081916 term61 term74). Qed.
Lemma lem3081919 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081920 : term74 = term121.
Proof. exact (@lem3081919 term75). Qed.
Lemma lem3081922 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081923 : term61 = term92.
Proof. exact (@lem3081922 (NUMERAL 0)). Qed.
Lemma lem3081924 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081925 : term151 = term152.
Proof. exact (MK_COMB (@lem3081924) (@lem3081923)). Qed.
Lemma lem3081926 : term150 = term153.
Proof. exact (MK_COMB (@lem3081925) (@lem3081920)). Qed.
Lemma lem3081927 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3081929 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081930 : term150 = term156.
Proof. exact (@lem3081929 (NUMERAL 0) term75). Qed.
Lemma lem3081931 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081932 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081933 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081932 h1) (fun h1 : term156 = True => @lem3081931)). Qed.
Lemma lem3081934 : term156 = True.
Proof. exact (EQ_MP (@lem3081933) (@lem3081931)). Qed.
Lemma lem3081935 : term150 = True.
Proof. exact (TRANS (@lem3081930) (@lem3081934)). Qed.
Lemma lem3081936 : True = term150.
Proof. exact (SYM (@lem3081935)). Qed.
Lemma lem3081937 : term150.
Proof. exact (EQ_MP (@lem3081936) (@lem0)). Qed.
Lemma lem3081938 : term158.
Proof. exact (@lem3081927 (@lem3081937)). Qed.
Lemma lem3081940 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081941 : term150 = term156.
Proof. exact (@lem3081940 (NUMERAL 0) term75). Qed.
Lemma lem3081942 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081943 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081944 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081943 h1) (fun h1 : term156 = True => @lem3081942)). Qed.
Lemma lem3081945 : term156 = True.
Proof. exact (EQ_MP (@lem3081944) (@lem3081942)). Qed.
Lemma lem3081946 : term150 = True.
Proof. exact (TRANS (@lem3081941) (@lem3081945)). Qed.
Lemma lem3081947 : True = term150.
Proof. exact (SYM (@lem3081946)). Qed.
Lemma lem3081948 : term150.
Proof. exact (EQ_MP (@lem3081947) (@lem0)). Qed.
Lemma lem3081949 : term153 = term159.
Proof. exact (@lem3081938 (@lem3081948)). Qed.
Lemma lem3081951 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3081952 : term104 = term105.
Proof. exact (@lem3081951 term75 term75). Qed.
Lemma lem3081953 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3081954 : term107 = term75.
Proof. exact (EQ_MP (@lem3081953) (@lem940073)). Qed.
Lemma lem3081955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3081956 : term105 = term74.
Proof. exact (MK_COMB (@lem3081955) (@lem3081954)). Qed.
Lemma lem3081957 : term104 = term74.
Proof. exact (TRANS (@lem3081952) (@lem3081956)). Qed.
Lemma lem3081959 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3081960 : term161 = term61.
Proof. exact (@lem3081959 term75). Qed.
Lemma lem3081961 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081962 : term162 = term151.
Proof. exact (MK_COMB (@lem3081961) (@lem3081960)). Qed.
Lemma lem3081963 : term159 = term150.
Proof. exact (MK_COMB (@lem3081962) (@lem3081957)). Qed.
Lemma lem3081965 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3081966 : term150 = term156.
Proof. exact (@lem3081965 (NUMERAL 0) term75). Qed.
Lemma lem3081967 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3081968 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3081969 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3081968 h1) (fun h1 : term156 = True => @lem3081967)). Qed.
Lemma lem3081970 : term156 = True.
Proof. exact (EQ_MP (@lem3081969) (@lem3081967)). Qed.
Lemma lem3081971 : term150 = True.
Proof. exact (TRANS (@lem3081966) (@lem3081970)). Qed.
Lemma lem3081972 : term159 = True.
Proof. exact (TRANS (@lem3081963) (@lem3081971)). Qed.
Lemma lem3081973 : term153 = True.
Proof. exact (TRANS (@lem3081949) (@lem3081972)). Qed.
Lemma lem3081974 : term150 = True.
Proof. exact (TRANS (@lem3081926) (@lem3081973)). Qed.
Lemma lem3081975 : term149 = True.
Proof. exact (TRANS (@lem3081917) (@lem3081974)). Qed.
Lemma lem3081976 : True = term149.
Proof. exact (SYM (@lem3081975)). Qed.
Lemma lem3081977 : term149.
Proof. exact (EQ_MP (@lem3081976) (@lem0)). Qed.
Lemma lem3081978 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term794 _32062.
Proof. exact (conj (@lem3081977) (@lem3081913 _32061 _32062 h1)). Qed.
Lemma lem3081980 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3081981 (_32062 : int) : term795 _32062.
Proof. exact (@lem3081980 term74 (term640 _32062)). Qed.
Lemma lem3081982 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term796 _32062.
Proof. exact (@lem3081981 _32062 (@lem3081978 _32061 _32062 h1)). Qed.
Lemma lem3081983 (_32062 : int) : (term797 _32062) = (term640 _32062).
Proof. exact (@lem1982733 (term640 _32062)). Qed.
Lemma lem3081984 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3081985 (_32062 : int) : (term798 _32062) = (term642 _32062).
Proof. exact (MK_COMB (@lem3081984) (@lem3081983 _32062)). Qed.
Lemma lem3081986 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3081987 (_32062 : int) : (term796 _32062) = (term643 _32062).
Proof. exact (MK_COMB (@lem3081985 _32062) (@lem3081986)). Qed.
Lemma lem3081988 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term643 _32062.
Proof. exact (EQ_MP (@lem3081987 _32062) (@lem3081982 _32061 _32062 h1)). Qed.
Lemma lem3081990 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3081991 : term149 = term150.
Proof. exact (@lem3081990 term61 term74). Qed.
Lemma lem3081993 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081994 : term74 = term121.
Proof. exact (@lem3081993 term75). Qed.
Lemma lem3081996 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3081997 : term61 = term92.
Proof. exact (@lem3081996 (NUMERAL 0)). Qed.
Lemma lem3081998 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3081999 : term151 = term152.
Proof. exact (MK_COMB (@lem3081998) (@lem3081997)). Qed.
Lemma lem3082000 : term150 = term153.
Proof. exact (MK_COMB (@lem3081999) (@lem3081994)). Qed.
Lemma lem3082001 : term154.
Proof. exact (@lem1980255 term61 term74 term74 term74). Qed.
Lemma lem3082003 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3082004 : term150 = term156.
Proof. exact (@lem3082003 (NUMERAL 0) term75). Qed.
Lemma lem3082005 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082006 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3082007 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082006 h1) (fun h1 : term156 = True => @lem3082005)). Qed.
Lemma lem3082008 : term156 = True.
Proof. exact (EQ_MP (@lem3082007) (@lem3082005)). Qed.
Lemma lem3082009 : term150 = True.
Proof. exact (TRANS (@lem3082004) (@lem3082008)). Qed.
Lemma lem3082010 : True = term150.
Proof. exact (SYM (@lem3082009)). Qed.
Lemma lem3082011 : term150.
Proof. exact (EQ_MP (@lem3082010) (@lem0)). Qed.
Lemma lem3082012 : term158.
Proof. exact (@lem3082001 (@lem3082011)). Qed.
Lemma lem3082014 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3082015 : term150 = term156.
Proof. exact (@lem3082014 (NUMERAL 0) term75). Qed.
Lemma lem3082016 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082017 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3082018 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082017 h1) (fun h1 : term156 = True => @lem3082016)). Qed.
Lemma lem3082019 : term156 = True.
Proof. exact (EQ_MP (@lem3082018) (@lem3082016)). Qed.
Lemma lem3082020 : term150 = True.
Proof. exact (TRANS (@lem3082015) (@lem3082019)). Qed.
Lemma lem3082021 : True = term150.
Proof. exact (SYM (@lem3082020)). Qed.
Lemma lem3082022 : term150.
Proof. exact (EQ_MP (@lem3082021) (@lem0)). Qed.
Lemma lem3082023 : term153 = term159.
Proof. exact (@lem3082012 (@lem3082022)). Qed.
Lemma lem3082025 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3082026 : term104 = term105.
Proof. exact (@lem3082025 term75 term75). Qed.
Lemma lem3082027 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3082028 : term107 = term75.
Proof. exact (EQ_MP (@lem3082027) (@lem940073)). Qed.
Lemma lem3082029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3082030 : term105 = term74.
Proof. exact (MK_COMB (@lem3082029) (@lem3082028)). Qed.
Lemma lem3082031 : term104 = term74.
Proof. exact (TRANS (@lem3082026) (@lem3082030)). Qed.
Lemma lem3082033 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3082034 : term161 = term61.
Proof. exact (@lem3082033 term75). Qed.
Lemma lem3082035 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3082036 : term162 = term151.
Proof. exact (MK_COMB (@lem3082035) (@lem3082034)). Qed.
Lemma lem3082037 : term159 = term150.
Proof. exact (MK_COMB (@lem3082036) (@lem3082031)). Qed.
Lemma lem3082039 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3082040 : term150 = term156.
Proof. exact (@lem3082039 (NUMERAL 0) term75). Qed.
Lemma lem3082041 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082042 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3082043 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082042 h1) (fun h1 : term156 = True => @lem3082041)). Qed.
Lemma lem3082044 : term156 = True.
Proof. exact (EQ_MP (@lem3082043) (@lem3082041)). Qed.
Lemma lem3082045 : term150 = True.
Proof. exact (TRANS (@lem3082040) (@lem3082044)). Qed.
Lemma lem3082046 : term159 = True.
Proof. exact (TRANS (@lem3082037) (@lem3082045)). Qed.
Lemma lem3082047 : term153 = True.
Proof. exact (TRANS (@lem3082023) (@lem3082046)). Qed.
Lemma lem3082048 : term150 = True.
Proof. exact (TRANS (@lem3082000) (@lem3082047)). Qed.
Lemma lem3082049 : term149 = True.
Proof. exact (TRANS (@lem3081991) (@lem3082048)). Qed.
Lemma lem3082050 : True = term149.
Proof. exact (SYM (@lem3082049)). Qed.
Lemma lem3082051 : term149.
Proof. exact (EQ_MP (@lem3082050) (@lem0)). Qed.
Lemma lem3082052 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term846 _32062.
Proof. exact (conj (@lem3082051) (@lem3081911 _32061 _32062 h1)). Qed.
Lemma lem3082054 (x : real) (y : real) : term164 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3082055 (_32062 : int) : term847 _32062.
Proof. exact (@lem3082054 term74 (term140 _32062)). Qed.
Lemma lem3082056 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term848 _32062.
Proof. exact (@lem3082055 _32062 (@lem3082052 _32061 _32062 h1)). Qed.
Lemma lem3082057 (_32062 : int) : (term849 _32062) = (term140 _32062).
Proof. exact (@lem1982733 (term140 _32062)). Qed.
Lemma lem3082058 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3082059 (_32062 : int) : (term850 _32062) = (term666 _32062).
Proof. exact (MK_COMB (@lem3082058) (@lem3082057 _32062)). Qed.
Lemma lem3082060 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3082061 (_32062 : int) : (term848 _32062) = (term667 _32062).
Proof. exact (MK_COMB (@lem3082059 _32062) (@lem3082060)). Qed.
Lemma lem3082062 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term667 _32062.
Proof. exact (EQ_MP (@lem3082061 _32062) (@lem3082056 _32061 _32062 h1)). Qed.
Lemma lem3082063 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term851 _32062.
Proof. exact (conj (@lem3082062 _32061 _32062 h1) (@lem3081988 _32061 _32062 h1)). Qed.
Lemma lem3082065 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3082066 (_32062 : int) : term852 _32062.
Proof. exact (@lem3082065 (term140 _32062) (term640 _32062)). Qed.
Lemma lem3082067 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term853 _32062.
Proof. exact (@lem3082066 _32062 (@lem3082063 _32061 _32062 h1)). Qed.
Lemma lem3082068 (_32062 : int) : (term854 _32062) = (term791 _32062).
Proof. exact (@lem1982763 (term140 _32062) (real_of_int _32062) term95). Qed.
Lemma lem3082069 (_32062 : int) : (term180 _32062) = (term181 _32062).
Proof. exact (@lem1982713 term95 (real_of_int _32062)). Qed.
Lemma lem3082071 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3082072 : term74 = term121.
Proof. exact (@lem3082071 term75). Qed.
Lemma lem3082074 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3082075 : term95 = term96.
Proof. exact (@lem3082074 term75). Qed.
Lemma lem3082076 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3082077 : term182 = term183.
Proof. exact (MK_COMB (@lem3082076) (@lem3082075)). Qed.
Lemma lem3082078 : term184 = term185.
Proof. exact (MK_COMB (@lem3082077) (@lem3082072)). Qed.
Lemma lem3082079 : term186.
Proof. exact (@lem1981473 term95 term74 term74 term74 term61 term74). Qed.
Lemma lem3082081 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3082082 : term150 = term156.
Proof. exact (@lem3082081 (NUMERAL 0) term75). Qed.
Lemma lem3082083 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082084 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3082085 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082084 h1) (fun h1 : term156 = True => @lem3082083)). Qed.
Lemma lem3082086 : term156 = True.
Proof. exact (EQ_MP (@lem3082085) (@lem3082083)). Qed.
Lemma lem3082087 : term150 = True.
Proof. exact (TRANS (@lem3082082) (@lem3082086)). Qed.
Lemma lem3082088 : True = term150.
Proof. exact (SYM (@lem3082087)). Qed.
Lemma lem3082089 : term150.
Proof. exact (EQ_MP (@lem3082088) (@lem0)). Qed.
Lemma lem3082090 : term187.
Proof. exact (@lem3082079 (@lem3082089)). Qed.
Lemma lem3082092 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3082093 : term150 = term156.
Proof. exact (@lem3082092 (NUMERAL 0) term75). Qed.
Lemma lem3082094 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082095 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3082096 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082095 h1) (fun h1 : term156 = True => @lem3082094)). Qed.
Lemma lem3082097 : term156 = True.
Proof. exact (EQ_MP (@lem3082096) (@lem3082094)). Qed.
Lemma lem3082098 : term150 = True.
Proof. exact (TRANS (@lem3082093) (@lem3082097)). Qed.
Lemma lem3082099 : True = term150.
Proof. exact (SYM (@lem3082098)). Qed.
Lemma lem3082100 : term150.
Proof. exact (EQ_MP (@lem3082099) (@lem0)). Qed.
Lemma lem3082101 : term188.
Proof. exact (@lem3082090 (@lem3082100)). Qed.
Lemma lem3082103 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3082104 : term150 = term156.
Proof. exact (@lem3082103 (NUMERAL 0) term75). Qed.
Lemma lem3082105 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082106 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3082107 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082106 h1) (fun h1 : term156 = True => @lem3082105)). Qed.
Lemma lem3082108 : term156 = True.
Proof. exact (EQ_MP (@lem3082107) (@lem3082105)). Qed.
Lemma lem3082109 : term150 = True.
Proof. exact (TRANS (@lem3082104) (@lem3082108)). Qed.
Lemma lem3082110 : True = term150.
Proof. exact (SYM (@lem3082109)). Qed.
Lemma lem3082111 : term150.
Proof. exact (EQ_MP (@lem3082110) (@lem0)). Qed.
Lemma lem3082112 : term189.
Proof. exact (@lem3082101 (@lem3082111)). Qed.
Lemma lem3082114 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3082115 : term104 = term105.
Proof. exact (@lem3082114 term75 term75). Qed.
Lemma lem3082116 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3082117 : term107 = term75.
Proof. exact (EQ_MP (@lem3082116) (@lem940073)). Qed.
Lemma lem3082118 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3082119 : term105 = term74.
Proof. exact (MK_COMB (@lem3082118) (@lem3082117)). Qed.
Lemma lem3082120 : term104 = term74.
Proof. exact (TRANS (@lem3082115) (@lem3082119)). Qed.
Lemma lem3082122 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3082123 : term122 = term127.
Proof. exact (@lem3082122 term75 term75). Qed.
Lemma lem3082124 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3082125 : term107 = term75.
Proof. exact (EQ_MP (@lem3082124) (@lem940073)). Qed.
Lemma lem3082126 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3082127 : term105 = term74.
Proof. exact (MK_COMB (@lem3082126) (@lem3082125)). Qed.
Lemma lem3082128 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3082129 : term127 = term95.
Proof. exact (MK_COMB (@lem3082128) (@lem3082127)). Qed.
Lemma lem3082130 : term122 = term95.
Proof. exact (TRANS (@lem3082123) (@lem3082129)). Qed.
Lemma lem3082131 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3082132 : term190 = term182.
Proof. exact (MK_COMB (@lem3082131) (@lem3082130)). Qed.
Lemma lem3082133 : term191 = term184.
Proof. exact (MK_COMB (@lem3082132) (@lem3082120)). Qed.
Lemma lem3082135 (m : nat) : (term192 m) = term61.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3082136 : term184 = term61.
Proof. exact (@lem3082135 term75). Qed.
Lemma lem3082137 : term191 = term61.
Proof. exact (TRANS (@lem3082133) (@lem3082136)). Qed.
Lemma lem3082138 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3082139 : term193 = term194.
Proof. exact (MK_COMB (@lem3082138) (@lem3082137)). Qed.
Lemma lem3082140 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem3082141 : term195 = term161.
Proof. exact (MK_COMB (@lem3082139) (@lem3082140)). Qed.
Lemma lem3082143 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3082144 : term161 = term61.
Proof. exact (@lem3082143 term75). Qed.
Lemma lem3082145 : term195 = term61.
Proof. exact (TRANS (@lem3082141) (@lem3082144)). Qed.
Lemma lem3082147 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3082148 : term104 = term105.
Proof. exact (@lem3082147 term75 term75). Qed.
Lemma lem3082149 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3082150 : term107 = term75.
Proof. exact (EQ_MP (@lem3082149) (@lem940073)). Qed.
Lemma lem3082151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3082152 : term105 = term74.
Proof. exact (MK_COMB (@lem3082151) (@lem3082150)). Qed.
Lemma lem3082153 : term104 = term74.
Proof. exact (TRANS (@lem3082148) (@lem3082152)). Qed.
Lemma lem3082154 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem3082155 : term196 = term161.
Proof. exact (MK_COMB (@lem3082154) (@lem3082153)). Qed.
Lemma lem3082157 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3082158 : term161 = term61.
Proof. exact (@lem3082157 term75). Qed.
Lemma lem3082159 : term196 = term61.
Proof. exact (TRANS (@lem3082155) (@lem3082158)). Qed.
Lemma lem3082160 : term61 = term196.
Proof. exact (SYM (@lem3082159)). Qed.
Lemma lem3082161 : term195 = term196.
Proof. exact (TRANS (@lem3082145) (@lem3082160)). Qed.
Lemma lem3082162 : term185 = term92.
Proof. exact (@lem3082112 (@lem3082161)). Qed.
Lemma lem3082163 : term184 = term92.
Proof. exact (TRANS (@lem3082078) (@lem3082162)). Qed.
Lemma lem3082165 (x : real) : (term111 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3082166 : term92 = term61.
Proof. exact (@lem3082165 term61). Qed.
Lemma lem3082167 : term184 = term61.
Proof. exact (TRANS (@lem3082163) (@lem3082166)). Qed.
Lemma lem3082168 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3082169 : term197 = term194.
Proof. exact (MK_COMB (@lem3082168) (@lem3082167)). Qed.
Lemma lem3082170 (_32062 : int) : (real_of_int _32062) = (real_of_int _32062).
Proof. exact (eq_refl (real_of_int _32062)). Qed.
Lemma lem3082171 (_32062 : int) : (term181 _32062) = (term198 _32062).
Proof. exact (MK_COMB (@lem3082169) (@lem3082170 _32062)). Qed.
Lemma lem3082172 (_32062 : int) : (term180 _32062) = (term198 _32062).
Proof. exact (TRANS (@lem3082069 _32062) (@lem3082171 _32062)). Qed.
Lemma lem3082173 (_32062 : int) : (term198 _32062) = term61.
Proof. exact (@lem1982719 (real_of_int _32062)). Qed.
Lemma lem3082174 (_32062 : int) : (term180 _32062) = term61.
Proof. exact (TRANS (@lem3082172 _32062) (@lem3082173 _32062)). Qed.
Lemma lem3082175 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3082176 (_32062 : int) : (term199 _32062) = term200.
Proof. exact (MK_COMB (@lem3082175) (@lem3082174 _32062)). Qed.
Lemma lem3082177 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3082178 (_32062 : int) : (term791 _32062) = term205.
Proof. exact (MK_COMB (@lem3082176 _32062) (@lem3082177)). Qed.
Lemma lem3082179 (_32062 : int) : (term854 _32062) = term205.
Proof. exact (TRANS (@lem3082068 _32062) (@lem3082178 _32062)). Qed.
Lemma lem3082180 : term205 = term95.
Proof. exact (@lem1982721 term95). Qed.
Lemma lem3082181 (_32062 : int) : (term854 _32062) = term95.
Proof. exact (TRANS (@lem3082179 _32062) (@lem3082180)). Qed.
Lemma lem3082182 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3082183 (_32062 : int) : (term855 _32062) = term207.
Proof. exact (MK_COMB (@lem3082182) (@lem3082181 _32062)). Qed.
Lemma lem3082184 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3082185 (_32062 : int) : (term853 _32062) = term208.
Proof. exact (MK_COMB (@lem3082183 _32062) (@lem3082184)). Qed.
Lemma lem3082186 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : term208.
Proof. exact (EQ_MP (@lem3082185 _32062) (@lem3082067 _32061 _32062 h1)). Qed.
Lemma lem3082188 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3082189 : term208 = term209.
Proof. exact (@lem3082188 term61 term95). Qed.
Lemma lem3082191 (x : nat) : (term93 x) = (term94 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3082192 : term95 = term96.
Proof. exact (@lem3082191 term75). Qed.
Lemma lem3082194 (x : nat) : (real_of_num x) = (term91 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3082195 : term61 = term92.
Proof. exact (@lem3082194 (NUMERAL 0)). Qed.
Lemma lem3082196 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3082197 : term63 = term210.
Proof. exact (MK_COMB (@lem3082196) (@lem3082195)). Qed.
Lemma lem3082198 : term209 = term211.
Proof. exact (MK_COMB (@lem3082197) (@lem3082192)). Qed.
Lemma lem3082199 : term212.
Proof. exact (@lem1980026 term61 term74 term95 term74). Qed.
Lemma lem3082201 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3082202 : term150 = term156.
Proof. exact (@lem3082201 (NUMERAL 0) term75). Qed.
Lemma lem3082203 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082204 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3082205 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082204 h1) (fun h1 : term156 = True => @lem3082203)). Qed.
Lemma lem3082206 : term156 = True.
Proof. exact (EQ_MP (@lem3082205) (@lem3082203)). Qed.
Lemma lem3082207 : term150 = True.
Proof. exact (TRANS (@lem3082202) (@lem3082206)). Qed.
Lemma lem3082208 : True = term150.
Proof. exact (SYM (@lem3082207)). Qed.
Lemma lem3082209 : term150.
Proof. exact (EQ_MP (@lem3082208) (@lem0)). Qed.
Lemma lem3082210 : term213.
Proof. exact (@lem3082199 (@lem3082209)). Qed.
Lemma lem3082212 (m : nat) (n : nat) : (term155 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3082213 : term150 = term156.
Proof. exact (@lem3082212 (NUMERAL 0) term75). Qed.
Lemma lem3082214 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082215 (h1 : term157 = (BIT1 0)) : term156 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3082216 : (term157 = (BIT1 0)) = (term156 = True).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082215 h1) (fun h1 : term156 = True => @lem3082214)). Qed.
Lemma lem3082217 : term156 = True.
Proof. exact (EQ_MP (@lem3082216) (@lem3082214)). Qed.
Lemma lem3082218 : term150 = True.
Proof. exact (TRANS (@lem3082213) (@lem3082217)). Qed.
Lemma lem3082219 : True = term150.
Proof. exact (SYM (@lem3082218)). Qed.
Lemma lem3082220 : term150.
Proof. exact (EQ_MP (@lem3082219) (@lem0)). Qed.
Lemma lem3082221 : term211 = term214.
Proof. exact (@lem3082210 (@lem3082220)). Qed.
Lemma lem3082223 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3082224 : term122 = term127.
Proof. exact (@lem3082223 term75 term75). Qed.
Lemma lem3082225 : (term106 = (BIT1 0)) = (term107 = term75).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3082226 : term107 = term75.
Proof. exact (EQ_MP (@lem3082225) (@lem940073)). Qed.
Lemma lem3082227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3082228 : term105 = term74.
Proof. exact (MK_COMB (@lem3082227) (@lem3082226)). Qed.
Lemma lem3082229 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3082230 : term127 = term95.
Proof. exact (MK_COMB (@lem3082229) (@lem3082228)). Qed.
Lemma lem3082231 : term122 = term95.
Proof. exact (TRANS (@lem3082224) (@lem3082230)). Qed.
Lemma lem3082233 (x : nat) : (term160 x) = term61.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3082234 : term161 = term61.
Proof. exact (@lem3082233 term75). Qed.
Lemma lem3082235 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3082236 : term215 = term63.
Proof. exact (MK_COMB (@lem3082235) (@lem3082234)). Qed.
Lemma lem3082237 : term214 = term209.
Proof. exact (MK_COMB (@lem3082236) (@lem3082231)). Qed.
Lemma lem3082239 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3082240 : term209 = term218.
Proof. exact (@lem3082239 (NUMERAL 0) term75). Qed.
Lemma lem3082241 : term157 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3082242 (h1 : term157 = (BIT1 0)) : (term75 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3082243 : (term157 = (BIT1 0)) = ((term75 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term157 = (BIT1 0) => @lem3082242 h1) (fun h1 : (term75 = (NUMERAL 0)) = False => @lem3082241)). Qed.
Lemma lem3082244 : (term75 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3082243) (@lem3082241)). Qed.
Lemma lem3082245 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3082246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3082247 : term219 = (and True).
Proof. exact (MK_COMB (@lem3082246) (@lem3082245)). Qed.
Lemma lem3082248 : term218 = (True /\ False).
Proof. exact (MK_COMB (@lem3082247) (@lem3082244)). Qed.
Lemma lem3082250 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3082251 : term218 = False.
Proof. exact (TRANS (@lem3082248) (@lem3082250)). Qed.
Lemma lem3082252 : term209 = False.
Proof. exact (TRANS (@lem3082240) (@lem3082251)). Qed.
Lemma lem3082253 : term214 = False.
Proof. exact (TRANS (@lem3082237) (@lem3082252)). Qed.
Lemma lem3082254 : term211 = False.
Proof. exact (TRANS (@lem3082221) (@lem3082253)). Qed.
Lemma lem3082255 : term209 = False.
Proof. exact (TRANS (@lem3082198) (@lem3082254)). Qed.
Lemma lem3082256 : term208 = False.
Proof. exact (TRANS (@lem3082189) (@lem3082255)). Qed.
Lemma lem3082257 (_32061 : int) (_32062 : int) (h1 : term845 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3082256) (@lem3082186 _32061 _32062 h1)). Qed.
Lemma lem3082258 (_32061 : int) (_32062 : int) (h1 : term750 _32061 _32062) : False.
Proof. exact (or_elim (@lem3081427 _32061 _32062 h1) (fun h0 : term844 _32061 _32062 => @lem3081903 _32061 _32062 h0) (fun h0 : term845 _32061 _32062 => @lem3082257 _32061 _32062 h0)). Qed.
Lemma lem3082259 (_32061 : int) (_32062 : int) (h1 : term759 _32061 _32062) : False.
Proof. exact (or_elim (@lem3080594 _32061 _32062 h1) (fun h0 : term754 _32061 _32062 => @lem3081426 _32061 _32062 h0) (fun h0 : term750 _32061 _32062 => @lem3082258 _32061 _32062 h0)). Qed.
Lemma lem3082260 (_32061 : int) (_32062 : int) (h1 : term775 _32061 _32062) : False.
Proof. exact (or_elim (@lem3078927 _32061 _32062 h1) (fun h0 : term772 _32061 _32062 => @lem3080593 _32061 _32062 h0) (fun h0 : term759 _32061 _32062 => @lem3082259 _32061 _32062 h0)). Qed.
Lemma lem3082262 (_32061 : int) (_32062 : int) (h1 : term775 _32061 _32062) : term775 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3082263 (_32061 : int) (_32062 : int) (h1 : term775 _32061 _32062) : (term775 _32061 _32062) = False.
Proof. exact (prop_ext (fun h2 : term775 _32061 _32062 => @lem3082260 _32061 _32062 h1) (fun h2 : False => @lem3082262 _32061 _32062 h1)). Qed.
Lemma lem3082264 (_32061 : int) (_32062 : int) (h1 : term775 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3082263 _32061 _32062 h1) (@lem3082262 _32061 _32062 h1)). Qed.
Lemma lem3082265 (_32061 : int) (_32062 : int) (h1 : term627 _32061 _32062) : term627 _32061 _32062.
Proof. exact (h1). Qed.
Lemma lem3082266 (_32061 : int) (_32062 : int) (h1 : term627 _32061 _32062) : term775 _32061 _32062.
Proof. exact (EQ_MP (@lem3078881 _32061 _32062) (@lem3082265 _32061 _32062 h1)). Qed.
Lemma lem3082267 (_32061 : int) (_32062 : int) (h1 : term627 _32061 _32062) : (term775 _32061 _32062) = False.
Proof. exact (prop_ext (fun h2 : term775 _32061 _32062 => @lem3082264 _32061 _32062 h2) (fun h2 : False => @lem3082266 _32061 _32062 h1)). Qed.
Lemma lem3082268 (_32061 : int) (_32062 : int) (h1 : term627 _32061 _32062) : False.
Proof. exact (EQ_MP (@lem3082267 _32061 _32062 h1) (@lem3082266 _32061 _32062 h1)). Qed.
Lemma lem3082269 (_32061 : int) (_32062 : int) : term856 _32061 _32062.
Proof. exact (fun h0 : term627 _32061 _32062 => @lem3082268 _32061 _32062 h0). Qed.
Lemma lem3082270 (_32061 : int) (_32062 : int) : term857 _32061 _32062.
Proof. exact (@lem1386578 (term858 _32061 _32062)). Qed.
Lemma lem3082273 (_32061 : int) (_32062 : int) : term858 _32061 _32062.
Proof. exact (@lem3082270 _32061 _32062 (@lem3082269 _32061 _32062)). Qed.
Lemma lem3082274 (_32061 : int) (_32062 : int) : (term626 _32061 _32062) = (term593 _32061 _32062).
Proof. exact (SYM (@lem3077916 _32061 _32062)). Qed.
Lemma lem3082275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3082276 (_32061 : int) (_32062 : int) : (term858 _32061 _32062) = (term573 _32061 _32062).
Proof. exact (MK_COMB (@lem3082275) (@lem3082274 _32061 _32062)). Qed.
Lemma lem3082277 (_32061 : int) (_32062 : int) : term573 _32061 _32062.
Proof. exact (EQ_MP (@lem3082276 _32061 _32062) (@lem3082273 _32061 _32062)). Qed.
Lemma lem3082278 (_32061 : int) (_32062 : int) : term574 _32061 _32062.
Proof. exact (EQ_MP (@lem3077633 _32061 _32062) (@lem3082277 _32061 _32062)). Qed.
Lemma lem3082279 (m : nat) (n : nat) : term859 m n.
Proof. exact (@lem3082278 (int_of_num m) (int_of_num n)). Qed.
Lemma lem3082280 (m : nat) (n : nat) : term860 m n.
Proof. exact (@lem3082279 m n (@lem3077629 m)). Qed.
Lemma lem3082281 (m : nat) (n : nat) : term568 m n.
Proof. exact (@lem3082280 m n (@lem3077632 n)). Qed.
Lemma lem3082282 (m : nat) : term570 m.
Proof. exact (fun n : nat => @lem3082281 m n). Qed.
Lemma lem3082283 : term572.
Proof. exact (fun m : nat => @lem3082282 m). Qed.
Lemma lem3082284 : term572 = term560.
Proof. exact (SYM (@lem3077626)). Qed.
Lemma lem3082285 : term560.
Proof. exact (EQ_MP (@lem3082284) (@lem3082283)). Qed.
Lemma lem3082286 : term560 = (term560 = True).
Proof. exact (@lem7 term560). Qed.
Lemma lem3082287 : term560 = True.
Proof. exact (EQ_MP (@lem3082286) (@lem3082285)). Qed.
Lemma lem3082288 : True = term560.
Proof. exact (SYM (@lem3082287)). Qed.
Lemma lem3082289 : term560.
Proof. exact (EQ_MP (@lem3082288) (@lem0)). Qed.
Lemma lem3082290 : term237.
Proof. exact (EQ_MP (@lem3077459) (@lem3082289)). Qed.
Lemma lem3082291 : term237 = term241.
Proof. exact (prop_ext (fun h1 : term237 => @lem3077411 h1) (fun h1 : term241 => @lem3082290)). Qed.
Lemma lem3082292 : term241.
Proof. exact (EQ_MP (@lem3082291) (@lem3082290)). Qed.
