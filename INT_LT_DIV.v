Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_DIV_term_abbrevs.
Require Import INT_DIV_EQ_0_spec.
Require Import INT_LE_DIV_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365720_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1482981_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
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
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
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
Require Import thm1988348_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
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
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2651668 (m : int) : term0 m.
Proof. exact (@lem2626069 m). Qed.
Lemma lem2651669 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2651670 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2651669 m) (@lem2651668 m)). Qed.
Lemma lem2651671 (m : int) (n : int) : term2 m n.
Proof. exact (@lem2651670 m n). Qed.
Lemma lem2651672 (m : int) (n : int) : (term2 m n) = (((div m n) = term3) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2651674 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2651675 (m : int) (h1 : term5) : term6 m.
Proof. exact (@lem2651674 h1 m). Qed.
Lemma lem2651676 (m : int) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem2651677 (m : int) (h1 : term5) : term7 m.
Proof. exact (EQ_MP (@lem2651676 m) (@lem2651675 m h1)). Qed.
Lemma lem2651678 (m : int) (n : int) (h1 : term5) : term8 m n.
Proof. exact (@lem2651677 m h1 n). Qed.
Lemma lem2651679 (m : int) (n : int) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem2651680 (m : int) (n : int) (h1 : term5) : term9 m n.
Proof. exact (EQ_MP (@lem2651679 m n) (@lem2651678 m n h1)). Qed.
Lemma lem2651681 (m : int) (n : int) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem2651682 (m : int) (n : int) (h1 : term5) (h2 : term10 m n) : term11 m n.
Proof. exact (@lem2651680 m n h1 (@lem2651681 m n h2)). Qed.
Lemma lem2651683 (m : int) (n : int) (h1 : term10 m n) : term12 m n.
Proof. exact (fun h0 : term5 => @lem2651682 m n h0 h1). Qed.
Lemma lem2651684 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2651685 (m : int) (n : int) (h1 : term5) (h2 : term10 m n) : term11 m n.
Proof. exact (@lem2651683 m n h2 (@lem2651684 h1)). Qed.
Lemma lem2651686 (m : int) (n : int) (h1 : term5) : term9 m n.
Proof. exact (fun h0 : term10 m n => @lem2651685 m n h1 h0). Qed.
Lemma lem2651687 (m : int) (h1 : term5) : term7 m.
Proof. exact (fun n : int => @lem2651686 m n h1). Qed.
Lemma lem2651688 (h1 : term5) : term5.
Proof. exact (fun m : int => @lem2651687 m h1). Qed.
Lemma lem2651689 : term13.
Proof. exact (fun h0 : term5 => @lem2651688 h0). Qed.
Lemma lem2651690 : term5.
Proof. exact (@lem2651689 (@lem2651667)). Qed.
Lemma lem2651691 (m : int) : term6 m.
Proof. exact (@lem2651690 m). Qed.
Lemma lem2651692 (m : int) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem2651693 (m : int) : term7 m.
Proof. exact (EQ_MP (@lem2651692 m) (@lem2651691 m)). Qed.
Lemma lem2651694 (m : int) (n : int) : term8 m n.
Proof. exact (@lem2651693 m n). Qed.
Lemma lem2651695 (m : int) (n : int) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem2651697 (x : int) : (term14 x) = ((term15 x) = (term16 x)).
Proof. exact (@lem2318604 ((term15 x) = (term16 x))). Qed.
Lemma lem2651712 (x : int) : (term17 x) = (x = term3).
Proof. exact (@lem16933 (x = term3)). Qed.
Lemma lem2651714 (x : int) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2651715 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2651714 x) (@lem2651712 x)). Qed.
Lemma lem2651716 (x : int) : (term21 x) = (term19 x).
Proof. exact (@lem17045 (term22 x) (term23 x)). Qed.
Lemma lem2651717 (x : int) : (term21 x) = (term20 x).
Proof. exact (TRANS (@lem2651716 x) (@lem2651715 x)). Qed.
Lemma lem2651723 (x : int) : (term24 x) = (term24 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem2651725 (x : int) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem2651726 (x : int) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem2651725 x) (@lem2651717 x)). Qed.
Lemma lem2651727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2651728 (x : int) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem2651727) (@lem2651726 x)). Qed.
Lemma lem2651729 (x : int) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem2651728 x) (@lem2651723 x)). Qed.
Lemma lem2651730 (x : int) : (term32 x) = (term30 x).
Proof. exact (@lem17646 (term15 x) (term16 x)). Qed.
Lemma lem2651760 (x : int) : (term32 x) = (term31 x).
Proof. exact (TRANS (@lem2651730 x) (@lem2651729 x)). Qed.
Lemma lem2651762 (x : int) (y : int) : (int_lt x y) = (term33 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2651763 (x : int) : (term15 x) = (term34 x).
Proof. exact (@lem2651762 term3 x). Qed.
Lemma lem2651765 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2651766 (x : int) : (term34 x) = (term36 x).
Proof. exact (@lem2651765 term37 x). Qed.
Lemma lem2651768 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2651769 : term40 = term41.
Proof. exact (@lem2651768 term3 term42). Qed.
Lemma lem2651771 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651772 : term44 = term45.
Proof. exact (@lem2651771 (NUMERAL 0)). Qed.
Lemma lem2651773 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2651774 : term46 = term47.
Proof. exact (MK_COMB (@lem2651773) (@lem2651772)). Qed.
Lemma lem2651776 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651777 : term48 = term49.
Proof. exact (@lem2651776 term50). Qed.
Lemma lem2651778 : term41 = term51.
Proof. exact (MK_COMB (@lem2651774) (@lem2651777)). Qed.
Lemma lem2651779 : term40 = term51.
Proof. exact (TRANS (@lem2651769) (@lem2651778)). Qed.
Lemma lem2651780 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2651781 : term52 = term53.
Proof. exact (MK_COMB (@lem2651780) (@lem2651779)). Qed.
Lemma lem2651782 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2651783 (x : int) : (term36 x) = (term54 x).
Proof. exact (MK_COMB (@lem2651781) (@lem2651782 x)). Qed.
Lemma lem2651784 (x : int) : (term34 x) = (term54 x).
Proof. exact (TRANS (@lem2651766 x) (@lem2651783 x)). Qed.
Lemma lem2651785 (x : int) : (term15 x) = (term54 x).
Proof. exact (TRANS (@lem2651763 x) (@lem2651784 x)). Qed.
Lemma lem2651787 (y : int) (x : int) : (term55 x y) = (term33 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2651788 (x : int) : (term56 x) = (term57 x).
Proof. exact (@lem2651787 x term3). Qed.
Lemma lem2651790 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2651791 (x : int) : (term57 x) = (term58 x).
Proof. exact (@lem2651790 (term59 x) term3). Qed.
Lemma lem2651793 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2651794 (x : int) : (term60 x) = (term61 x).
Proof. exact (@lem2651793 x term42). Qed.
Lemma lem2651796 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651797 : term48 = term49.
Proof. exact (@lem2651796 term50). Qed.
Lemma lem2651798 (x : int) : (term62 x) = (term62 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem2651799 (x : int) : (term61 x) = (term63 x).
Proof. exact (MK_COMB (@lem2651798 x) (@lem2651797)). Qed.
Lemma lem2651800 (x : int) : (term60 x) = (term63 x).
Proof. exact (TRANS (@lem2651794 x) (@lem2651799 x)). Qed.
Lemma lem2651801 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2651802 (x : int) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem2651801) (@lem2651800 x)). Qed.
Lemma lem2651804 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651805 : term44 = term45.
Proof. exact (@lem2651804 (NUMERAL 0)). Qed.
Lemma lem2651806 (x : int) : (term58 x) = (term66 x).
Proof. exact (MK_COMB (@lem2651802 x) (@lem2651805)). Qed.
Lemma lem2651807 (x : int) : (term57 x) = (term66 x).
Proof. exact (TRANS (@lem2651791 x) (@lem2651806 x)). Qed.
Lemma lem2651808 (x : int) : (term56 x) = (term66 x).
Proof. exact (TRANS (@lem2651788 x) (@lem2651807 x)). Qed.
Lemma lem2651811 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2651812 (x : int) : (x = term3) = ((real_of_int x) = term44).
Proof. exact (@lem2651811 x term3). Qed.
Lemma lem2651816 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651817 : term44 = term45.
Proof. exact (@lem2651816 (NUMERAL 0)). Qed.
Lemma lem2651818 (x : int) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem2651819 (x : int) : ((real_of_int x) = term44) = ((real_of_int x) = term45).
Proof. exact (MK_COMB (@lem2651818 x) (@lem2651817)). Qed.
Lemma lem2651821 (x : int) : (x = term3) = ((real_of_int x) = term45).
Proof. exact (TRANS (@lem2651812 x) (@lem2651819 x)). Qed.
Lemma lem2651822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2651823 (x : int) : (term18 x) = (term68 x).
Proof. exact (MK_COMB (@lem2651822) (@lem2651808 x)). Qed.
Lemma lem2651824 (x : int) : (term20 x) = (term69 x).
Proof. exact (MK_COMB (@lem2651823 x) (@lem2651821 x)). Qed.
Lemma lem2651825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2651826 (x : int) : (term25 x) = (term70 x).
Proof. exact (MK_COMB (@lem2651825) (@lem2651785 x)). Qed.
Lemma lem2651827 (x : int) : (term27 x) = (term71 x).
Proof. exact (MK_COMB (@lem2651826 x) (@lem2651824 x)). Qed.
Lemma lem2651829 (y : int) (x : int) : (term72 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2651830 (x : int) : (term73 x) = (term74 x).
Proof. exact (@lem2651829 x term3). Qed.
Lemma lem2651832 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2651833 (x : int) : (term74 x) = (term75 x).
Proof. exact (@lem2651832 x term3). Qed.
Lemma lem2651835 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651836 : term44 = term45.
Proof. exact (@lem2651835 (NUMERAL 0)). Qed.
Lemma lem2651837 (x : int) : (term76 x) = (term76 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem2651838 (x : int) : (term75 x) = (term77 x).
Proof. exact (MK_COMB (@lem2651837 x) (@lem2651836)). Qed.
Lemma lem2651839 (x : int) : (term74 x) = (term77 x).
Proof. exact (TRANS (@lem2651833 x) (@lem2651838 x)). Qed.
Lemma lem2651840 (x : int) : (term73 x) = (term77 x).
Proof. exact (TRANS (@lem2651830 x) (@lem2651839 x)). Qed.
Lemma lem2651843 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2651844 (x : int) : (term22 x) = (term78 x).
Proof. exact (@lem2651843 term3 x). Qed.
Lemma lem2651846 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651847 : term44 = term45.
Proof. exact (@lem2651846 (NUMERAL 0)). Qed.
Lemma lem2651848 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2651849 : term79 = term80.
Proof. exact (MK_COMB (@lem2651848) (@lem2651847)). Qed.
Lemma lem2651850 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2651851 (x : int) : (term78 x) = (term81 x).
Proof. exact (MK_COMB (@lem2651849) (@lem2651850 x)). Qed.
Lemma lem2651853 (x : int) : (term22 x) = (term81 x).
Proof. exact (TRANS (@lem2651844 x) (@lem2651851 x)). Qed.
Lemma lem2651855 (y : int) (x : int) : (term82 x y) = (term83 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2651856 (x : int) : (term23 x) = (term84 x).
Proof. exact (@lem2651855 term3 x). Qed.
Lemma lem2651858 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2651859 (x : int) : (term57 x) = (term58 x).
Proof. exact (@lem2651858 (term59 x) term3). Qed.
Lemma lem2651861 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2651862 (x : int) : (term60 x) = (term61 x).
Proof. exact (@lem2651861 x term42). Qed.
Lemma lem2651864 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651865 : term48 = term49.
Proof. exact (@lem2651864 term50). Qed.
Lemma lem2651866 (x : int) : (term62 x) = (term62 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem2651867 (x : int) : (term61 x) = (term63 x).
Proof. exact (MK_COMB (@lem2651866 x) (@lem2651865)). Qed.
Lemma lem2651868 (x : int) : (term60 x) = (term63 x).
Proof. exact (TRANS (@lem2651862 x) (@lem2651867 x)). Qed.
Lemma lem2651869 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2651870 (x : int) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem2651869) (@lem2651868 x)). Qed.
Lemma lem2651872 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651873 : term44 = term45.
Proof. exact (@lem2651872 (NUMERAL 0)). Qed.
Lemma lem2651874 (x : int) : (term58 x) = (term66 x).
Proof. exact (MK_COMB (@lem2651870 x) (@lem2651873)). Qed.
Lemma lem2651875 (x : int) : (term57 x) = (term66 x).
Proof. exact (TRANS (@lem2651859 x) (@lem2651874 x)). Qed.
Lemma lem2651876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2651877 (x : int) : (term85 x) = (term68 x).
Proof. exact (MK_COMB (@lem2651876) (@lem2651875 x)). Qed.
Lemma lem2651879 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2651880 (x : int) : (term34 x) = (term36 x).
Proof. exact (@lem2651879 term37 x). Qed.
Lemma lem2651882 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2651883 : term40 = term41.
Proof. exact (@lem2651882 term3 term42). Qed.
Lemma lem2651885 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651886 : term44 = term45.
Proof. exact (@lem2651885 (NUMERAL 0)). Qed.
Lemma lem2651887 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2651888 : term46 = term47.
Proof. exact (MK_COMB (@lem2651887) (@lem2651886)). Qed.
Lemma lem2651890 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2651891 : term48 = term49.
Proof. exact (@lem2651890 term50). Qed.
Lemma lem2651892 : term41 = term51.
Proof. exact (MK_COMB (@lem2651888) (@lem2651891)). Qed.
Lemma lem2651893 : term40 = term51.
Proof. exact (TRANS (@lem2651883) (@lem2651892)). Qed.
Lemma lem2651894 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2651895 : term52 = term53.
Proof. exact (MK_COMB (@lem2651894) (@lem2651893)). Qed.
Lemma lem2651896 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2651897 (x : int) : (term36 x) = (term54 x).
Proof. exact (MK_COMB (@lem2651895) (@lem2651896 x)). Qed.
Lemma lem2651898 (x : int) : (term34 x) = (term54 x).
Proof. exact (TRANS (@lem2651880 x) (@lem2651897 x)). Qed.
Lemma lem2651899 (x : int) : (term84 x) = (term86 x).
Proof. exact (MK_COMB (@lem2651877 x) (@lem2651898 x)). Qed.
Lemma lem2651900 (x : int) : (term23 x) = (term86 x).
Proof. exact (TRANS (@lem2651856 x) (@lem2651899 x)). Qed.
Lemma lem2651901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2651902 (x : int) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem2651901) (@lem2651853 x)). Qed.
Lemma lem2651903 (x : int) : (term16 x) = (term89 x).
Proof. exact (MK_COMB (@lem2651902 x) (@lem2651900 x)). Qed.
Lemma lem2651904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2651905 (x : int) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem2651904) (@lem2651840 x)). Qed.
Lemma lem2651906 (x : int) : (term24 x) = (term92 x).
Proof. exact (MK_COMB (@lem2651905 x) (@lem2651903 x)). Qed.
Lemma lem2651907 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2651908 (x : int) : (term29 x) = (term93 x).
Proof. exact (MK_COMB (@lem2651907) (@lem2651827 x)). Qed.
Lemma lem2651909 (x : int) : (term31 x) = (term94 x).
Proof. exact (MK_COMB (@lem2651908 x) (@lem2651906 x)). Qed.
Lemma lem2651910 (x : int) : (term32 x) = (term94 x).
Proof. exact (TRANS (@lem2651760 x) (@lem2651909 x)). Qed.
Lemma lem2651914 (t : Prop) : (term95 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2651980 (x : int) : (term96 x) = (term94 x).
Proof. exact (@lem2651914 (term94 x)). Qed.
Lemma lem2651981 (x : int) : (term54 x) = (term97 x).
Proof. exact (@lem1988287 (real_of_int x) term51). Qed.
Lemma lem2651988 : term51 = term49.
Proof. exact (@lem1982721 term49). Qed.
Lemma lem2651991 (x : int) : (term98 x) = (term98 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem2651992 (x : int) : (term99 x) = (term100 x).
Proof. exact (MK_COMB (@lem2651991 x) (@lem2651988)). Qed.
Lemma lem2651993 (x : int) : (term100 x) = (term101 x).
Proof. exact (@lem1982792 (real_of_int x) term49). Qed.
Lemma lem2651995 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2651996 : term49 = term103.
Proof. exact (@lem2651995 term50). Qed.
Lemma lem2651998 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2651999 : term106 = term107.
Proof. exact (@lem2651998 term50). Qed.
Lemma lem2652000 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652001 : term108 = term109.
Proof. exact (MK_COMB (@lem2652000) (@lem2651999)). Qed.
Lemma lem2652002 : term110 = term111.
Proof. exact (MK_COMB (@lem2652001) (@lem2651996)). Qed.
Lemma lem2652003 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2652005 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652006 : term115 = term116.
Proof. exact (@lem2652005 term50 term50). Qed.
Lemma lem2652007 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652008 : term118 = term50.
Proof. exact (EQ_MP (@lem2652007) (@lem940073)). Qed.
Lemma lem2652009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652010 : term116 = term49.
Proof. exact (MK_COMB (@lem2652009) (@lem2652008)). Qed.
Lemma lem2652011 : term115 = term49.
Proof. exact (TRANS (@lem2652006) (@lem2652010)). Qed.
Lemma lem2652013 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652014 : term110 = term121.
Proof. exact (@lem2652013 term50 term50). Qed.
Lemma lem2652015 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652016 : term118 = term50.
Proof. exact (EQ_MP (@lem2652015) (@lem940073)). Qed.
Lemma lem2652017 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652018 : term116 = term49.
Proof. exact (MK_COMB (@lem2652017) (@lem2652016)). Qed.
Lemma lem2652019 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652020 : term121 = term106.
Proof. exact (MK_COMB (@lem2652019) (@lem2652018)). Qed.
Lemma lem2652021 : term110 = term106.
Proof. exact (TRANS (@lem2652014) (@lem2652020)). Qed.
Lemma lem2652022 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2652023 : term122 = term123.
Proof. exact (MK_COMB (@lem2652022) (@lem2652021)). Qed.
Lemma lem2652024 : term112 = term107.
Proof. exact (MK_COMB (@lem2652023) (@lem2652011)). Qed.
Lemma lem2652025 : term111 = term107.
Proof. exact (TRANS (@lem2652003) (@lem2652024)). Qed.
Lemma lem2652026 : term110 = term107.
Proof. exact (TRANS (@lem2652002) (@lem2652025)). Qed.
Lemma lem2652028 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2652029 : term107 = term106.
Proof. exact (@lem2652028 term106). Qed.
Lemma lem2652030 : term110 = term106.
Proof. exact (TRANS (@lem2652026) (@lem2652029)). Qed.
Lemma lem2652031 (x : int) : (term62 x) = (term62 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem2652034 (x : int) : (term101 x) = (term125 x).
Proof. exact (MK_COMB (@lem2652031 x) (@lem2652030)). Qed.
Lemma lem2652035 (x : int) : (term100 x) = (term125 x).
Proof. exact (TRANS (@lem2651993 x) (@lem2652034 x)). Qed.
Lemma lem2652036 (x : int) : (term99 x) = (term125 x).
Proof. exact (TRANS (@lem2651992 x) (@lem2652035 x)). Qed.
Lemma lem2652037 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652038 (x : int) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem2652037) (@lem2652036 x)). Qed.
Lemma lem2652039 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652040 (x : int) : (term97 x) = (term128 x).
Proof. exact (MK_COMB (@lem2652038 x) (@lem2652039)). Qed.
Lemma lem2652041 (x : int) : (term54 x) = (term128 x).
Proof. exact (TRANS (@lem2651981 x) (@lem2652040 x)). Qed.
Lemma lem2652042 (x : int) : (term66 x) = (term129 x).
Proof. exact (@lem1988287 term45 (term63 x)). Qed.
Lemma lem2652054 (x : int) : (term130 x) = (term131 x).
Proof. exact (@lem1982792 term45 (term63 x)). Qed.
Lemma lem2652055 (x : int) : (term132 x) = (term133 x).
Proof. exact (@lem1982781 (real_of_int x) term106 term49). Qed.
Lemma lem2652057 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652058 : term49 = term103.
Proof. exact (@lem2652057 term50). Qed.
Lemma lem2652060 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652061 : term106 = term107.
Proof. exact (@lem2652060 term50). Qed.
Lemma lem2652062 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652063 : term108 = term109.
Proof. exact (MK_COMB (@lem2652062) (@lem2652061)). Qed.
Lemma lem2652064 : term110 = term111.
Proof. exact (MK_COMB (@lem2652063) (@lem2652058)). Qed.
Lemma lem2652065 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2652067 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652068 : term115 = term116.
Proof. exact (@lem2652067 term50 term50). Qed.
Lemma lem2652069 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652070 : term118 = term50.
Proof. exact (EQ_MP (@lem2652069) (@lem940073)). Qed.
Lemma lem2652071 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652072 : term116 = term49.
Proof. exact (MK_COMB (@lem2652071) (@lem2652070)). Qed.
Lemma lem2652073 : term115 = term49.
Proof. exact (TRANS (@lem2652068) (@lem2652072)). Qed.
Lemma lem2652075 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652076 : term110 = term121.
Proof. exact (@lem2652075 term50 term50). Qed.
Lemma lem2652077 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652078 : term118 = term50.
Proof. exact (EQ_MP (@lem2652077) (@lem940073)). Qed.
Lemma lem2652079 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652080 : term116 = term49.
Proof. exact (MK_COMB (@lem2652079) (@lem2652078)). Qed.
Lemma lem2652081 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652082 : term121 = term106.
Proof. exact (MK_COMB (@lem2652081) (@lem2652080)). Qed.
Lemma lem2652083 : term110 = term106.
Proof. exact (TRANS (@lem2652076) (@lem2652082)). Qed.
Lemma lem2652084 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2652085 : term122 = term123.
Proof. exact (MK_COMB (@lem2652084) (@lem2652083)). Qed.
Lemma lem2652086 : term112 = term107.
Proof. exact (MK_COMB (@lem2652085) (@lem2652073)). Qed.
Lemma lem2652087 : term111 = term107.
Proof. exact (TRANS (@lem2652065) (@lem2652086)). Qed.
Lemma lem2652088 : term110 = term107.
Proof. exact (TRANS (@lem2652064) (@lem2652087)). Qed.
Lemma lem2652090 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2652091 : term107 = term106.
Proof. exact (@lem2652090 term106). Qed.
Lemma lem2652092 : term110 = term106.
Proof. exact (TRANS (@lem2652088) (@lem2652091)). Qed.
Lemma lem2652095 (x : int) : (term134 x) = (term134 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem2652096 (x : int) : (term133 x) = (term135 x).
Proof. exact (MK_COMB (@lem2652095 x) (@lem2652092)). Qed.
Lemma lem2652097 (x : int) : (term132 x) = (term135 x).
Proof. exact (TRANS (@lem2652055 x) (@lem2652096 x)). Qed.
Lemma lem2652098 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2652099 (x : int) : (term131 x) = (term136 x).
Proof. exact (MK_COMB (@lem2652098) (@lem2652097 x)). Qed.
Lemma lem2652100 (x : int) : (term136 x) = (term135 x).
Proof. exact (@lem1982721 (term135 x)). Qed.
Lemma lem2652101 (x : int) : (term131 x) = (term135 x).
Proof. exact (TRANS (@lem2652099 x) (@lem2652100 x)). Qed.
Lemma lem2652103 (x : int) : (term130 x) = (term135 x).
Proof. exact (TRANS (@lem2652054 x) (@lem2652101 x)). Qed.
Lemma lem2652104 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652105 (x : int) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem2652104) (@lem2652103 x)). Qed.
Lemma lem2652106 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652107 (x : int) : (term129 x) = (term139 x).
Proof. exact (MK_COMB (@lem2652105 x) (@lem2652106)). Qed.
Lemma lem2652108 (x : int) : (term66 x) = (term139 x).
Proof. exact (TRANS (@lem2652042 x) (@lem2652107 x)). Qed.
Lemma lem2652109 (x : int) : ((real_of_int x) = term45) = ((term140 x) = term45).
Proof. exact (@lem1988293 (real_of_int x) term45). Qed.
Lemma lem2652115 (x : int) : (term140 x) = (term141 x).
Proof. exact (@lem1982792 (real_of_int x) term45). Qed.
Lemma lem2652117 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652118 : term45 = term142.
Proof. exact (@lem2652117 (NUMERAL 0)). Qed.
Lemma lem2652120 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652121 : term106 = term107.
Proof. exact (@lem2652120 term50). Qed.
Lemma lem2652122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652123 : term108 = term109.
Proof. exact (MK_COMB (@lem2652122) (@lem2652121)). Qed.
Lemma lem2652124 : term143 = term144.
Proof. exact (MK_COMB (@lem2652123) (@lem2652118)). Qed.
Lemma lem2652125 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2652127 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652128 : term115 = term116.
Proof. exact (@lem2652127 term50 term50). Qed.
Lemma lem2652129 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652130 : term118 = term50.
Proof. exact (EQ_MP (@lem2652129) (@lem940073)). Qed.
Lemma lem2652131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652132 : term116 = term49.
Proof. exact (MK_COMB (@lem2652131) (@lem2652130)). Qed.
Lemma lem2652133 : term115 = term49.
Proof. exact (TRANS (@lem2652128) (@lem2652132)). Qed.
Lemma lem2652135 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2652136 : term143 = term45.
Proof. exact (@lem2652135 term50). Qed.
Lemma lem2652137 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2652138 : term147 = term148.
Proof. exact (MK_COMB (@lem2652137) (@lem2652136)). Qed.
Lemma lem2652139 : term145 = term142.
Proof. exact (MK_COMB (@lem2652138) (@lem2652133)). Qed.
Lemma lem2652140 : term144 = term142.
Proof. exact (TRANS (@lem2652125) (@lem2652139)). Qed.
Lemma lem2652141 : term143 = term142.
Proof. exact (TRANS (@lem2652124) (@lem2652140)). Qed.
Lemma lem2652143 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2652144 : term142 = term45.
Proof. exact (@lem2652143 term45). Qed.
Lemma lem2652145 : term143 = term45.
Proof. exact (TRANS (@lem2652141) (@lem2652144)). Qed.
Lemma lem2652146 (x : int) : (term62 x) = (term62 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem2652147 (x : int) : (term141 x) = (term149 x).
Proof. exact (MK_COMB (@lem2652146 x) (@lem2652145)). Qed.
Lemma lem2652148 (x : int) : (term149 x) = (real_of_int x).
Proof. exact (@lem1982723 (real_of_int x)). Qed.
Lemma lem2652149 (x : int) : (term141 x) = (real_of_int x).
Proof. exact (TRANS (@lem2652147 x) (@lem2652148 x)). Qed.
Lemma lem2652151 (x : int) : (term140 x) = (real_of_int x).
Proof. exact (TRANS (@lem2652115 x) (@lem2652149 x)). Qed.
Lemma lem2652152 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2652153 (x : int) : (term150 x) = (term67 x).
Proof. exact (MK_COMB (@lem2652152) (@lem2652151 x)). Qed.
Lemma lem2652154 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652155 (x : int) : ((term140 x) = term45) = ((real_of_int x) = term45).
Proof. exact (MK_COMB (@lem2652153 x) (@lem2652154)). Qed.
Lemma lem2652156 (x : int) : ((real_of_int x) = term45) = ((real_of_int x) = term45).
Proof. exact (TRANS (@lem2652109 x) (@lem2652155 x)). Qed.
Lemma lem2652157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2652158 (x : int) : (term68 x) = (term151 x).
Proof. exact (MK_COMB (@lem2652157) (@lem2652108 x)). Qed.
Lemma lem2652159 (x : int) : (term69 x) = (term152 x).
Proof. exact (MK_COMB (@lem2652158 x) (@lem2652156 x)). Qed.
Lemma lem2652160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2652161 (x : int) : (term70 x) = (term153 x).
Proof. exact (MK_COMB (@lem2652160) (@lem2652041 x)). Qed.
Lemma lem2652162 (x : int) : (term71 x) = (term154 x).
Proof. exact (MK_COMB (@lem2652161 x) (@lem2652159 x)). Qed.
Lemma lem2652163 (x : int) : (term77 x) = (term155 x).
Proof. exact (@lem1988287 term45 (real_of_int x)). Qed.
Lemma lem2652169 (x : int) : (term156 x) = (term157 x).
Proof. exact (@lem1982792 term45 (real_of_int x)). Qed.
Lemma lem2652174 (x : int) : (term157 x) = (term158 x).
Proof. exact (@lem1982721 (term158 x)). Qed.
Lemma lem2652176 (x : int) : (term156 x) = (term158 x).
Proof. exact (TRANS (@lem2652169 x) (@lem2652174 x)). Qed.
Lemma lem2652177 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652178 (x : int) : (term159 x) = (term160 x).
Proof. exact (MK_COMB (@lem2652177) (@lem2652176 x)). Qed.
Lemma lem2652179 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652180 (x : int) : (term155 x) = (term161 x).
Proof. exact (MK_COMB (@lem2652178 x) (@lem2652179)). Qed.
Lemma lem2652181 (x : int) : (term77 x) = (term161 x).
Proof. exact (TRANS (@lem2652163 x) (@lem2652180 x)). Qed.
Lemma lem2652182 (x : int) : (term81 x) = (term162 x).
Proof. exact (@lem1988287 (real_of_int x) term45). Qed.
Lemma lem2652188 (x : int) : (term140 x) = (term141 x).
Proof. exact (@lem1982792 (real_of_int x) term45). Qed.
Lemma lem2652190 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652191 : term45 = term142.
Proof. exact (@lem2652190 (NUMERAL 0)). Qed.
Lemma lem2652193 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652194 : term106 = term107.
Proof. exact (@lem2652193 term50). Qed.
Lemma lem2652195 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652196 : term108 = term109.
Proof. exact (MK_COMB (@lem2652195) (@lem2652194)). Qed.
Lemma lem2652197 : term143 = term144.
Proof. exact (MK_COMB (@lem2652196) (@lem2652191)). Qed.
Lemma lem2652198 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2652200 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652201 : term115 = term116.
Proof. exact (@lem2652200 term50 term50). Qed.
Lemma lem2652202 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652203 : term118 = term50.
Proof. exact (EQ_MP (@lem2652202) (@lem940073)). Qed.
Lemma lem2652204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652205 : term116 = term49.
Proof. exact (MK_COMB (@lem2652204) (@lem2652203)). Qed.
Lemma lem2652206 : term115 = term49.
Proof. exact (TRANS (@lem2652201) (@lem2652205)). Qed.
Lemma lem2652208 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2652209 : term143 = term45.
Proof. exact (@lem2652208 term50). Qed.
Lemma lem2652210 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2652211 : term147 = term148.
Proof. exact (MK_COMB (@lem2652210) (@lem2652209)). Qed.
Lemma lem2652212 : term145 = term142.
Proof. exact (MK_COMB (@lem2652211) (@lem2652206)). Qed.
Lemma lem2652213 : term144 = term142.
Proof. exact (TRANS (@lem2652198) (@lem2652212)). Qed.
Lemma lem2652214 : term143 = term142.
Proof. exact (TRANS (@lem2652197) (@lem2652213)). Qed.
Lemma lem2652216 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2652217 : term142 = term45.
Proof. exact (@lem2652216 term45). Qed.
Lemma lem2652218 : term143 = term45.
Proof. exact (TRANS (@lem2652214) (@lem2652217)). Qed.
Lemma lem2652219 (x : int) : (term62 x) = (term62 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem2652220 (x : int) : (term141 x) = (term149 x).
Proof. exact (MK_COMB (@lem2652219 x) (@lem2652218)). Qed.
Lemma lem2652221 (x : int) : (term149 x) = (real_of_int x).
Proof. exact (@lem1982723 (real_of_int x)). Qed.
Lemma lem2652222 (x : int) : (term141 x) = (real_of_int x).
Proof. exact (TRANS (@lem2652220 x) (@lem2652221 x)). Qed.
Lemma lem2652224 (x : int) : (term140 x) = (real_of_int x).
Proof. exact (TRANS (@lem2652188 x) (@lem2652222 x)). Qed.
Lemma lem2652225 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652226 (x : int) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem2652225) (@lem2652224 x)). Qed.
Lemma lem2652227 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652228 (x : int) : (term162 x) = (term165 x).
Proof. exact (MK_COMB (@lem2652226 x) (@lem2652227)). Qed.
Lemma lem2652229 (x : int) : (term81 x) = (term165 x).
Proof. exact (TRANS (@lem2652182 x) (@lem2652228 x)). Qed.
Lemma lem2652230 (x : int) : (term66 x) = (term129 x).
Proof. exact (@lem1988287 term45 (term63 x)). Qed.
Lemma lem2652242 (x : int) : (term130 x) = (term131 x).
Proof. exact (@lem1982792 term45 (term63 x)). Qed.
Lemma lem2652243 (x : int) : (term132 x) = (term133 x).
Proof. exact (@lem1982781 (real_of_int x) term106 term49). Qed.
Lemma lem2652245 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652246 : term49 = term103.
Proof. exact (@lem2652245 term50). Qed.
Lemma lem2652248 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652249 : term106 = term107.
Proof. exact (@lem2652248 term50). Qed.
Lemma lem2652250 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652251 : term108 = term109.
Proof. exact (MK_COMB (@lem2652250) (@lem2652249)). Qed.
Lemma lem2652252 : term110 = term111.
Proof. exact (MK_COMB (@lem2652251) (@lem2652246)). Qed.
Lemma lem2652253 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2652255 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652256 : term115 = term116.
Proof. exact (@lem2652255 term50 term50). Qed.
Lemma lem2652257 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652258 : term118 = term50.
Proof. exact (EQ_MP (@lem2652257) (@lem940073)). Qed.
Lemma lem2652259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652260 : term116 = term49.
Proof. exact (MK_COMB (@lem2652259) (@lem2652258)). Qed.
Lemma lem2652261 : term115 = term49.
Proof. exact (TRANS (@lem2652256) (@lem2652260)). Qed.
Lemma lem2652263 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652264 : term110 = term121.
Proof. exact (@lem2652263 term50 term50). Qed.
Lemma lem2652265 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652266 : term118 = term50.
Proof. exact (EQ_MP (@lem2652265) (@lem940073)). Qed.
Lemma lem2652267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652268 : term116 = term49.
Proof. exact (MK_COMB (@lem2652267) (@lem2652266)). Qed.
Lemma lem2652269 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652270 : term121 = term106.
Proof. exact (MK_COMB (@lem2652269) (@lem2652268)). Qed.
Lemma lem2652271 : term110 = term106.
Proof. exact (TRANS (@lem2652264) (@lem2652270)). Qed.
Lemma lem2652272 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2652273 : term122 = term123.
Proof. exact (MK_COMB (@lem2652272) (@lem2652271)). Qed.
Lemma lem2652274 : term112 = term107.
Proof. exact (MK_COMB (@lem2652273) (@lem2652261)). Qed.
Lemma lem2652275 : term111 = term107.
Proof. exact (TRANS (@lem2652253) (@lem2652274)). Qed.
Lemma lem2652276 : term110 = term107.
Proof. exact (TRANS (@lem2652252) (@lem2652275)). Qed.
Lemma lem2652278 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2652279 : term107 = term106.
Proof. exact (@lem2652278 term106). Qed.
Lemma lem2652280 : term110 = term106.
Proof. exact (TRANS (@lem2652276) (@lem2652279)). Qed.
Lemma lem2652283 (x : int) : (term134 x) = (term134 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem2652284 (x : int) : (term133 x) = (term135 x).
Proof. exact (MK_COMB (@lem2652283 x) (@lem2652280)). Qed.
Lemma lem2652285 (x : int) : (term132 x) = (term135 x).
Proof. exact (TRANS (@lem2652243 x) (@lem2652284 x)). Qed.
Lemma lem2652286 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2652287 (x : int) : (term131 x) = (term136 x).
Proof. exact (MK_COMB (@lem2652286) (@lem2652285 x)). Qed.
Lemma lem2652288 (x : int) : (term136 x) = (term135 x).
Proof. exact (@lem1982721 (term135 x)). Qed.
Lemma lem2652289 (x : int) : (term131 x) = (term135 x).
Proof. exact (TRANS (@lem2652287 x) (@lem2652288 x)). Qed.
Lemma lem2652291 (x : int) : (term130 x) = (term135 x).
Proof. exact (TRANS (@lem2652242 x) (@lem2652289 x)). Qed.
Lemma lem2652292 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652293 (x : int) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem2652292) (@lem2652291 x)). Qed.
Lemma lem2652294 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652295 (x : int) : (term129 x) = (term139 x).
Proof. exact (MK_COMB (@lem2652293 x) (@lem2652294)). Qed.
Lemma lem2652296 (x : int) : (term66 x) = (term139 x).
Proof. exact (TRANS (@lem2652230 x) (@lem2652295 x)). Qed.
Lemma lem2652297 (x : int) : (term54 x) = (term97 x).
Proof. exact (@lem1988287 (real_of_int x) term51). Qed.
Lemma lem2652304 : term51 = term49.
Proof. exact (@lem1982721 term49). Qed.
Lemma lem2652307 (x : int) : (term98 x) = (term98 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem2652308 (x : int) : (term99 x) = (term100 x).
Proof. exact (MK_COMB (@lem2652307 x) (@lem2652304)). Qed.
Lemma lem2652309 (x : int) : (term100 x) = (term101 x).
Proof. exact (@lem1982792 (real_of_int x) term49). Qed.
Lemma lem2652311 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652312 : term49 = term103.
Proof. exact (@lem2652311 term50). Qed.
Lemma lem2652314 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652315 : term106 = term107.
Proof. exact (@lem2652314 term50). Qed.
Lemma lem2652316 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652317 : term108 = term109.
Proof. exact (MK_COMB (@lem2652316) (@lem2652315)). Qed.
Lemma lem2652318 : term110 = term111.
Proof. exact (MK_COMB (@lem2652317) (@lem2652312)). Qed.
Lemma lem2652319 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2652321 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652322 : term115 = term116.
Proof. exact (@lem2652321 term50 term50). Qed.
Lemma lem2652323 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652324 : term118 = term50.
Proof. exact (EQ_MP (@lem2652323) (@lem940073)). Qed.
Lemma lem2652325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652326 : term116 = term49.
Proof. exact (MK_COMB (@lem2652325) (@lem2652324)). Qed.
Lemma lem2652327 : term115 = term49.
Proof. exact (TRANS (@lem2652322) (@lem2652326)). Qed.
Lemma lem2652329 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652330 : term110 = term121.
Proof. exact (@lem2652329 term50 term50). Qed.
Lemma lem2652331 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652332 : term118 = term50.
Proof. exact (EQ_MP (@lem2652331) (@lem940073)). Qed.
Lemma lem2652333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652334 : term116 = term49.
Proof. exact (MK_COMB (@lem2652333) (@lem2652332)). Qed.
Lemma lem2652335 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652336 : term121 = term106.
Proof. exact (MK_COMB (@lem2652335) (@lem2652334)). Qed.
Lemma lem2652337 : term110 = term106.
Proof. exact (TRANS (@lem2652330) (@lem2652336)). Qed.
Lemma lem2652338 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2652339 : term122 = term123.
Proof. exact (MK_COMB (@lem2652338) (@lem2652337)). Qed.
Lemma lem2652340 : term112 = term107.
Proof. exact (MK_COMB (@lem2652339) (@lem2652327)). Qed.
Lemma lem2652341 : term111 = term107.
Proof. exact (TRANS (@lem2652319) (@lem2652340)). Qed.
Lemma lem2652342 : term110 = term107.
Proof. exact (TRANS (@lem2652318) (@lem2652341)). Qed.
Lemma lem2652344 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2652345 : term107 = term106.
Proof. exact (@lem2652344 term106). Qed.
Lemma lem2652346 : term110 = term106.
Proof. exact (TRANS (@lem2652342) (@lem2652345)). Qed.
Lemma lem2652347 (x : int) : (term62 x) = (term62 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem2652350 (x : int) : (term101 x) = (term125 x).
Proof. exact (MK_COMB (@lem2652347 x) (@lem2652346)). Qed.
Lemma lem2652351 (x : int) : (term100 x) = (term125 x).
Proof. exact (TRANS (@lem2652309 x) (@lem2652350 x)). Qed.
Lemma lem2652352 (x : int) : (term99 x) = (term125 x).
Proof. exact (TRANS (@lem2652308 x) (@lem2652351 x)). Qed.
Lemma lem2652353 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652354 (x : int) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem2652353) (@lem2652352 x)). Qed.
Lemma lem2652355 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652356 (x : int) : (term97 x) = (term128 x).
Proof. exact (MK_COMB (@lem2652354 x) (@lem2652355)). Qed.
Lemma lem2652357 (x : int) : (term54 x) = (term128 x).
Proof. exact (TRANS (@lem2652297 x) (@lem2652356 x)). Qed.
Lemma lem2652358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2652359 (x : int) : (term68 x) = (term151 x).
Proof. exact (MK_COMB (@lem2652358) (@lem2652296 x)). Qed.
Lemma lem2652360 (x : int) : (term86 x) = (term166 x).
Proof. exact (MK_COMB (@lem2652359 x) (@lem2652357 x)). Qed.
Lemma lem2652361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2652362 (x : int) : (term88 x) = (term167 x).
Proof. exact (MK_COMB (@lem2652361) (@lem2652229 x)). Qed.
Lemma lem2652363 (x : int) : (term89 x) = (term168 x).
Proof. exact (MK_COMB (@lem2652362 x) (@lem2652360 x)). Qed.
Lemma lem2652364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2652365 (x : int) : (term91 x) = (term169 x).
Proof. exact (MK_COMB (@lem2652364) (@lem2652181 x)). Qed.
Lemma lem2652366 (x : int) : (term92 x) = (term170 x).
Proof. exact (MK_COMB (@lem2652365 x) (@lem2652363 x)). Qed.
Lemma lem2652367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2652368 (x : int) : (term93 x) = (term171 x).
Proof. exact (MK_COMB (@lem2652367) (@lem2652162 x)). Qed.
Lemma lem2652369 (x : int) : (term94 x) = (term172 x).
Proof. exact (MK_COMB (@lem2652368 x) (@lem2652366 x)). Qed.
Lemma lem2652376 (x : int) : (term96 x) = (term172 x).
Proof. exact (TRANS (@lem2651980 x) (@lem2652369 x)). Qed.
Lemma lem2652393 (x : int) : (term168 x) = (term173 x).
Proof. exact (@lem19158 (term139 x) (term165 x) (term128 x)). Qed.
Lemma lem2652396 (x : int) : (term169 x) = (term169 x).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem2652397 (x : int) : (term170 x) = (term174 x).
Proof. exact (MK_COMB (@lem2652396 x) (@lem2652393 x)). Qed.
Lemma lem2652404 (x : int) : (term174 x) = (term175 x).
Proof. exact (@lem19158 (term176 x) (term161 x) (term177 x)). Qed.
Lemma lem2652405 (x : int) : (term170 x) = (term175 x).
Proof. exact (TRANS (@lem2652397 x) (@lem2652404 x)). Qed.
Lemma lem2652422 (x : int) : (term154 x) = (term178 x).
Proof. exact (@lem19158 (term139 x) (term128 x) ((real_of_int x) = term45)). Qed.
Lemma lem2652423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2652424 (x : int) : (term171 x) = (term179 x).
Proof. exact (MK_COMB (@lem2652423) (@lem2652422 x)). Qed.
Lemma lem2652425 (x : int) : (term172 x) = (term180 x).
Proof. exact (MK_COMB (@lem2652424 x) (@lem2652405 x)). Qed.
Lemma lem2652426 (x : int) : (term96 x) = (term180 x).
Proof. exact (TRANS (@lem2652376 x) (@lem2652425 x)). Qed.
Lemma lem2652448 (x : int) (h1 : term180 x) : term180 x.
Proof. exact (h1). Qed.
Lemma lem2652449 (x : int) (h1 : term178 x) : term178 x.
Proof. exact (h1). Qed.
Lemma lem2652450 (x : int) (h1 : term181 x) : term181 x.
Proof. exact (h1). Qed.
Lemma lem2652451 (x : int) (h1 : term181 x) : term139 x.
Proof. exact (proj2 (@lem2652450 x h1)). Qed.
Lemma lem2652452 (x : int) (h1 : term181 x) : term128 x.
Proof. exact (proj1 (@lem2652450 x h1)). Qed.
Lemma lem2652454 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2652455 : term182 = term183.
Proof. exact (@lem2652454 term45 term49). Qed.
Lemma lem2652457 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652458 : term49 = term103.
Proof. exact (@lem2652457 term50). Qed.
Lemma lem2652460 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652461 : term45 = term142.
Proof. exact (@lem2652460 (NUMERAL 0)). Qed.
Lemma lem2652462 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2652463 : term184 = term185.
Proof. exact (MK_COMB (@lem2652462) (@lem2652461)). Qed.
Lemma lem2652464 : term183 = term186.
Proof. exact (MK_COMB (@lem2652463) (@lem2652458)). Qed.
Lemma lem2652465 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2652467 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652468 : term183 = term189.
Proof. exact (@lem2652467 (NUMERAL 0) term50). Qed.
Lemma lem2652469 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652470 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652471 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652470 h1) (fun h1 : term189 = True => @lem2652469)). Qed.
Lemma lem2652472 : term189 = True.
Proof. exact (EQ_MP (@lem2652471) (@lem2652469)). Qed.
Lemma lem2652473 : term183 = True.
Proof. exact (TRANS (@lem2652468) (@lem2652472)). Qed.
Lemma lem2652474 : True = term183.
Proof. exact (SYM (@lem2652473)). Qed.
Lemma lem2652475 : term183.
Proof. exact (EQ_MP (@lem2652474) (@lem0)). Qed.
Lemma lem2652476 : term191.
Proof. exact (@lem2652465 (@lem2652475)). Qed.
Lemma lem2652478 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652479 : term183 = term189.
Proof. exact (@lem2652478 (NUMERAL 0) term50). Qed.
Lemma lem2652480 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652481 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652482 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652481 h1) (fun h1 : term189 = True => @lem2652480)). Qed.
Lemma lem2652483 : term189 = True.
Proof. exact (EQ_MP (@lem2652482) (@lem2652480)). Qed.
Lemma lem2652484 : term183 = True.
Proof. exact (TRANS (@lem2652479) (@lem2652483)). Qed.
Lemma lem2652485 : True = term183.
Proof. exact (SYM (@lem2652484)). Qed.
Lemma lem2652486 : term183.
Proof. exact (EQ_MP (@lem2652485) (@lem0)). Qed.
Lemma lem2652487 : term186 = term192.
Proof. exact (@lem2652476 (@lem2652486)). Qed.
Lemma lem2652489 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652490 : term115 = term116.
Proof. exact (@lem2652489 term50 term50). Qed.
Lemma lem2652491 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652492 : term118 = term50.
Proof. exact (EQ_MP (@lem2652491) (@lem940073)). Qed.
Lemma lem2652493 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652494 : term116 = term49.
Proof. exact (MK_COMB (@lem2652493) (@lem2652492)). Qed.
Lemma lem2652495 : term115 = term49.
Proof. exact (TRANS (@lem2652490) (@lem2652494)). Qed.
Lemma lem2652497 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2652498 : term194 = term45.
Proof. exact (@lem2652497 term50). Qed.
Lemma lem2652499 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2652500 : term195 = term184.
Proof. exact (MK_COMB (@lem2652499) (@lem2652498)). Qed.
Lemma lem2652501 : term192 = term183.
Proof. exact (MK_COMB (@lem2652500) (@lem2652495)). Qed.
Lemma lem2652503 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652504 : term183 = term189.
Proof. exact (@lem2652503 (NUMERAL 0) term50). Qed.
Lemma lem2652505 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652506 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652507 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652506 h1) (fun h1 : term189 = True => @lem2652505)). Qed.
Lemma lem2652508 : term189 = True.
Proof. exact (EQ_MP (@lem2652507) (@lem2652505)). Qed.
Lemma lem2652509 : term183 = True.
Proof. exact (TRANS (@lem2652504) (@lem2652508)). Qed.
Lemma lem2652510 : term192 = True.
Proof. exact (TRANS (@lem2652501) (@lem2652509)). Qed.
Lemma lem2652511 : term186 = True.
Proof. exact (TRANS (@lem2652487) (@lem2652510)). Qed.
Lemma lem2652512 : term183 = True.
Proof. exact (TRANS (@lem2652464) (@lem2652511)). Qed.
Lemma lem2652513 : term182 = True.
Proof. exact (TRANS (@lem2652455) (@lem2652512)). Qed.
Lemma lem2652514 : True = term182.
Proof. exact (SYM (@lem2652513)). Qed.
Lemma lem2652515 : term182.
Proof. exact (EQ_MP (@lem2652514) (@lem0)). Qed.
Lemma lem2652516 (x : int) (h1 : term181 x) : term196 x.
Proof. exact (conj (@lem2652515) (@lem2652452 x h1)). Qed.
Lemma lem2652518 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2652519 (x : int) : term198 x.
Proof. exact (@lem2652518 term49 (term125 x)). Qed.
Lemma lem2652520 (x : int) (h1 : term181 x) : term199 x.
Proof. exact (@lem2652519 x (@lem2652516 x h1)). Qed.
Lemma lem2652521 (x : int) : (term200 x) = (term125 x).
Proof. exact (@lem1982733 (term125 x)). Qed.
Lemma lem2652522 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652523 (x : int) : (term201 x) = (term127 x).
Proof. exact (MK_COMB (@lem2652522) (@lem2652521 x)). Qed.
Lemma lem2652524 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652525 (x : int) : (term199 x) = (term128 x).
Proof. exact (MK_COMB (@lem2652523 x) (@lem2652524)). Qed.
Lemma lem2652526 (x : int) (h1 : term181 x) : term128 x.
Proof. exact (EQ_MP (@lem2652525 x) (@lem2652520 x h1)). Qed.
Lemma lem2652528 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2652529 : term182 = term183.
Proof. exact (@lem2652528 term45 term49). Qed.
Lemma lem2652531 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652532 : term49 = term103.
Proof. exact (@lem2652531 term50). Qed.
Lemma lem2652534 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652535 : term45 = term142.
Proof. exact (@lem2652534 (NUMERAL 0)). Qed.
Lemma lem2652536 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2652537 : term184 = term185.
Proof. exact (MK_COMB (@lem2652536) (@lem2652535)). Qed.
Lemma lem2652538 : term183 = term186.
Proof. exact (MK_COMB (@lem2652537) (@lem2652532)). Qed.
Lemma lem2652539 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2652541 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652542 : term183 = term189.
Proof. exact (@lem2652541 (NUMERAL 0) term50). Qed.
Lemma lem2652543 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652544 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652545 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652544 h1) (fun h1 : term189 = True => @lem2652543)). Qed.
Lemma lem2652546 : term189 = True.
Proof. exact (EQ_MP (@lem2652545) (@lem2652543)). Qed.
Lemma lem2652547 : term183 = True.
Proof. exact (TRANS (@lem2652542) (@lem2652546)). Qed.
Lemma lem2652548 : True = term183.
Proof. exact (SYM (@lem2652547)). Qed.
Lemma lem2652549 : term183.
Proof. exact (EQ_MP (@lem2652548) (@lem0)). Qed.
Lemma lem2652550 : term191.
Proof. exact (@lem2652539 (@lem2652549)). Qed.
Lemma lem2652552 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652553 : term183 = term189.
Proof. exact (@lem2652552 (NUMERAL 0) term50). Qed.
Lemma lem2652554 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652555 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652556 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652555 h1) (fun h1 : term189 = True => @lem2652554)). Qed.
Lemma lem2652557 : term189 = True.
Proof. exact (EQ_MP (@lem2652556) (@lem2652554)). Qed.
Lemma lem2652558 : term183 = True.
Proof. exact (TRANS (@lem2652553) (@lem2652557)). Qed.
Lemma lem2652559 : True = term183.
Proof. exact (SYM (@lem2652558)). Qed.
Lemma lem2652560 : term183.
Proof. exact (EQ_MP (@lem2652559) (@lem0)). Qed.
Lemma lem2652561 : term186 = term192.
Proof. exact (@lem2652550 (@lem2652560)). Qed.
Lemma lem2652563 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652564 : term115 = term116.
Proof. exact (@lem2652563 term50 term50). Qed.
Lemma lem2652565 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652566 : term118 = term50.
Proof. exact (EQ_MP (@lem2652565) (@lem940073)). Qed.
Lemma lem2652567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652568 : term116 = term49.
Proof. exact (MK_COMB (@lem2652567) (@lem2652566)). Qed.
Lemma lem2652569 : term115 = term49.
Proof. exact (TRANS (@lem2652564) (@lem2652568)). Qed.
Lemma lem2652571 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2652572 : term194 = term45.
Proof. exact (@lem2652571 term50). Qed.
Lemma lem2652573 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2652574 : term195 = term184.
Proof. exact (MK_COMB (@lem2652573) (@lem2652572)). Qed.
Lemma lem2652575 : term192 = term183.
Proof. exact (MK_COMB (@lem2652574) (@lem2652569)). Qed.
Lemma lem2652577 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652578 : term183 = term189.
Proof. exact (@lem2652577 (NUMERAL 0) term50). Qed.
Lemma lem2652579 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652580 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652581 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652580 h1) (fun h1 : term189 = True => @lem2652579)). Qed.
Lemma lem2652582 : term189 = True.
Proof. exact (EQ_MP (@lem2652581) (@lem2652579)). Qed.
Lemma lem2652583 : term183 = True.
Proof. exact (TRANS (@lem2652578) (@lem2652582)). Qed.
Lemma lem2652584 : term192 = True.
Proof. exact (TRANS (@lem2652575) (@lem2652583)). Qed.
Lemma lem2652585 : term186 = True.
Proof. exact (TRANS (@lem2652561) (@lem2652584)). Qed.
Lemma lem2652586 : term183 = True.
Proof. exact (TRANS (@lem2652538) (@lem2652585)). Qed.
Lemma lem2652587 : term182 = True.
Proof. exact (TRANS (@lem2652529) (@lem2652586)). Qed.
Lemma lem2652588 : True = term182.
Proof. exact (SYM (@lem2652587)). Qed.
Lemma lem2652589 : term182.
Proof. exact (EQ_MP (@lem2652588) (@lem0)). Qed.
Lemma lem2652590 (x : int) (h1 : term181 x) : term202 x.
Proof. exact (conj (@lem2652589) (@lem2652451 x h1)). Qed.
Lemma lem2652592 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2652593 (x : int) : term203 x.
Proof. exact (@lem2652592 term49 (term135 x)). Qed.
Lemma lem2652594 (x : int) (h1 : term181 x) : term204 x.
Proof. exact (@lem2652593 x (@lem2652590 x h1)). Qed.
Lemma lem2652595 (x : int) : (term205 x) = (term135 x).
Proof. exact (@lem1982733 (term135 x)). Qed.
Lemma lem2652596 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652597 (x : int) : (term206 x) = (term138 x).
Proof. exact (MK_COMB (@lem2652596) (@lem2652595 x)). Qed.
Lemma lem2652598 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652599 (x : int) : (term204 x) = (term139 x).
Proof. exact (MK_COMB (@lem2652597 x) (@lem2652598)). Qed.
Lemma lem2652600 (x : int) (h1 : term181 x) : term139 x.
Proof. exact (EQ_MP (@lem2652599 x) (@lem2652594 x h1)). Qed.
Lemma lem2652601 (x : int) (h1 : term181 x) : term207 x.
Proof. exact (conj (@lem2652600 x h1) (@lem2652526 x h1)). Qed.
Lemma lem2652603 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2652604 (x : int) : term209 x.
Proof. exact (@lem2652603 (term135 x) (term125 x)). Qed.
Lemma lem2652605 (x : int) (h1 : term181 x) : term210 x.
Proof. exact (@lem2652604 x (@lem2652601 x h1)). Qed.
Lemma lem2652606 (x : int) : (term211 x) = (term212 x).
Proof. exact (@lem1982753 (term158 x) (real_of_int x) term106 term106). Qed.
Lemma lem2652607 (x : int) : (term213 x) = (term214 x).
Proof. exact (@lem1982713 term106 (real_of_int x)). Qed.
Lemma lem2652609 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652610 : term49 = term103.
Proof. exact (@lem2652609 term50). Qed.
Lemma lem2652612 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652613 : term106 = term107.
Proof. exact (@lem2652612 term50). Qed.
Lemma lem2652614 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2652615 : term215 = term216.
Proof. exact (MK_COMB (@lem2652614) (@lem2652613)). Qed.
Lemma lem2652616 : term217 = term218.
Proof. exact (MK_COMB (@lem2652615) (@lem2652610)). Qed.
Lemma lem2652617 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2652619 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652620 : term183 = term189.
Proof. exact (@lem2652619 (NUMERAL 0) term50). Qed.
Lemma lem2652621 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652622 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652623 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652622 h1) (fun h1 : term189 = True => @lem2652621)). Qed.
Lemma lem2652624 : term189 = True.
Proof. exact (EQ_MP (@lem2652623) (@lem2652621)). Qed.
Lemma lem2652625 : term183 = True.
Proof. exact (TRANS (@lem2652620) (@lem2652624)). Qed.
Lemma lem2652626 : True = term183.
Proof. exact (SYM (@lem2652625)). Qed.
Lemma lem2652627 : term183.
Proof. exact (EQ_MP (@lem2652626) (@lem0)). Qed.
Lemma lem2652628 : term220.
Proof. exact (@lem2652617 (@lem2652627)). Qed.
Lemma lem2652630 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652631 : term183 = term189.
Proof. exact (@lem2652630 (NUMERAL 0) term50). Qed.
Lemma lem2652632 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652633 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652634 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652633 h1) (fun h1 : term189 = True => @lem2652632)). Qed.
Lemma lem2652635 : term189 = True.
Proof. exact (EQ_MP (@lem2652634) (@lem2652632)). Qed.
Lemma lem2652636 : term183 = True.
Proof. exact (TRANS (@lem2652631) (@lem2652635)). Qed.
Lemma lem2652637 : True = term183.
Proof. exact (SYM (@lem2652636)). Qed.
Lemma lem2652638 : term183.
Proof. exact (EQ_MP (@lem2652637) (@lem0)). Qed.
Lemma lem2652639 : term221.
Proof. exact (@lem2652628 (@lem2652638)). Qed.
Lemma lem2652641 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652642 : term183 = term189.
Proof. exact (@lem2652641 (NUMERAL 0) term50). Qed.
Lemma lem2652643 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652644 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652645 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652644 h1) (fun h1 : term189 = True => @lem2652643)). Qed.
Lemma lem2652646 : term189 = True.
Proof. exact (EQ_MP (@lem2652645) (@lem2652643)). Qed.
Lemma lem2652647 : term183 = True.
Proof. exact (TRANS (@lem2652642) (@lem2652646)). Qed.
Lemma lem2652648 : True = term183.
Proof. exact (SYM (@lem2652647)). Qed.
Lemma lem2652649 : term183.
Proof. exact (EQ_MP (@lem2652648) (@lem0)). Qed.
Lemma lem2652650 : term222.
Proof. exact (@lem2652639 (@lem2652649)). Qed.
Lemma lem2652652 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652653 : term115 = term116.
Proof. exact (@lem2652652 term50 term50). Qed.
Lemma lem2652654 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652655 : term118 = term50.
Proof. exact (EQ_MP (@lem2652654) (@lem940073)). Qed.
Lemma lem2652656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652657 : term116 = term49.
Proof. exact (MK_COMB (@lem2652656) (@lem2652655)). Qed.
Lemma lem2652658 : term115 = term49.
Proof. exact (TRANS (@lem2652653) (@lem2652657)). Qed.
Lemma lem2652660 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652661 : term110 = term121.
Proof. exact (@lem2652660 term50 term50). Qed.
Lemma lem2652662 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652663 : term118 = term50.
Proof. exact (EQ_MP (@lem2652662) (@lem940073)). Qed.
Lemma lem2652664 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652665 : term116 = term49.
Proof. exact (MK_COMB (@lem2652664) (@lem2652663)). Qed.
Lemma lem2652666 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652667 : term121 = term106.
Proof. exact (MK_COMB (@lem2652666) (@lem2652665)). Qed.
Lemma lem2652668 : term110 = term106.
Proof. exact (TRANS (@lem2652661) (@lem2652667)). Qed.
Lemma lem2652669 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2652670 : term223 = term215.
Proof. exact (MK_COMB (@lem2652669) (@lem2652668)). Qed.
Lemma lem2652671 : term224 = term217.
Proof. exact (MK_COMB (@lem2652670) (@lem2652658)). Qed.
Lemma lem2652673 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2652674 : term217 = term45.
Proof. exact (@lem2652673 term50). Qed.
Lemma lem2652675 : term224 = term45.
Proof. exact (TRANS (@lem2652671) (@lem2652674)). Qed.
Lemma lem2652676 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652677 : term226 = term227.
Proof. exact (MK_COMB (@lem2652676) (@lem2652675)). Qed.
Lemma lem2652678 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2652679 : term228 = term194.
Proof. exact (MK_COMB (@lem2652677) (@lem2652678)). Qed.
Lemma lem2652681 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2652682 : term194 = term45.
Proof. exact (@lem2652681 term50). Qed.
Lemma lem2652683 : term228 = term45.
Proof. exact (TRANS (@lem2652679) (@lem2652682)). Qed.
Lemma lem2652685 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652686 : term115 = term116.
Proof. exact (@lem2652685 term50 term50). Qed.
Lemma lem2652687 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652688 : term118 = term50.
Proof. exact (EQ_MP (@lem2652687) (@lem940073)). Qed.
Lemma lem2652689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652690 : term116 = term49.
Proof. exact (MK_COMB (@lem2652689) (@lem2652688)). Qed.
Lemma lem2652691 : term115 = term49.
Proof. exact (TRANS (@lem2652686) (@lem2652690)). Qed.
Lemma lem2652692 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2652693 : term229 = term194.
Proof. exact (MK_COMB (@lem2652692) (@lem2652691)). Qed.
Lemma lem2652695 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2652696 : term194 = term45.
Proof. exact (@lem2652695 term50). Qed.
Lemma lem2652697 : term229 = term45.
Proof. exact (TRANS (@lem2652693) (@lem2652696)). Qed.
Lemma lem2652698 : term45 = term229.
Proof. exact (SYM (@lem2652697)). Qed.
Lemma lem2652699 : term228 = term229.
Proof. exact (TRANS (@lem2652683) (@lem2652698)). Qed.
Lemma lem2652700 : term218 = term142.
Proof. exact (@lem2652650 (@lem2652699)). Qed.
Lemma lem2652701 : term217 = term142.
Proof. exact (TRANS (@lem2652616) (@lem2652700)). Qed.
Lemma lem2652703 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2652704 : term142 = term45.
Proof. exact (@lem2652703 term45). Qed.
Lemma lem2652705 : term217 = term45.
Proof. exact (TRANS (@lem2652701) (@lem2652704)). Qed.
Lemma lem2652706 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652707 : term230 = term227.
Proof. exact (MK_COMB (@lem2652706) (@lem2652705)). Qed.
Lemma lem2652708 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2652709 (x : int) : (term214 x) = (term231 x).
Proof. exact (MK_COMB (@lem2652707) (@lem2652708 x)). Qed.
Lemma lem2652710 (x : int) : (term213 x) = (term231 x).
Proof. exact (TRANS (@lem2652607 x) (@lem2652709 x)). Qed.
Lemma lem2652711 (x : int) : (term231 x) = term45.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2652712 (x : int) : (term213 x) = term45.
Proof. exact (TRANS (@lem2652710 x) (@lem2652711 x)). Qed.
Lemma lem2652713 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2652714 (x : int) : (term232 x) = term47.
Proof. exact (MK_COMB (@lem2652713) (@lem2652712 x)). Qed.
Lemma lem2652716 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652717 : term106 = term107.
Proof. exact (@lem2652716 term50). Qed.
Lemma lem2652719 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652720 : term106 = term107.
Proof. exact (@lem2652719 term50). Qed.
Lemma lem2652721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2652722 : term215 = term216.
Proof. exact (MK_COMB (@lem2652721) (@lem2652720)). Qed.
Lemma lem2652723 : term233 = term234.
Proof. exact (MK_COMB (@lem2652722) (@lem2652717)). Qed.
Lemma lem2652724 : term235.
Proof. exact (@lem1981473 term106 term49 term106 term49 term236 term49). Qed.
Lemma lem2652726 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652727 : term183 = term189.
Proof. exact (@lem2652726 (NUMERAL 0) term50). Qed.
Lemma lem2652728 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652729 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652730 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652729 h1) (fun h1 : term189 = True => @lem2652728)). Qed.
Lemma lem2652731 : term189 = True.
Proof. exact (EQ_MP (@lem2652730) (@lem2652728)). Qed.
Lemma lem2652732 : term183 = True.
Proof. exact (TRANS (@lem2652727) (@lem2652731)). Qed.
Lemma lem2652733 : True = term183.
Proof. exact (SYM (@lem2652732)). Qed.
Lemma lem2652734 : term183.
Proof. exact (EQ_MP (@lem2652733) (@lem0)). Qed.
Lemma lem2652735 : term237.
Proof. exact (@lem2652724 (@lem2652734)). Qed.
Lemma lem2652737 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652738 : term183 = term189.
Proof. exact (@lem2652737 (NUMERAL 0) term50). Qed.
Lemma lem2652739 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652740 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652741 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652740 h1) (fun h1 : term189 = True => @lem2652739)). Qed.
Lemma lem2652742 : term189 = True.
Proof. exact (EQ_MP (@lem2652741) (@lem2652739)). Qed.
Lemma lem2652743 : term183 = True.
Proof. exact (TRANS (@lem2652738) (@lem2652742)). Qed.
Lemma lem2652744 : True = term183.
Proof. exact (SYM (@lem2652743)). Qed.
Lemma lem2652745 : term183.
Proof. exact (EQ_MP (@lem2652744) (@lem0)). Qed.
Lemma lem2652746 : term238.
Proof. exact (@lem2652735 (@lem2652745)). Qed.
Lemma lem2652748 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652749 : term183 = term189.
Proof. exact (@lem2652748 (NUMERAL 0) term50). Qed.
Lemma lem2652750 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652751 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652752 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652751 h1) (fun h1 : term189 = True => @lem2652750)). Qed.
Lemma lem2652753 : term189 = True.
Proof. exact (EQ_MP (@lem2652752) (@lem2652750)). Qed.
Lemma lem2652754 : term183 = True.
Proof. exact (TRANS (@lem2652749) (@lem2652753)). Qed.
Lemma lem2652755 : True = term183.
Proof. exact (SYM (@lem2652754)). Qed.
Lemma lem2652756 : term183.
Proof. exact (EQ_MP (@lem2652755) (@lem0)). Qed.
Lemma lem2652757 : term239.
Proof. exact (@lem2652746 (@lem2652756)). Qed.
Lemma lem2652759 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652760 : term110 = term121.
Proof. exact (@lem2652759 term50 term50). Qed.
Lemma lem2652761 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652762 : term118 = term50.
Proof. exact (EQ_MP (@lem2652761) (@lem940073)). Qed.
Lemma lem2652763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652764 : term116 = term49.
Proof. exact (MK_COMB (@lem2652763) (@lem2652762)). Qed.
Lemma lem2652765 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652766 : term121 = term106.
Proof. exact (MK_COMB (@lem2652765) (@lem2652764)). Qed.
Lemma lem2652767 : term110 = term106.
Proof. exact (TRANS (@lem2652760) (@lem2652766)). Qed.
Lemma lem2652769 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652770 : term110 = term121.
Proof. exact (@lem2652769 term50 term50). Qed.
Lemma lem2652771 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652772 : term118 = term50.
Proof. exact (EQ_MP (@lem2652771) (@lem940073)). Qed.
Lemma lem2652773 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652774 : term116 = term49.
Proof. exact (MK_COMB (@lem2652773) (@lem2652772)). Qed.
Lemma lem2652775 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652776 : term121 = term106.
Proof. exact (MK_COMB (@lem2652775) (@lem2652774)). Qed.
Lemma lem2652777 : term110 = term106.
Proof. exact (TRANS (@lem2652770) (@lem2652776)). Qed.
Lemma lem2652778 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2652779 : term223 = term215.
Proof. exact (MK_COMB (@lem2652778) (@lem2652777)). Qed.
Lemma lem2652780 : term240 = term233.
Proof. exact (MK_COMB (@lem2652779) (@lem2652767)). Qed.
Lemma lem2652781 : term233 = term241.
Proof. exact (@lem1367763 term50 term50). Qed.
Lemma lem2652782 : term242 = term243.
Proof. exact (@lem706885). Qed.
Lemma lem2652783 : (term242 = term243) = (term244 = term245).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term243). Qed.
Lemma lem2652784 : term244 = term245.
Proof. exact (EQ_MP (@lem2652783) (@lem2652782)). Qed.
Lemma lem2652785 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652786 : term246 = term247.
Proof. exact (MK_COMB (@lem2652785) (@lem2652784)). Qed.
Lemma lem2652787 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652788 : term241 = term236.
Proof. exact (MK_COMB (@lem2652787) (@lem2652786)). Qed.
Lemma lem2652789 : term233 = term236.
Proof. exact (TRANS (@lem2652781) (@lem2652788)). Qed.
Lemma lem2652790 : term240 = term236.
Proof. exact (TRANS (@lem2652780) (@lem2652789)). Qed.
Lemma lem2652791 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2652792 : term248 = term249.
Proof. exact (MK_COMB (@lem2652791) (@lem2652790)). Qed.
Lemma lem2652793 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2652794 : term250 = term251.
Proof. exact (MK_COMB (@lem2652792) (@lem2652793)). Qed.
Lemma lem2652796 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652797 : term251 = term252.
Proof. exact (@lem2652796 term245 term50). Qed.
Lemma lem2652798 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2652799 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2652800 : term254 = term245.
Proof. exact (EQ_MP (@lem2652799) (@lem2652798)). Qed.
Lemma lem2652801 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652802 : term255 = term247.
Proof. exact (MK_COMB (@lem2652801) (@lem2652800)). Qed.
Lemma lem2652803 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652804 : term252 = term236.
Proof. exact (MK_COMB (@lem2652803) (@lem2652802)). Qed.
Lemma lem2652805 : term251 = term236.
Proof. exact (TRANS (@lem2652797) (@lem2652804)). Qed.
Lemma lem2652806 : term250 = term236.
Proof. exact (TRANS (@lem2652794) (@lem2652805)). Qed.
Lemma lem2652808 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652809 : term115 = term116.
Proof. exact (@lem2652808 term50 term50). Qed.
Lemma lem2652810 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652811 : term118 = term50.
Proof. exact (EQ_MP (@lem2652810) (@lem940073)). Qed.
Lemma lem2652812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652813 : term116 = term49.
Proof. exact (MK_COMB (@lem2652812) (@lem2652811)). Qed.
Lemma lem2652814 : term115 = term49.
Proof. exact (TRANS (@lem2652809) (@lem2652813)). Qed.
Lemma lem2652815 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem2652816 : term256 = term251.
Proof. exact (MK_COMB (@lem2652815) (@lem2652814)). Qed.
Lemma lem2652818 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652819 : term251 = term252.
Proof. exact (@lem2652818 term245 term50). Qed.
Lemma lem2652820 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2652821 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2652822 : term254 = term245.
Proof. exact (EQ_MP (@lem2652821) (@lem2652820)). Qed.
Lemma lem2652823 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652824 : term255 = term247.
Proof. exact (MK_COMB (@lem2652823) (@lem2652822)). Qed.
Lemma lem2652825 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652826 : term252 = term236.
Proof. exact (MK_COMB (@lem2652825) (@lem2652824)). Qed.
Lemma lem2652827 : term251 = term236.
Proof. exact (TRANS (@lem2652819) (@lem2652826)). Qed.
Lemma lem2652828 : term256 = term236.
Proof. exact (TRANS (@lem2652816) (@lem2652827)). Qed.
Lemma lem2652829 : term236 = term256.
Proof. exact (SYM (@lem2652828)). Qed.
Lemma lem2652830 : term250 = term256.
Proof. exact (TRANS (@lem2652806) (@lem2652829)). Qed.
Lemma lem2652831 : term234 = term257.
Proof. exact (@lem2652757 (@lem2652830)). Qed.
Lemma lem2652832 : term233 = term257.
Proof. exact (TRANS (@lem2652723) (@lem2652831)). Qed.
Lemma lem2652834 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2652835 : term257 = term236.
Proof. exact (@lem2652834 term236). Qed.
Lemma lem2652836 : term233 = term236.
Proof. exact (TRANS (@lem2652832) (@lem2652835)). Qed.
Lemma lem2652837 (x : int) : (term212 x) = term258.
Proof. exact (MK_COMB (@lem2652714 x) (@lem2652836)). Qed.
Lemma lem2652838 (x : int) : (term211 x) = term258.
Proof. exact (TRANS (@lem2652606 x) (@lem2652837 x)). Qed.
Lemma lem2652839 : term258 = term236.
Proof. exact (@lem1982721 term236). Qed.
Lemma lem2652840 (x : int) : (term211 x) = term236.
Proof. exact (TRANS (@lem2652838 x) (@lem2652839)). Qed.
Lemma lem2652841 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652842 (x : int) : (term259 x) = term260.
Proof. exact (MK_COMB (@lem2652841) (@lem2652840 x)). Qed.
Lemma lem2652843 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652844 (x : int) : (term210 x) = term261.
Proof. exact (MK_COMB (@lem2652842 x) (@lem2652843)). Qed.
Lemma lem2652845 (x : int) (h1 : term181 x) : term261.
Proof. exact (EQ_MP (@lem2652844 x) (@lem2652605 x h1)). Qed.
Lemma lem2652847 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2652848 : term261 = term262.
Proof. exact (@lem2652847 term45 term236). Qed.
Lemma lem2652850 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2652851 : term236 = term257.
Proof. exact (@lem2652850 term245). Qed.
Lemma lem2652853 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652854 : term45 = term142.
Proof. exact (@lem2652853 (NUMERAL 0)). Qed.
Lemma lem2652855 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2652856 : term80 = term263.
Proof. exact (MK_COMB (@lem2652855) (@lem2652854)). Qed.
Lemma lem2652857 : term262 = term264.
Proof. exact (MK_COMB (@lem2652856) (@lem2652851)). Qed.
Lemma lem2652858 : term265.
Proof. exact (@lem1980026 term45 term49 term236 term49). Qed.
Lemma lem2652860 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652861 : term183 = term189.
Proof. exact (@lem2652860 (NUMERAL 0) term50). Qed.
Lemma lem2652862 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652863 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652864 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652863 h1) (fun h1 : term189 = True => @lem2652862)). Qed.
Lemma lem2652865 : term189 = True.
Proof. exact (EQ_MP (@lem2652864) (@lem2652862)). Qed.
Lemma lem2652866 : term183 = True.
Proof. exact (TRANS (@lem2652861) (@lem2652865)). Qed.
Lemma lem2652867 : True = term183.
Proof. exact (SYM (@lem2652866)). Qed.
Lemma lem2652868 : term183.
Proof. exact (EQ_MP (@lem2652867) (@lem0)). Qed.
Lemma lem2652869 : term266.
Proof. exact (@lem2652858 (@lem2652868)). Qed.
Lemma lem2652871 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652872 : term183 = term189.
Proof. exact (@lem2652871 (NUMERAL 0) term50). Qed.
Lemma lem2652873 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652874 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652875 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652874 h1) (fun h1 : term189 = True => @lem2652873)). Qed.
Lemma lem2652876 : term189 = True.
Proof. exact (EQ_MP (@lem2652875) (@lem2652873)). Qed.
Lemma lem2652877 : term183 = True.
Proof. exact (TRANS (@lem2652872) (@lem2652876)). Qed.
Lemma lem2652878 : True = term183.
Proof. exact (SYM (@lem2652877)). Qed.
Lemma lem2652879 : term183.
Proof. exact (EQ_MP (@lem2652878) (@lem0)). Qed.
Lemma lem2652880 : term264 = term267.
Proof. exact (@lem2652869 (@lem2652879)). Qed.
Lemma lem2652882 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2652883 : term251 = term252.
Proof. exact (@lem2652882 term245 term50). Qed.
Lemma lem2652884 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2652885 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2652886 : term254 = term245.
Proof. exact (EQ_MP (@lem2652885) (@lem2652884)). Qed.
Lemma lem2652887 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652888 : term255 = term247.
Proof. exact (MK_COMB (@lem2652887) (@lem2652886)). Qed.
Lemma lem2652889 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2652890 : term252 = term236.
Proof. exact (MK_COMB (@lem2652889) (@lem2652888)). Qed.
Lemma lem2652891 : term251 = term236.
Proof. exact (TRANS (@lem2652883) (@lem2652890)). Qed.
Lemma lem2652893 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2652894 : term194 = term45.
Proof. exact (@lem2652893 term50). Qed.
Lemma lem2652895 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2652896 : term268 = term80.
Proof. exact (MK_COMB (@lem2652895) (@lem2652894)). Qed.
Lemma lem2652897 : term267 = term262.
Proof. exact (MK_COMB (@lem2652896) (@lem2652891)). Qed.
Lemma lem2652899 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2652900 : term262 = term271.
Proof. exact (@lem2652899 (NUMERAL 0) term245). Qed.
Lemma lem2652901 : term272 = term243.
Proof. exact (@lem912803). Qed.
Lemma lem2652902 (h1 : term272 = term243) : (term245 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term243 h1). Qed.
Lemma lem2652903 : (term272 = term243) = ((term245 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term272 = term243 => @lem2652902 h1) (fun h1 : (term245 = (NUMERAL 0)) = False => @lem2652901)). Qed.
Lemma lem2652904 : (term245 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2652903) (@lem2652901)). Qed.
Lemma lem2652905 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2652906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2652907 : term273 = (and True).
Proof. exact (MK_COMB (@lem2652906) (@lem2652905)). Qed.
Lemma lem2652908 : term271 = (True /\ False).
Proof. exact (MK_COMB (@lem2652907) (@lem2652904)). Qed.
Lemma lem2652910 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2652911 : term271 = False.
Proof. exact (TRANS (@lem2652908) (@lem2652910)). Qed.
Lemma lem2652912 : term262 = False.
Proof. exact (TRANS (@lem2652900) (@lem2652911)). Qed.
Lemma lem2652913 : term267 = False.
Proof. exact (TRANS (@lem2652897) (@lem2652912)). Qed.
Lemma lem2652914 : term264 = False.
Proof. exact (TRANS (@lem2652880) (@lem2652913)). Qed.
Lemma lem2652915 : term262 = False.
Proof. exact (TRANS (@lem2652857) (@lem2652914)). Qed.
Lemma lem2652916 : term261 = False.
Proof. exact (TRANS (@lem2652848) (@lem2652915)). Qed.
Lemma lem2652917 (x : int) (h1 : term181 x) : False.
Proof. exact (EQ_MP (@lem2652916) (@lem2652845 x h1)). Qed.
Lemma lem2652918 (x : int) (h1 : term274 x) : term274 x.
Proof. exact (h1). Qed.
Lemma lem2652919 (x : int) (h1 : term274 x) : (real_of_int x) = term45.
Proof. exact (proj2 (@lem2652918 x h1)). Qed.
Lemma lem2652920 (x : int) (h1 : term274 x) : term128 x.
Proof. exact (proj1 (@lem2652918 x h1)). Qed.
Lemma lem2652922 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2652923 : term182 = term183.
Proof. exact (@lem2652922 term45 term49). Qed.
Lemma lem2652925 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652926 : term49 = term103.
Proof. exact (@lem2652925 term50). Qed.
Lemma lem2652928 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2652929 : term45 = term142.
Proof. exact (@lem2652928 (NUMERAL 0)). Qed.
Lemma lem2652930 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2652931 : term184 = term185.
Proof. exact (MK_COMB (@lem2652930) (@lem2652929)). Qed.
Lemma lem2652932 : term183 = term186.
Proof. exact (MK_COMB (@lem2652931) (@lem2652926)). Qed.
Lemma lem2652933 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2652935 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652936 : term183 = term189.
Proof. exact (@lem2652935 (NUMERAL 0) term50). Qed.
Lemma lem2652937 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652938 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652939 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652938 h1) (fun h1 : term189 = True => @lem2652937)). Qed.
Lemma lem2652940 : term189 = True.
Proof. exact (EQ_MP (@lem2652939) (@lem2652937)). Qed.
Lemma lem2652941 : term183 = True.
Proof. exact (TRANS (@lem2652936) (@lem2652940)). Qed.
Lemma lem2652942 : True = term183.
Proof. exact (SYM (@lem2652941)). Qed.
Lemma lem2652943 : term183.
Proof. exact (EQ_MP (@lem2652942) (@lem0)). Qed.
Lemma lem2652944 : term191.
Proof. exact (@lem2652933 (@lem2652943)). Qed.
Lemma lem2652946 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652947 : term183 = term189.
Proof. exact (@lem2652946 (NUMERAL 0) term50). Qed.
Lemma lem2652948 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652949 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652950 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652949 h1) (fun h1 : term189 = True => @lem2652948)). Qed.
Lemma lem2652951 : term189 = True.
Proof. exact (EQ_MP (@lem2652950) (@lem2652948)). Qed.
Lemma lem2652952 : term183 = True.
Proof. exact (TRANS (@lem2652947) (@lem2652951)). Qed.
Lemma lem2652953 : True = term183.
Proof. exact (SYM (@lem2652952)). Qed.
Lemma lem2652954 : term183.
Proof. exact (EQ_MP (@lem2652953) (@lem0)). Qed.
Lemma lem2652955 : term186 = term192.
Proof. exact (@lem2652944 (@lem2652954)). Qed.
Lemma lem2652957 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2652958 : term115 = term116.
Proof. exact (@lem2652957 term50 term50). Qed.
Lemma lem2652959 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2652960 : term118 = term50.
Proof. exact (EQ_MP (@lem2652959) (@lem940073)). Qed.
Lemma lem2652961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2652962 : term116 = term49.
Proof. exact (MK_COMB (@lem2652961) (@lem2652960)). Qed.
Lemma lem2652963 : term115 = term49.
Proof. exact (TRANS (@lem2652958) (@lem2652962)). Qed.
Lemma lem2652965 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2652966 : term194 = term45.
Proof. exact (@lem2652965 term50). Qed.
Lemma lem2652967 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2652968 : term195 = term184.
Proof. exact (MK_COMB (@lem2652967) (@lem2652966)). Qed.
Lemma lem2652969 : term192 = term183.
Proof. exact (MK_COMB (@lem2652968) (@lem2652963)). Qed.
Lemma lem2652971 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2652972 : term183 = term189.
Proof. exact (@lem2652971 (NUMERAL 0) term50). Qed.
Lemma lem2652973 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2652974 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2652975 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2652974 h1) (fun h1 : term189 = True => @lem2652973)). Qed.
Lemma lem2652976 : term189 = True.
Proof. exact (EQ_MP (@lem2652975) (@lem2652973)). Qed.
Lemma lem2652977 : term183 = True.
Proof. exact (TRANS (@lem2652972) (@lem2652976)). Qed.
Lemma lem2652978 : term192 = True.
Proof. exact (TRANS (@lem2652969) (@lem2652977)). Qed.
Lemma lem2652979 : term186 = True.
Proof. exact (TRANS (@lem2652955) (@lem2652978)). Qed.
Lemma lem2652980 : term183 = True.
Proof. exact (TRANS (@lem2652932) (@lem2652979)). Qed.
Lemma lem2652981 : term182 = True.
Proof. exact (TRANS (@lem2652923) (@lem2652980)). Qed.
Lemma lem2652982 : True = term182.
Proof. exact (SYM (@lem2652981)). Qed.
Lemma lem2652983 : term182.
Proof. exact (EQ_MP (@lem2652982) (@lem0)). Qed.
Lemma lem2652984 (x : int) (h1 : term274 x) : term196 x.
Proof. exact (conj (@lem2652983) (@lem2652920 x h1)). Qed.
Lemma lem2652986 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2652987 (x : int) : term198 x.
Proof. exact (@lem2652986 term49 (term125 x)). Qed.
Lemma lem2652988 (x : int) (h1 : term274 x) : term199 x.
Proof. exact (@lem2652987 x (@lem2652984 x h1)). Qed.
Lemma lem2652989 (x : int) : (term200 x) = (term125 x).
Proof. exact (@lem1982733 (term125 x)). Qed.
Lemma lem2652990 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2652991 (x : int) : (term201 x) = (term127 x).
Proof. exact (MK_COMB (@lem2652990) (@lem2652989 x)). Qed.
Lemma lem2652992 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2652993 (x : int) : (term199 x) = (term128 x).
Proof. exact (MK_COMB (@lem2652991 x) (@lem2652992)). Qed.
Lemma lem2652994 (x : int) (h1 : term274 x) : term128 x.
Proof. exact (EQ_MP (@lem2652993 x) (@lem2652988 x h1)). Qed.
Lemma lem2652996 (y : real) : term275 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2652997 (x : int) : term276 x.
Proof. exact (@lem2652996 (real_of_int x)). Qed.
Lemma lem2652998 (x : int) (h1 : term274 x) : term277 x.
Proof. exact (@lem2652997 x (@lem2652919 x h1)). Qed.
Lemma lem2652999 (x : int) (h1 : term274 x) : term278 x.
Proof. exact (@lem2652998 x h1 term106). Qed.
Lemma lem2653000 (x : int) : (term278 x) = ((term158 x) = term45).
Proof. exact (eq_refl (term278 x)). Qed.
Lemma lem2653007 (x : int) (h1 : term274 x) : (term158 x) = term45.
Proof. exact (EQ_MP (@lem2653000 x) (@lem2652999 x h1)). Qed.
Lemma lem2653008 (x : int) (h1 : term274 x) : term279 x.
Proof. exact (conj (@lem2653007 x h1) (@lem2652994 x h1)). Qed.
Lemma lem2653010 (x : real) (y : real) : term280 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2653011 (x : int) : term281 x.
Proof. exact (@lem2653010 (term158 x) (term125 x)). Qed.
Lemma lem2653012 (x : int) (h1 : term274 x) : term282 x.
Proof. exact (@lem2653011 x (@lem2653008 x h1)). Qed.
Lemma lem2653013 (x : int) : (term283 x) = (term284 x).
Proof. exact (@lem1982763 (term158 x) (real_of_int x) term106). Qed.
Lemma lem2653014 (x : int) : (term213 x) = (term214 x).
Proof. exact (@lem1982713 term106 (real_of_int x)). Qed.
Lemma lem2653016 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653017 : term49 = term103.
Proof. exact (@lem2653016 term50). Qed.
Lemma lem2653019 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2653020 : term106 = term107.
Proof. exact (@lem2653019 term50). Qed.
Lemma lem2653021 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653022 : term215 = term216.
Proof. exact (MK_COMB (@lem2653021) (@lem2653020)). Qed.
Lemma lem2653023 : term217 = term218.
Proof. exact (MK_COMB (@lem2653022) (@lem2653017)). Qed.
Lemma lem2653024 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2653026 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653027 : term183 = term189.
Proof. exact (@lem2653026 (NUMERAL 0) term50). Qed.
Lemma lem2653028 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653029 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653030 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653029 h1) (fun h1 : term189 = True => @lem2653028)). Qed.
Lemma lem2653031 : term189 = True.
Proof. exact (EQ_MP (@lem2653030) (@lem2653028)). Qed.
Lemma lem2653032 : term183 = True.
Proof. exact (TRANS (@lem2653027) (@lem2653031)). Qed.
Lemma lem2653033 : True = term183.
Proof. exact (SYM (@lem2653032)). Qed.
Lemma lem2653034 : term183.
Proof. exact (EQ_MP (@lem2653033) (@lem0)). Qed.
Lemma lem2653035 : term220.
Proof. exact (@lem2653024 (@lem2653034)). Qed.
Lemma lem2653037 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653038 : term183 = term189.
Proof. exact (@lem2653037 (NUMERAL 0) term50). Qed.
Lemma lem2653039 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653040 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653041 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653040 h1) (fun h1 : term189 = True => @lem2653039)). Qed.
Lemma lem2653042 : term189 = True.
Proof. exact (EQ_MP (@lem2653041) (@lem2653039)). Qed.
Lemma lem2653043 : term183 = True.
Proof. exact (TRANS (@lem2653038) (@lem2653042)). Qed.
Lemma lem2653044 : True = term183.
Proof. exact (SYM (@lem2653043)). Qed.
Lemma lem2653045 : term183.
Proof. exact (EQ_MP (@lem2653044) (@lem0)). Qed.
Lemma lem2653046 : term221.
Proof. exact (@lem2653035 (@lem2653045)). Qed.
Lemma lem2653048 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653049 : term183 = term189.
Proof. exact (@lem2653048 (NUMERAL 0) term50). Qed.
Lemma lem2653050 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653051 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653052 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653051 h1) (fun h1 : term189 = True => @lem2653050)). Qed.
Lemma lem2653053 : term189 = True.
Proof. exact (EQ_MP (@lem2653052) (@lem2653050)). Qed.
Lemma lem2653054 : term183 = True.
Proof. exact (TRANS (@lem2653049) (@lem2653053)). Qed.
Lemma lem2653055 : True = term183.
Proof. exact (SYM (@lem2653054)). Qed.
Lemma lem2653056 : term183.
Proof. exact (EQ_MP (@lem2653055) (@lem0)). Qed.
Lemma lem2653057 : term222.
Proof. exact (@lem2653046 (@lem2653056)). Qed.
Lemma lem2653059 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653060 : term115 = term116.
Proof. exact (@lem2653059 term50 term50). Qed.
Lemma lem2653061 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653062 : term118 = term50.
Proof. exact (EQ_MP (@lem2653061) (@lem940073)). Qed.
Lemma lem2653063 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653064 : term116 = term49.
Proof. exact (MK_COMB (@lem2653063) (@lem2653062)). Qed.
Lemma lem2653065 : term115 = term49.
Proof. exact (TRANS (@lem2653060) (@lem2653064)). Qed.
Lemma lem2653067 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2653068 : term110 = term121.
Proof. exact (@lem2653067 term50 term50). Qed.
Lemma lem2653069 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653070 : term118 = term50.
Proof. exact (EQ_MP (@lem2653069) (@lem940073)). Qed.
Lemma lem2653071 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653072 : term116 = term49.
Proof. exact (MK_COMB (@lem2653071) (@lem2653070)). Qed.
Lemma lem2653073 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2653074 : term121 = term106.
Proof. exact (MK_COMB (@lem2653073) (@lem2653072)). Qed.
Lemma lem2653075 : term110 = term106.
Proof. exact (TRANS (@lem2653068) (@lem2653074)). Qed.
Lemma lem2653076 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653077 : term223 = term215.
Proof. exact (MK_COMB (@lem2653076) (@lem2653075)). Qed.
Lemma lem2653078 : term224 = term217.
Proof. exact (MK_COMB (@lem2653077) (@lem2653065)). Qed.
Lemma lem2653080 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2653081 : term217 = term45.
Proof. exact (@lem2653080 term50). Qed.
Lemma lem2653082 : term224 = term45.
Proof. exact (TRANS (@lem2653078) (@lem2653081)). Qed.
Lemma lem2653083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2653084 : term226 = term227.
Proof. exact (MK_COMB (@lem2653083) (@lem2653082)). Qed.
Lemma lem2653085 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2653086 : term228 = term194.
Proof. exact (MK_COMB (@lem2653084) (@lem2653085)). Qed.
Lemma lem2653088 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653089 : term194 = term45.
Proof. exact (@lem2653088 term50). Qed.
Lemma lem2653090 : term228 = term45.
Proof. exact (TRANS (@lem2653086) (@lem2653089)). Qed.
Lemma lem2653092 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653093 : term115 = term116.
Proof. exact (@lem2653092 term50 term50). Qed.
Lemma lem2653094 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653095 : term118 = term50.
Proof. exact (EQ_MP (@lem2653094) (@lem940073)). Qed.
Lemma lem2653096 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653097 : term116 = term49.
Proof. exact (MK_COMB (@lem2653096) (@lem2653095)). Qed.
Lemma lem2653098 : term115 = term49.
Proof. exact (TRANS (@lem2653093) (@lem2653097)). Qed.
Lemma lem2653099 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2653100 : term229 = term194.
Proof. exact (MK_COMB (@lem2653099) (@lem2653098)). Qed.
Lemma lem2653102 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653103 : term194 = term45.
Proof. exact (@lem2653102 term50). Qed.
Lemma lem2653104 : term229 = term45.
Proof. exact (TRANS (@lem2653100) (@lem2653103)). Qed.
Lemma lem2653105 : term45 = term229.
Proof. exact (SYM (@lem2653104)). Qed.
Lemma lem2653106 : term228 = term229.
Proof. exact (TRANS (@lem2653090) (@lem2653105)). Qed.
Lemma lem2653107 : term218 = term142.
Proof. exact (@lem2653057 (@lem2653106)). Qed.
Lemma lem2653108 : term217 = term142.
Proof. exact (TRANS (@lem2653023) (@lem2653107)). Qed.
Lemma lem2653110 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2653111 : term142 = term45.
Proof. exact (@lem2653110 term45). Qed.
Lemma lem2653112 : term217 = term45.
Proof. exact (TRANS (@lem2653108) (@lem2653111)). Qed.
Lemma lem2653113 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2653114 : term230 = term227.
Proof. exact (MK_COMB (@lem2653113) (@lem2653112)). Qed.
Lemma lem2653115 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2653116 (x : int) : (term214 x) = (term231 x).
Proof. exact (MK_COMB (@lem2653114) (@lem2653115 x)). Qed.
Lemma lem2653117 (x : int) : (term213 x) = (term231 x).
Proof. exact (TRANS (@lem2653014 x) (@lem2653116 x)). Qed.
Lemma lem2653118 (x : int) : (term231 x) = term45.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2653119 (x : int) : (term213 x) = term45.
Proof. exact (TRANS (@lem2653117 x) (@lem2653118 x)). Qed.
Lemma lem2653120 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653121 (x : int) : (term232 x) = term47.
Proof. exact (MK_COMB (@lem2653120) (@lem2653119 x)). Qed.
Lemma lem2653122 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2653123 (x : int) : (term284 x) = term285.
Proof. exact (MK_COMB (@lem2653121 x) (@lem2653122)). Qed.
Lemma lem2653124 (x : int) : (term283 x) = term285.
Proof. exact (TRANS (@lem2653013 x) (@lem2653123 x)). Qed.
Lemma lem2653125 : term285 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2653126 (x : int) : (term283 x) = term106.
Proof. exact (TRANS (@lem2653124 x) (@lem2653125)). Qed.
Lemma lem2653127 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2653128 (x : int) : (term286 x) = term287.
Proof. exact (MK_COMB (@lem2653127) (@lem2653126 x)). Qed.
Lemma lem2653129 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2653130 (x : int) : (term282 x) = term288.
Proof. exact (MK_COMB (@lem2653128 x) (@lem2653129)). Qed.
Lemma lem2653131 (x : int) (h1 : term274 x) : term288.
Proof. exact (EQ_MP (@lem2653130 x) (@lem2653012 x h1)). Qed.
Lemma lem2653133 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2653134 : term288 = term289.
Proof. exact (@lem2653133 term45 term106). Qed.
Lemma lem2653136 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2653137 : term106 = term107.
Proof. exact (@lem2653136 term50). Qed.
Lemma lem2653139 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653140 : term45 = term142.
Proof. exact (@lem2653139 (NUMERAL 0)). Qed.
Lemma lem2653141 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2653142 : term80 = term263.
Proof. exact (MK_COMB (@lem2653141) (@lem2653140)). Qed.
Lemma lem2653143 : term289 = term290.
Proof. exact (MK_COMB (@lem2653142) (@lem2653137)). Qed.
Lemma lem2653144 : term291.
Proof. exact (@lem1980026 term45 term49 term106 term49). Qed.
Lemma lem2653146 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653147 : term183 = term189.
Proof. exact (@lem2653146 (NUMERAL 0) term50). Qed.
Lemma lem2653148 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653149 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653150 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653149 h1) (fun h1 : term189 = True => @lem2653148)). Qed.
Lemma lem2653151 : term189 = True.
Proof. exact (EQ_MP (@lem2653150) (@lem2653148)). Qed.
Lemma lem2653152 : term183 = True.
Proof. exact (TRANS (@lem2653147) (@lem2653151)). Qed.
Lemma lem2653153 : True = term183.
Proof. exact (SYM (@lem2653152)). Qed.
Lemma lem2653154 : term183.
Proof. exact (EQ_MP (@lem2653153) (@lem0)). Qed.
Lemma lem2653155 : term292.
Proof. exact (@lem2653144 (@lem2653154)). Qed.
Lemma lem2653157 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653158 : term183 = term189.
Proof. exact (@lem2653157 (NUMERAL 0) term50). Qed.
Lemma lem2653159 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653160 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653161 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653160 h1) (fun h1 : term189 = True => @lem2653159)). Qed.
Lemma lem2653162 : term189 = True.
Proof. exact (EQ_MP (@lem2653161) (@lem2653159)). Qed.
Lemma lem2653163 : term183 = True.
Proof. exact (TRANS (@lem2653158) (@lem2653162)). Qed.
Lemma lem2653164 : True = term183.
Proof. exact (SYM (@lem2653163)). Qed.
Lemma lem2653165 : term183.
Proof. exact (EQ_MP (@lem2653164) (@lem0)). Qed.
Lemma lem2653166 : term290 = term293.
Proof. exact (@lem2653155 (@lem2653165)). Qed.
Lemma lem2653168 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2653169 : term110 = term121.
Proof. exact (@lem2653168 term50 term50). Qed.
Lemma lem2653170 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653171 : term118 = term50.
Proof. exact (EQ_MP (@lem2653170) (@lem940073)). Qed.
Lemma lem2653172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653173 : term116 = term49.
Proof. exact (MK_COMB (@lem2653172) (@lem2653171)). Qed.
Lemma lem2653174 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2653175 : term121 = term106.
Proof. exact (MK_COMB (@lem2653174) (@lem2653173)). Qed.
Lemma lem2653176 : term110 = term106.
Proof. exact (TRANS (@lem2653169) (@lem2653175)). Qed.
Lemma lem2653178 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653179 : term194 = term45.
Proof. exact (@lem2653178 term50). Qed.
Lemma lem2653180 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2653181 : term268 = term80.
Proof. exact (MK_COMB (@lem2653180) (@lem2653179)). Qed.
Lemma lem2653182 : term293 = term289.
Proof. exact (MK_COMB (@lem2653181) (@lem2653176)). Qed.
Lemma lem2653184 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2653185 : term289 = term294.
Proof. exact (@lem2653184 (NUMERAL 0) term50). Qed.
Lemma lem2653186 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653187 (h1 : term190 = (BIT1 0)) : (term50 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2653188 : (term190 = (BIT1 0)) = ((term50 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653187 h1) (fun h1 : (term50 = (NUMERAL 0)) = False => @lem2653186)). Qed.
Lemma lem2653189 : (term50 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2653188) (@lem2653186)). Qed.
Lemma lem2653190 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2653191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2653192 : term273 = (and True).
Proof. exact (MK_COMB (@lem2653191) (@lem2653190)). Qed.
Lemma lem2653193 : term294 = (True /\ False).
Proof. exact (MK_COMB (@lem2653192) (@lem2653189)). Qed.
Lemma lem2653195 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2653196 : term294 = False.
Proof. exact (TRANS (@lem2653193) (@lem2653195)). Qed.
Lemma lem2653197 : term289 = False.
Proof. exact (TRANS (@lem2653185) (@lem2653196)). Qed.
Lemma lem2653198 : term293 = False.
Proof. exact (TRANS (@lem2653182) (@lem2653197)). Qed.
Lemma lem2653199 : term290 = False.
Proof. exact (TRANS (@lem2653166) (@lem2653198)). Qed.
Lemma lem2653200 : term289 = False.
Proof. exact (TRANS (@lem2653143) (@lem2653199)). Qed.
Lemma lem2653201 : term288 = False.
Proof. exact (TRANS (@lem2653134) (@lem2653200)). Qed.
Lemma lem2653202 (x : int) (h1 : term274 x) : False.
Proof. exact (EQ_MP (@lem2653201) (@lem2653131 x h1)). Qed.
Lemma lem2653203 (x : int) (h1 : term178 x) : False.
Proof. exact (or_elim (@lem2652449 x h1) (fun h0 : term181 x => @lem2652917 x h0) (fun h0 : term274 x => @lem2653202 x h0)). Qed.
Lemma lem2653204 (x : int) (h1 : term175 x) : term175 x.
Proof. exact (h1). Qed.
Lemma lem2653205 (x : int) (h1 : term295 x) : term295 x.
Proof. exact (h1). Qed.
Lemma lem2653206 (x : int) (h1 : term295 x) : term176 x.
Proof. exact (proj2 (@lem2653205 x h1)). Qed.
Lemma lem2653208 (x : int) (h1 : term295 x) : term139 x.
Proof. exact (proj2 (@lem2653206 x h1)). Qed.
Lemma lem2653209 (x : int) (h1 : term295 x) : term165 x.
Proof. exact (proj1 (@lem2653206 x h1)). Qed.
Lemma lem2653211 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2653212 : term182 = term183.
Proof. exact (@lem2653211 term45 term49). Qed.
Lemma lem2653214 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653215 : term49 = term103.
Proof. exact (@lem2653214 term50). Qed.
Lemma lem2653217 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653218 : term45 = term142.
Proof. exact (@lem2653217 (NUMERAL 0)). Qed.
Lemma lem2653219 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2653220 : term184 = term185.
Proof. exact (MK_COMB (@lem2653219) (@lem2653218)). Qed.
Lemma lem2653221 : term183 = term186.
Proof. exact (MK_COMB (@lem2653220) (@lem2653215)). Qed.
Lemma lem2653222 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2653224 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653225 : term183 = term189.
Proof. exact (@lem2653224 (NUMERAL 0) term50). Qed.
Lemma lem2653226 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653227 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653228 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653227 h1) (fun h1 : term189 = True => @lem2653226)). Qed.
Lemma lem2653229 : term189 = True.
Proof. exact (EQ_MP (@lem2653228) (@lem2653226)). Qed.
Lemma lem2653230 : term183 = True.
Proof. exact (TRANS (@lem2653225) (@lem2653229)). Qed.
Lemma lem2653231 : True = term183.
Proof. exact (SYM (@lem2653230)). Qed.
Lemma lem2653232 : term183.
Proof. exact (EQ_MP (@lem2653231) (@lem0)). Qed.
Lemma lem2653233 : term191.
Proof. exact (@lem2653222 (@lem2653232)). Qed.
Lemma lem2653235 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653236 : term183 = term189.
Proof. exact (@lem2653235 (NUMERAL 0) term50). Qed.
Lemma lem2653237 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653238 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653239 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653238 h1) (fun h1 : term189 = True => @lem2653237)). Qed.
Lemma lem2653240 : term189 = True.
Proof. exact (EQ_MP (@lem2653239) (@lem2653237)). Qed.
Lemma lem2653241 : term183 = True.
Proof. exact (TRANS (@lem2653236) (@lem2653240)). Qed.
Lemma lem2653242 : True = term183.
Proof. exact (SYM (@lem2653241)). Qed.
Lemma lem2653243 : term183.
Proof. exact (EQ_MP (@lem2653242) (@lem0)). Qed.
Lemma lem2653244 : term186 = term192.
Proof. exact (@lem2653233 (@lem2653243)). Qed.
Lemma lem2653246 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653247 : term115 = term116.
Proof. exact (@lem2653246 term50 term50). Qed.
Lemma lem2653248 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653249 : term118 = term50.
Proof. exact (EQ_MP (@lem2653248) (@lem940073)). Qed.
Lemma lem2653250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653251 : term116 = term49.
Proof. exact (MK_COMB (@lem2653250) (@lem2653249)). Qed.
Lemma lem2653252 : term115 = term49.
Proof. exact (TRANS (@lem2653247) (@lem2653251)). Qed.
Lemma lem2653254 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653255 : term194 = term45.
Proof. exact (@lem2653254 term50). Qed.
Lemma lem2653256 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2653257 : term195 = term184.
Proof. exact (MK_COMB (@lem2653256) (@lem2653255)). Qed.
Lemma lem2653258 : term192 = term183.
Proof. exact (MK_COMB (@lem2653257) (@lem2653252)). Qed.
Lemma lem2653260 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653261 : term183 = term189.
Proof. exact (@lem2653260 (NUMERAL 0) term50). Qed.
Lemma lem2653262 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653263 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653264 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653263 h1) (fun h1 : term189 = True => @lem2653262)). Qed.
Lemma lem2653265 : term189 = True.
Proof. exact (EQ_MP (@lem2653264) (@lem2653262)). Qed.
Lemma lem2653266 : term183 = True.
Proof. exact (TRANS (@lem2653261) (@lem2653265)). Qed.
Lemma lem2653267 : term192 = True.
Proof. exact (TRANS (@lem2653258) (@lem2653266)). Qed.
Lemma lem2653268 : term186 = True.
Proof. exact (TRANS (@lem2653244) (@lem2653267)). Qed.
Lemma lem2653269 : term183 = True.
Proof. exact (TRANS (@lem2653221) (@lem2653268)). Qed.
Lemma lem2653270 : term182 = True.
Proof. exact (TRANS (@lem2653212) (@lem2653269)). Qed.
Lemma lem2653271 : True = term182.
Proof. exact (SYM (@lem2653270)). Qed.
Lemma lem2653272 : term182.
Proof. exact (EQ_MP (@lem2653271) (@lem0)). Qed.
Lemma lem2653273 (x : int) (h1 : term295 x) : term296 x.
Proof. exact (conj (@lem2653272) (@lem2653209 x h1)). Qed.
Lemma lem2653275 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2653276 (x : int) : term297 x.
Proof. exact (@lem2653275 term49 (real_of_int x)). Qed.
Lemma lem2653277 (x : int) (h1 : term295 x) : term298 x.
Proof. exact (@lem2653276 x (@lem2653273 x h1)). Qed.
Lemma lem2653278 (x : int) : (term299 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2653279 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2653280 (x : int) : (term300 x) = (term164 x).
Proof. exact (MK_COMB (@lem2653279) (@lem2653278 x)). Qed.
Lemma lem2653281 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2653282 (x : int) : (term298 x) = (term165 x).
Proof. exact (MK_COMB (@lem2653280 x) (@lem2653281)). Qed.
Lemma lem2653283 (x : int) (h1 : term295 x) : term165 x.
Proof. exact (EQ_MP (@lem2653282 x) (@lem2653277 x h1)). Qed.
Lemma lem2653285 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2653286 : term182 = term183.
Proof. exact (@lem2653285 term45 term49). Qed.
Lemma lem2653288 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653289 : term49 = term103.
Proof. exact (@lem2653288 term50). Qed.
Lemma lem2653291 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653292 : term45 = term142.
Proof. exact (@lem2653291 (NUMERAL 0)). Qed.
Lemma lem2653293 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2653294 : term184 = term185.
Proof. exact (MK_COMB (@lem2653293) (@lem2653292)). Qed.
Lemma lem2653295 : term183 = term186.
Proof. exact (MK_COMB (@lem2653294) (@lem2653289)). Qed.
Lemma lem2653296 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2653298 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653299 : term183 = term189.
Proof. exact (@lem2653298 (NUMERAL 0) term50). Qed.
Lemma lem2653300 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653301 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653302 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653301 h1) (fun h1 : term189 = True => @lem2653300)). Qed.
Lemma lem2653303 : term189 = True.
Proof. exact (EQ_MP (@lem2653302) (@lem2653300)). Qed.
Lemma lem2653304 : term183 = True.
Proof. exact (TRANS (@lem2653299) (@lem2653303)). Qed.
Lemma lem2653305 : True = term183.
Proof. exact (SYM (@lem2653304)). Qed.
Lemma lem2653306 : term183.
Proof. exact (EQ_MP (@lem2653305) (@lem0)). Qed.
Lemma lem2653307 : term191.
Proof. exact (@lem2653296 (@lem2653306)). Qed.
Lemma lem2653309 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653310 : term183 = term189.
Proof. exact (@lem2653309 (NUMERAL 0) term50). Qed.
Lemma lem2653311 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653312 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653313 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653312 h1) (fun h1 : term189 = True => @lem2653311)). Qed.
Lemma lem2653314 : term189 = True.
Proof. exact (EQ_MP (@lem2653313) (@lem2653311)). Qed.
Lemma lem2653315 : term183 = True.
Proof. exact (TRANS (@lem2653310) (@lem2653314)). Qed.
Lemma lem2653316 : True = term183.
Proof. exact (SYM (@lem2653315)). Qed.
Lemma lem2653317 : term183.
Proof. exact (EQ_MP (@lem2653316) (@lem0)). Qed.
Lemma lem2653318 : term186 = term192.
Proof. exact (@lem2653307 (@lem2653317)). Qed.
Lemma lem2653320 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653321 : term115 = term116.
Proof. exact (@lem2653320 term50 term50). Qed.
Lemma lem2653322 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653323 : term118 = term50.
Proof. exact (EQ_MP (@lem2653322) (@lem940073)). Qed.
Lemma lem2653324 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653325 : term116 = term49.
Proof. exact (MK_COMB (@lem2653324) (@lem2653323)). Qed.
Lemma lem2653326 : term115 = term49.
Proof. exact (TRANS (@lem2653321) (@lem2653325)). Qed.
Lemma lem2653328 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653329 : term194 = term45.
Proof. exact (@lem2653328 term50). Qed.
Lemma lem2653330 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2653331 : term195 = term184.
Proof. exact (MK_COMB (@lem2653330) (@lem2653329)). Qed.
Lemma lem2653332 : term192 = term183.
Proof. exact (MK_COMB (@lem2653331) (@lem2653326)). Qed.
Lemma lem2653334 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653335 : term183 = term189.
Proof. exact (@lem2653334 (NUMERAL 0) term50). Qed.
Lemma lem2653336 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653337 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653338 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653337 h1) (fun h1 : term189 = True => @lem2653336)). Qed.
Lemma lem2653339 : term189 = True.
Proof. exact (EQ_MP (@lem2653338) (@lem2653336)). Qed.
Lemma lem2653340 : term183 = True.
Proof. exact (TRANS (@lem2653335) (@lem2653339)). Qed.
Lemma lem2653341 : term192 = True.
Proof. exact (TRANS (@lem2653332) (@lem2653340)). Qed.
Lemma lem2653342 : term186 = True.
Proof. exact (TRANS (@lem2653318) (@lem2653341)). Qed.
Lemma lem2653343 : term183 = True.
Proof. exact (TRANS (@lem2653295) (@lem2653342)). Qed.
Lemma lem2653344 : term182 = True.
Proof. exact (TRANS (@lem2653286) (@lem2653343)). Qed.
Lemma lem2653345 : True = term182.
Proof. exact (SYM (@lem2653344)). Qed.
Lemma lem2653346 : term182.
Proof. exact (EQ_MP (@lem2653345) (@lem0)). Qed.
Lemma lem2653347 (x : int) (h1 : term295 x) : term202 x.
Proof. exact (conj (@lem2653346) (@lem2653208 x h1)). Qed.
Lemma lem2653349 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2653350 (x : int) : term203 x.
Proof. exact (@lem2653349 term49 (term135 x)). Qed.
Lemma lem2653351 (x : int) (h1 : term295 x) : term204 x.
Proof. exact (@lem2653350 x (@lem2653347 x h1)). Qed.
Lemma lem2653352 (x : int) : (term205 x) = (term135 x).
Proof. exact (@lem1982733 (term135 x)). Qed.
Lemma lem2653353 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2653354 (x : int) : (term206 x) = (term138 x).
Proof. exact (MK_COMB (@lem2653353) (@lem2653352 x)). Qed.
Lemma lem2653355 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2653356 (x : int) : (term204 x) = (term139 x).
Proof. exact (MK_COMB (@lem2653354 x) (@lem2653355)). Qed.
Lemma lem2653357 (x : int) (h1 : term295 x) : term139 x.
Proof. exact (EQ_MP (@lem2653356 x) (@lem2653351 x h1)). Qed.
Lemma lem2653358 (x : int) (h1 : term295 x) : term301 x.
Proof. exact (conj (@lem2653357 x h1) (@lem2653283 x h1)). Qed.
Lemma lem2653360 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2653361 (x : int) : term302 x.
Proof. exact (@lem2653360 (term135 x) (real_of_int x)). Qed.
Lemma lem2653362 (x : int) (h1 : term295 x) : term303 x.
Proof. exact (@lem2653361 x (@lem2653358 x h1)). Qed.
Lemma lem2653363 (x : int) : (term304 x) = (term284 x).
Proof. exact (@lem1982759 (term158 x) (real_of_int x) term106). Qed.
Lemma lem2653364 (x : int) : (term213 x) = (term214 x).
Proof. exact (@lem1982713 term106 (real_of_int x)). Qed.
Lemma lem2653366 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653367 : term49 = term103.
Proof. exact (@lem2653366 term50). Qed.
Lemma lem2653369 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2653370 : term106 = term107.
Proof. exact (@lem2653369 term50). Qed.
Lemma lem2653371 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653372 : term215 = term216.
Proof. exact (MK_COMB (@lem2653371) (@lem2653370)). Qed.
Lemma lem2653373 : term217 = term218.
Proof. exact (MK_COMB (@lem2653372) (@lem2653367)). Qed.
Lemma lem2653374 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2653376 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653377 : term183 = term189.
Proof. exact (@lem2653376 (NUMERAL 0) term50). Qed.
Lemma lem2653378 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653379 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653380 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653379 h1) (fun h1 : term189 = True => @lem2653378)). Qed.
Lemma lem2653381 : term189 = True.
Proof. exact (EQ_MP (@lem2653380) (@lem2653378)). Qed.
Lemma lem2653382 : term183 = True.
Proof. exact (TRANS (@lem2653377) (@lem2653381)). Qed.
Lemma lem2653383 : True = term183.
Proof. exact (SYM (@lem2653382)). Qed.
Lemma lem2653384 : term183.
Proof. exact (EQ_MP (@lem2653383) (@lem0)). Qed.
Lemma lem2653385 : term220.
Proof. exact (@lem2653374 (@lem2653384)). Qed.
Lemma lem2653387 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653388 : term183 = term189.
Proof. exact (@lem2653387 (NUMERAL 0) term50). Qed.
Lemma lem2653389 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653390 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653391 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653390 h1) (fun h1 : term189 = True => @lem2653389)). Qed.
Lemma lem2653392 : term189 = True.
Proof. exact (EQ_MP (@lem2653391) (@lem2653389)). Qed.
Lemma lem2653393 : term183 = True.
Proof. exact (TRANS (@lem2653388) (@lem2653392)). Qed.
Lemma lem2653394 : True = term183.
Proof. exact (SYM (@lem2653393)). Qed.
Lemma lem2653395 : term183.
Proof. exact (EQ_MP (@lem2653394) (@lem0)). Qed.
Lemma lem2653396 : term221.
Proof. exact (@lem2653385 (@lem2653395)). Qed.
Lemma lem2653398 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653399 : term183 = term189.
Proof. exact (@lem2653398 (NUMERAL 0) term50). Qed.
Lemma lem2653400 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653401 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653402 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653401 h1) (fun h1 : term189 = True => @lem2653400)). Qed.
Lemma lem2653403 : term189 = True.
Proof. exact (EQ_MP (@lem2653402) (@lem2653400)). Qed.
Lemma lem2653404 : term183 = True.
Proof. exact (TRANS (@lem2653399) (@lem2653403)). Qed.
Lemma lem2653405 : True = term183.
Proof. exact (SYM (@lem2653404)). Qed.
Lemma lem2653406 : term183.
Proof. exact (EQ_MP (@lem2653405) (@lem0)). Qed.
Lemma lem2653407 : term222.
Proof. exact (@lem2653396 (@lem2653406)). Qed.
Lemma lem2653409 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653410 : term115 = term116.
Proof. exact (@lem2653409 term50 term50). Qed.
Lemma lem2653411 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653412 : term118 = term50.
Proof. exact (EQ_MP (@lem2653411) (@lem940073)). Qed.
Lemma lem2653413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653414 : term116 = term49.
Proof. exact (MK_COMB (@lem2653413) (@lem2653412)). Qed.
Lemma lem2653415 : term115 = term49.
Proof. exact (TRANS (@lem2653410) (@lem2653414)). Qed.
Lemma lem2653417 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2653418 : term110 = term121.
Proof. exact (@lem2653417 term50 term50). Qed.
Lemma lem2653419 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653420 : term118 = term50.
Proof. exact (EQ_MP (@lem2653419) (@lem940073)). Qed.
Lemma lem2653421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653422 : term116 = term49.
Proof. exact (MK_COMB (@lem2653421) (@lem2653420)). Qed.
Lemma lem2653423 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2653424 : term121 = term106.
Proof. exact (MK_COMB (@lem2653423) (@lem2653422)). Qed.
Lemma lem2653425 : term110 = term106.
Proof. exact (TRANS (@lem2653418) (@lem2653424)). Qed.
Lemma lem2653426 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653427 : term223 = term215.
Proof. exact (MK_COMB (@lem2653426) (@lem2653425)). Qed.
Lemma lem2653428 : term224 = term217.
Proof. exact (MK_COMB (@lem2653427) (@lem2653415)). Qed.
Lemma lem2653430 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2653431 : term217 = term45.
Proof. exact (@lem2653430 term50). Qed.
Lemma lem2653432 : term224 = term45.
Proof. exact (TRANS (@lem2653428) (@lem2653431)). Qed.
Lemma lem2653433 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2653434 : term226 = term227.
Proof. exact (MK_COMB (@lem2653433) (@lem2653432)). Qed.
Lemma lem2653435 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2653436 : term228 = term194.
Proof. exact (MK_COMB (@lem2653434) (@lem2653435)). Qed.
Lemma lem2653438 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653439 : term194 = term45.
Proof. exact (@lem2653438 term50). Qed.
Lemma lem2653440 : term228 = term45.
Proof. exact (TRANS (@lem2653436) (@lem2653439)). Qed.
Lemma lem2653442 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653443 : term115 = term116.
Proof. exact (@lem2653442 term50 term50). Qed.
Lemma lem2653444 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653445 : term118 = term50.
Proof. exact (EQ_MP (@lem2653444) (@lem940073)). Qed.
Lemma lem2653446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653447 : term116 = term49.
Proof. exact (MK_COMB (@lem2653446) (@lem2653445)). Qed.
Lemma lem2653448 : term115 = term49.
Proof. exact (TRANS (@lem2653443) (@lem2653447)). Qed.
Lemma lem2653449 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2653450 : term229 = term194.
Proof. exact (MK_COMB (@lem2653449) (@lem2653448)). Qed.
Lemma lem2653452 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653453 : term194 = term45.
Proof. exact (@lem2653452 term50). Qed.
Lemma lem2653454 : term229 = term45.
Proof. exact (TRANS (@lem2653450) (@lem2653453)). Qed.
Lemma lem2653455 : term45 = term229.
Proof. exact (SYM (@lem2653454)). Qed.
Lemma lem2653456 : term228 = term229.
Proof. exact (TRANS (@lem2653440) (@lem2653455)). Qed.
Lemma lem2653457 : term218 = term142.
Proof. exact (@lem2653407 (@lem2653456)). Qed.
Lemma lem2653458 : term217 = term142.
Proof. exact (TRANS (@lem2653373) (@lem2653457)). Qed.
Lemma lem2653460 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2653461 : term142 = term45.
Proof. exact (@lem2653460 term45). Qed.
Lemma lem2653462 : term217 = term45.
Proof. exact (TRANS (@lem2653458) (@lem2653461)). Qed.
Lemma lem2653463 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2653464 : term230 = term227.
Proof. exact (MK_COMB (@lem2653463) (@lem2653462)). Qed.
Lemma lem2653465 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2653466 (x : int) : (term214 x) = (term231 x).
Proof. exact (MK_COMB (@lem2653464) (@lem2653465 x)). Qed.
Lemma lem2653467 (x : int) : (term213 x) = (term231 x).
Proof. exact (TRANS (@lem2653364 x) (@lem2653466 x)). Qed.
Lemma lem2653468 (x : int) : (term231 x) = term45.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2653469 (x : int) : (term213 x) = term45.
Proof. exact (TRANS (@lem2653467 x) (@lem2653468 x)). Qed.
Lemma lem2653470 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653471 (x : int) : (term232 x) = term47.
Proof. exact (MK_COMB (@lem2653470) (@lem2653469 x)). Qed.
Lemma lem2653472 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2653473 (x : int) : (term284 x) = term285.
Proof. exact (MK_COMB (@lem2653471 x) (@lem2653472)). Qed.
Lemma lem2653474 (x : int) : (term304 x) = term285.
Proof. exact (TRANS (@lem2653363 x) (@lem2653473 x)). Qed.
Lemma lem2653475 : term285 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2653476 (x : int) : (term304 x) = term106.
Proof. exact (TRANS (@lem2653474 x) (@lem2653475)). Qed.
Lemma lem2653477 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2653478 (x : int) : (term305 x) = term287.
Proof. exact (MK_COMB (@lem2653477) (@lem2653476 x)). Qed.
Lemma lem2653479 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2653480 (x : int) : (term303 x) = term288.
Proof. exact (MK_COMB (@lem2653478 x) (@lem2653479)). Qed.
Lemma lem2653481 (x : int) (h1 : term295 x) : term288.
Proof. exact (EQ_MP (@lem2653480 x) (@lem2653362 x h1)). Qed.
Lemma lem2653483 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2653484 : term288 = term289.
Proof. exact (@lem2653483 term45 term106). Qed.
Lemma lem2653486 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2653487 : term106 = term107.
Proof. exact (@lem2653486 term50). Qed.
Lemma lem2653489 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653490 : term45 = term142.
Proof. exact (@lem2653489 (NUMERAL 0)). Qed.
Lemma lem2653491 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2653492 : term80 = term263.
Proof. exact (MK_COMB (@lem2653491) (@lem2653490)). Qed.
Lemma lem2653493 : term289 = term290.
Proof. exact (MK_COMB (@lem2653492) (@lem2653487)). Qed.
Lemma lem2653494 : term291.
Proof. exact (@lem1980026 term45 term49 term106 term49). Qed.
Lemma lem2653496 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653497 : term183 = term189.
Proof. exact (@lem2653496 (NUMERAL 0) term50). Qed.
Lemma lem2653498 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653499 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653500 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653499 h1) (fun h1 : term189 = True => @lem2653498)). Qed.
Lemma lem2653501 : term189 = True.
Proof. exact (EQ_MP (@lem2653500) (@lem2653498)). Qed.
Lemma lem2653502 : term183 = True.
Proof. exact (TRANS (@lem2653497) (@lem2653501)). Qed.
Lemma lem2653503 : True = term183.
Proof. exact (SYM (@lem2653502)). Qed.
Lemma lem2653504 : term183.
Proof. exact (EQ_MP (@lem2653503) (@lem0)). Qed.
Lemma lem2653505 : term292.
Proof. exact (@lem2653494 (@lem2653504)). Qed.
Lemma lem2653507 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653508 : term183 = term189.
Proof. exact (@lem2653507 (NUMERAL 0) term50). Qed.
Lemma lem2653509 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653510 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653511 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653510 h1) (fun h1 : term189 = True => @lem2653509)). Qed.
Lemma lem2653512 : term189 = True.
Proof. exact (EQ_MP (@lem2653511) (@lem2653509)). Qed.
Lemma lem2653513 : term183 = True.
Proof. exact (TRANS (@lem2653508) (@lem2653512)). Qed.
Lemma lem2653514 : True = term183.
Proof. exact (SYM (@lem2653513)). Qed.
Lemma lem2653515 : term183.
Proof. exact (EQ_MP (@lem2653514) (@lem0)). Qed.
Lemma lem2653516 : term290 = term293.
Proof. exact (@lem2653505 (@lem2653515)). Qed.
Lemma lem2653518 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2653519 : term110 = term121.
Proof. exact (@lem2653518 term50 term50). Qed.
Lemma lem2653520 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653521 : term118 = term50.
Proof. exact (EQ_MP (@lem2653520) (@lem940073)). Qed.
Lemma lem2653522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653523 : term116 = term49.
Proof. exact (MK_COMB (@lem2653522) (@lem2653521)). Qed.
Lemma lem2653524 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2653525 : term121 = term106.
Proof. exact (MK_COMB (@lem2653524) (@lem2653523)). Qed.
Lemma lem2653526 : term110 = term106.
Proof. exact (TRANS (@lem2653519) (@lem2653525)). Qed.
Lemma lem2653528 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653529 : term194 = term45.
Proof. exact (@lem2653528 term50). Qed.
Lemma lem2653530 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2653531 : term268 = term80.
Proof. exact (MK_COMB (@lem2653530) (@lem2653529)). Qed.
Lemma lem2653532 : term293 = term289.
Proof. exact (MK_COMB (@lem2653531) (@lem2653526)). Qed.
Lemma lem2653534 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2653535 : term289 = term294.
Proof. exact (@lem2653534 (NUMERAL 0) term50). Qed.
Lemma lem2653536 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653537 (h1 : term190 = (BIT1 0)) : (term50 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2653538 : (term190 = (BIT1 0)) = ((term50 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653537 h1) (fun h1 : (term50 = (NUMERAL 0)) = False => @lem2653536)). Qed.
Lemma lem2653539 : (term50 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2653538) (@lem2653536)). Qed.
Lemma lem2653540 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2653541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2653542 : term273 = (and True).
Proof. exact (MK_COMB (@lem2653541) (@lem2653540)). Qed.
Lemma lem2653543 : term294 = (True /\ False).
Proof. exact (MK_COMB (@lem2653542) (@lem2653539)). Qed.
Lemma lem2653545 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2653546 : term294 = False.
Proof. exact (TRANS (@lem2653543) (@lem2653545)). Qed.
Lemma lem2653547 : term289 = False.
Proof. exact (TRANS (@lem2653535) (@lem2653546)). Qed.
Lemma lem2653548 : term293 = False.
Proof. exact (TRANS (@lem2653532) (@lem2653547)). Qed.
Lemma lem2653549 : term290 = False.
Proof. exact (TRANS (@lem2653516) (@lem2653548)). Qed.
Lemma lem2653550 : term289 = False.
Proof. exact (TRANS (@lem2653493) (@lem2653549)). Qed.
Lemma lem2653551 : term288 = False.
Proof. exact (TRANS (@lem2653484) (@lem2653550)). Qed.
Lemma lem2653552 (x : int) (h1 : term295 x) : False.
Proof. exact (EQ_MP (@lem2653551) (@lem2653481 x h1)). Qed.
Lemma lem2653553 (x : int) (h1 : term306 x) : term306 x.
Proof. exact (h1). Qed.
Lemma lem2653554 (x : int) (h1 : term306 x) : term177 x.
Proof. exact (proj2 (@lem2653553 x h1)). Qed.
Lemma lem2653555 (x : int) (h1 : term306 x) : term161 x.
Proof. exact (proj1 (@lem2653553 x h1)). Qed.
Lemma lem2653556 (x : int) (h1 : term306 x) : term128 x.
Proof. exact (proj2 (@lem2653554 x h1)). Qed.
Lemma lem2653559 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2653560 : term182 = term183.
Proof. exact (@lem2653559 term45 term49). Qed.
Lemma lem2653562 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653563 : term49 = term103.
Proof. exact (@lem2653562 term50). Qed.
Lemma lem2653565 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653566 : term45 = term142.
Proof. exact (@lem2653565 (NUMERAL 0)). Qed.
Lemma lem2653567 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2653568 : term184 = term185.
Proof. exact (MK_COMB (@lem2653567) (@lem2653566)). Qed.
Lemma lem2653569 : term183 = term186.
Proof. exact (MK_COMB (@lem2653568) (@lem2653563)). Qed.
Lemma lem2653570 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2653572 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653573 : term183 = term189.
Proof. exact (@lem2653572 (NUMERAL 0) term50). Qed.
Lemma lem2653574 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653575 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653576 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653575 h1) (fun h1 : term189 = True => @lem2653574)). Qed.
Lemma lem2653577 : term189 = True.
Proof. exact (EQ_MP (@lem2653576) (@lem2653574)). Qed.
Lemma lem2653578 : term183 = True.
Proof. exact (TRANS (@lem2653573) (@lem2653577)). Qed.
Lemma lem2653579 : True = term183.
Proof. exact (SYM (@lem2653578)). Qed.
Lemma lem2653580 : term183.
Proof. exact (EQ_MP (@lem2653579) (@lem0)). Qed.
Lemma lem2653581 : term191.
Proof. exact (@lem2653570 (@lem2653580)). Qed.
Lemma lem2653583 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653584 : term183 = term189.
Proof. exact (@lem2653583 (NUMERAL 0) term50). Qed.
Lemma lem2653585 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653586 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653587 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653586 h1) (fun h1 : term189 = True => @lem2653585)). Qed.
Lemma lem2653588 : term189 = True.
Proof. exact (EQ_MP (@lem2653587) (@lem2653585)). Qed.
Lemma lem2653589 : term183 = True.
Proof. exact (TRANS (@lem2653584) (@lem2653588)). Qed.
Lemma lem2653590 : True = term183.
Proof. exact (SYM (@lem2653589)). Qed.
Lemma lem2653591 : term183.
Proof. exact (EQ_MP (@lem2653590) (@lem0)). Qed.
Lemma lem2653592 : term186 = term192.
Proof. exact (@lem2653581 (@lem2653591)). Qed.
Lemma lem2653594 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653595 : term115 = term116.
Proof. exact (@lem2653594 term50 term50). Qed.
Lemma lem2653596 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653597 : term118 = term50.
Proof. exact (EQ_MP (@lem2653596) (@lem940073)). Qed.
Lemma lem2653598 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653599 : term116 = term49.
Proof. exact (MK_COMB (@lem2653598) (@lem2653597)). Qed.
Lemma lem2653600 : term115 = term49.
Proof. exact (TRANS (@lem2653595) (@lem2653599)). Qed.
Lemma lem2653602 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653603 : term194 = term45.
Proof. exact (@lem2653602 term50). Qed.
Lemma lem2653604 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2653605 : term195 = term184.
Proof. exact (MK_COMB (@lem2653604) (@lem2653603)). Qed.
Lemma lem2653606 : term192 = term183.
Proof. exact (MK_COMB (@lem2653605) (@lem2653600)). Qed.
Lemma lem2653608 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653609 : term183 = term189.
Proof. exact (@lem2653608 (NUMERAL 0) term50). Qed.
Lemma lem2653610 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653611 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653612 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653611 h1) (fun h1 : term189 = True => @lem2653610)). Qed.
Lemma lem2653613 : term189 = True.
Proof. exact (EQ_MP (@lem2653612) (@lem2653610)). Qed.
Lemma lem2653614 : term183 = True.
Proof. exact (TRANS (@lem2653609) (@lem2653613)). Qed.
Lemma lem2653615 : term192 = True.
Proof. exact (TRANS (@lem2653606) (@lem2653614)). Qed.
Lemma lem2653616 : term186 = True.
Proof. exact (TRANS (@lem2653592) (@lem2653615)). Qed.
Lemma lem2653617 : term183 = True.
Proof. exact (TRANS (@lem2653569) (@lem2653616)). Qed.
Lemma lem2653618 : term182 = True.
Proof. exact (TRANS (@lem2653560) (@lem2653617)). Qed.
Lemma lem2653619 : True = term182.
Proof. exact (SYM (@lem2653618)). Qed.
Lemma lem2653620 : term182.
Proof. exact (EQ_MP (@lem2653619) (@lem0)). Qed.
Lemma lem2653621 (x : int) (h1 : term306 x) : term196 x.
Proof. exact (conj (@lem2653620) (@lem2653556 x h1)). Qed.
Lemma lem2653623 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2653624 (x : int) : term198 x.
Proof. exact (@lem2653623 term49 (term125 x)). Qed.
Lemma lem2653625 (x : int) (h1 : term306 x) : term199 x.
Proof. exact (@lem2653624 x (@lem2653621 x h1)). Qed.
Lemma lem2653626 (x : int) : (term200 x) = (term125 x).
Proof. exact (@lem1982733 (term125 x)). Qed.
Lemma lem2653627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2653628 (x : int) : (term201 x) = (term127 x).
Proof. exact (MK_COMB (@lem2653627) (@lem2653626 x)). Qed.
Lemma lem2653629 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2653630 (x : int) : (term199 x) = (term128 x).
Proof. exact (MK_COMB (@lem2653628 x) (@lem2653629)). Qed.
Lemma lem2653631 (x : int) (h1 : term306 x) : term128 x.
Proof. exact (EQ_MP (@lem2653630 x) (@lem2653625 x h1)). Qed.
Lemma lem2653633 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2653634 : term182 = term183.
Proof. exact (@lem2653633 term45 term49). Qed.
Lemma lem2653636 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653637 : term49 = term103.
Proof. exact (@lem2653636 term50). Qed.
Lemma lem2653639 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653640 : term45 = term142.
Proof. exact (@lem2653639 (NUMERAL 0)). Qed.
Lemma lem2653641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2653642 : term184 = term185.
Proof. exact (MK_COMB (@lem2653641) (@lem2653640)). Qed.
Lemma lem2653643 : term183 = term186.
Proof. exact (MK_COMB (@lem2653642) (@lem2653637)). Qed.
Lemma lem2653644 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2653646 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653647 : term183 = term189.
Proof. exact (@lem2653646 (NUMERAL 0) term50). Qed.
Lemma lem2653648 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653649 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653650 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653649 h1) (fun h1 : term189 = True => @lem2653648)). Qed.
Lemma lem2653651 : term189 = True.
Proof. exact (EQ_MP (@lem2653650) (@lem2653648)). Qed.
Lemma lem2653652 : term183 = True.
Proof. exact (TRANS (@lem2653647) (@lem2653651)). Qed.
Lemma lem2653653 : True = term183.
Proof. exact (SYM (@lem2653652)). Qed.
Lemma lem2653654 : term183.
Proof. exact (EQ_MP (@lem2653653) (@lem0)). Qed.
Lemma lem2653655 : term191.
Proof. exact (@lem2653644 (@lem2653654)). Qed.
Lemma lem2653657 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653658 : term183 = term189.
Proof. exact (@lem2653657 (NUMERAL 0) term50). Qed.
Lemma lem2653659 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653660 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653661 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653660 h1) (fun h1 : term189 = True => @lem2653659)). Qed.
Lemma lem2653662 : term189 = True.
Proof. exact (EQ_MP (@lem2653661) (@lem2653659)). Qed.
Lemma lem2653663 : term183 = True.
Proof. exact (TRANS (@lem2653658) (@lem2653662)). Qed.
Lemma lem2653664 : True = term183.
Proof. exact (SYM (@lem2653663)). Qed.
Lemma lem2653665 : term183.
Proof. exact (EQ_MP (@lem2653664) (@lem0)). Qed.
Lemma lem2653666 : term186 = term192.
Proof. exact (@lem2653655 (@lem2653665)). Qed.
Lemma lem2653668 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653669 : term115 = term116.
Proof. exact (@lem2653668 term50 term50). Qed.
Lemma lem2653670 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653671 : term118 = term50.
Proof. exact (EQ_MP (@lem2653670) (@lem940073)). Qed.
Lemma lem2653672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653673 : term116 = term49.
Proof. exact (MK_COMB (@lem2653672) (@lem2653671)). Qed.
Lemma lem2653674 : term115 = term49.
Proof. exact (TRANS (@lem2653669) (@lem2653673)). Qed.
Lemma lem2653676 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653677 : term194 = term45.
Proof. exact (@lem2653676 term50). Qed.
Lemma lem2653678 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2653679 : term195 = term184.
Proof. exact (MK_COMB (@lem2653678) (@lem2653677)). Qed.
Lemma lem2653680 : term192 = term183.
Proof. exact (MK_COMB (@lem2653679) (@lem2653674)). Qed.
Lemma lem2653682 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653683 : term183 = term189.
Proof. exact (@lem2653682 (NUMERAL 0) term50). Qed.
Lemma lem2653684 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653685 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653686 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653685 h1) (fun h1 : term189 = True => @lem2653684)). Qed.
Lemma lem2653687 : term189 = True.
Proof. exact (EQ_MP (@lem2653686) (@lem2653684)). Qed.
Lemma lem2653688 : term183 = True.
Proof. exact (TRANS (@lem2653683) (@lem2653687)). Qed.
Lemma lem2653689 : term192 = True.
Proof. exact (TRANS (@lem2653680) (@lem2653688)). Qed.
Lemma lem2653690 : term186 = True.
Proof. exact (TRANS (@lem2653666) (@lem2653689)). Qed.
Lemma lem2653691 : term183 = True.
Proof. exact (TRANS (@lem2653643) (@lem2653690)). Qed.
Lemma lem2653692 : term182 = True.
Proof. exact (TRANS (@lem2653634) (@lem2653691)). Qed.
Lemma lem2653693 : True = term182.
Proof. exact (SYM (@lem2653692)). Qed.
Lemma lem2653694 : term182.
Proof. exact (EQ_MP (@lem2653693) (@lem0)). Qed.
Lemma lem2653695 (x : int) (h1 : term306 x) : term307 x.
Proof. exact (conj (@lem2653694) (@lem2653555 x h1)). Qed.
Lemma lem2653697 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2653698 (x : int) : term308 x.
Proof. exact (@lem2653697 term49 (term158 x)). Qed.
Lemma lem2653699 (x : int) (h1 : term306 x) : term309 x.
Proof. exact (@lem2653698 x (@lem2653695 x h1)). Qed.
Lemma lem2653700 (x : int) : (term310 x) = (term158 x).
Proof. exact (@lem1982733 (term158 x)). Qed.
Lemma lem2653701 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2653702 (x : int) : (term311 x) = (term160 x).
Proof. exact (MK_COMB (@lem2653701) (@lem2653700 x)). Qed.
Lemma lem2653703 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2653704 (x : int) : (term309 x) = (term161 x).
Proof. exact (MK_COMB (@lem2653702 x) (@lem2653703)). Qed.
Lemma lem2653705 (x : int) (h1 : term306 x) : term161 x.
Proof. exact (EQ_MP (@lem2653704 x) (@lem2653699 x h1)). Qed.
Lemma lem2653706 (x : int) (h1 : term306 x) : term312 x.
Proof. exact (conj (@lem2653705 x h1) (@lem2653631 x h1)). Qed.
Lemma lem2653708 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2653709 (x : int) : term313 x.
Proof. exact (@lem2653708 (term158 x) (term125 x)). Qed.
Lemma lem2653710 (x : int) (h1 : term306 x) : term282 x.
Proof. exact (@lem2653709 x (@lem2653706 x h1)). Qed.
Lemma lem2653711 (x : int) : (term283 x) = (term284 x).
Proof. exact (@lem1982763 (term158 x) (real_of_int x) term106). Qed.
Lemma lem2653712 (x : int) : (term213 x) = (term214 x).
Proof. exact (@lem1982713 term106 (real_of_int x)). Qed.
Lemma lem2653714 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653715 : term49 = term103.
Proof. exact (@lem2653714 term50). Qed.
Lemma lem2653717 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2653718 : term106 = term107.
Proof. exact (@lem2653717 term50). Qed.
Lemma lem2653719 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653720 : term215 = term216.
Proof. exact (MK_COMB (@lem2653719) (@lem2653718)). Qed.
Lemma lem2653721 : term217 = term218.
Proof. exact (MK_COMB (@lem2653720) (@lem2653715)). Qed.
Lemma lem2653722 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2653724 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653725 : term183 = term189.
Proof. exact (@lem2653724 (NUMERAL 0) term50). Qed.
Lemma lem2653726 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653727 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653728 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653727 h1) (fun h1 : term189 = True => @lem2653726)). Qed.
Lemma lem2653729 : term189 = True.
Proof. exact (EQ_MP (@lem2653728) (@lem2653726)). Qed.
Lemma lem2653730 : term183 = True.
Proof. exact (TRANS (@lem2653725) (@lem2653729)). Qed.
Lemma lem2653731 : True = term183.
Proof. exact (SYM (@lem2653730)). Qed.
Lemma lem2653732 : term183.
Proof. exact (EQ_MP (@lem2653731) (@lem0)). Qed.
Lemma lem2653733 : term220.
Proof. exact (@lem2653722 (@lem2653732)). Qed.
Lemma lem2653735 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653736 : term183 = term189.
Proof. exact (@lem2653735 (NUMERAL 0) term50). Qed.
Lemma lem2653737 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653738 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653739 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653738 h1) (fun h1 : term189 = True => @lem2653737)). Qed.
Lemma lem2653740 : term189 = True.
Proof. exact (EQ_MP (@lem2653739) (@lem2653737)). Qed.
Lemma lem2653741 : term183 = True.
Proof. exact (TRANS (@lem2653736) (@lem2653740)). Qed.
Lemma lem2653742 : True = term183.
Proof. exact (SYM (@lem2653741)). Qed.
Lemma lem2653743 : term183.
Proof. exact (EQ_MP (@lem2653742) (@lem0)). Qed.
Lemma lem2653744 : term221.
Proof. exact (@lem2653733 (@lem2653743)). Qed.
Lemma lem2653746 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653747 : term183 = term189.
Proof. exact (@lem2653746 (NUMERAL 0) term50). Qed.
Lemma lem2653748 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653749 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653750 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653749 h1) (fun h1 : term189 = True => @lem2653748)). Qed.
Lemma lem2653751 : term189 = True.
Proof. exact (EQ_MP (@lem2653750) (@lem2653748)). Qed.
Lemma lem2653752 : term183 = True.
Proof. exact (TRANS (@lem2653747) (@lem2653751)). Qed.
Lemma lem2653753 : True = term183.
Proof. exact (SYM (@lem2653752)). Qed.
Lemma lem2653754 : term183.
Proof. exact (EQ_MP (@lem2653753) (@lem0)). Qed.
Lemma lem2653755 : term222.
Proof. exact (@lem2653744 (@lem2653754)). Qed.
Lemma lem2653757 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653758 : term115 = term116.
Proof. exact (@lem2653757 term50 term50). Qed.
Lemma lem2653759 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653760 : term118 = term50.
Proof. exact (EQ_MP (@lem2653759) (@lem940073)). Qed.
Lemma lem2653761 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653762 : term116 = term49.
Proof. exact (MK_COMB (@lem2653761) (@lem2653760)). Qed.
Lemma lem2653763 : term115 = term49.
Proof. exact (TRANS (@lem2653758) (@lem2653762)). Qed.
Lemma lem2653765 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2653766 : term110 = term121.
Proof. exact (@lem2653765 term50 term50). Qed.
Lemma lem2653767 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653768 : term118 = term50.
Proof. exact (EQ_MP (@lem2653767) (@lem940073)). Qed.
Lemma lem2653769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653770 : term116 = term49.
Proof. exact (MK_COMB (@lem2653769) (@lem2653768)). Qed.
Lemma lem2653771 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2653772 : term121 = term106.
Proof. exact (MK_COMB (@lem2653771) (@lem2653770)). Qed.
Lemma lem2653773 : term110 = term106.
Proof. exact (TRANS (@lem2653766) (@lem2653772)). Qed.
Lemma lem2653774 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653775 : term223 = term215.
Proof. exact (MK_COMB (@lem2653774) (@lem2653773)). Qed.
Lemma lem2653776 : term224 = term217.
Proof. exact (MK_COMB (@lem2653775) (@lem2653763)). Qed.
Lemma lem2653778 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2653779 : term217 = term45.
Proof. exact (@lem2653778 term50). Qed.
Lemma lem2653780 : term224 = term45.
Proof. exact (TRANS (@lem2653776) (@lem2653779)). Qed.
Lemma lem2653781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2653782 : term226 = term227.
Proof. exact (MK_COMB (@lem2653781) (@lem2653780)). Qed.
Lemma lem2653783 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2653784 : term228 = term194.
Proof. exact (MK_COMB (@lem2653782) (@lem2653783)). Qed.
Lemma lem2653786 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653787 : term194 = term45.
Proof. exact (@lem2653786 term50). Qed.
Lemma lem2653788 : term228 = term45.
Proof. exact (TRANS (@lem2653784) (@lem2653787)). Qed.
Lemma lem2653790 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2653791 : term115 = term116.
Proof. exact (@lem2653790 term50 term50). Qed.
Lemma lem2653792 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653793 : term118 = term50.
Proof. exact (EQ_MP (@lem2653792) (@lem940073)). Qed.
Lemma lem2653794 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653795 : term116 = term49.
Proof. exact (MK_COMB (@lem2653794) (@lem2653793)). Qed.
Lemma lem2653796 : term115 = term49.
Proof. exact (TRANS (@lem2653791) (@lem2653795)). Qed.
Lemma lem2653797 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2653798 : term229 = term194.
Proof. exact (MK_COMB (@lem2653797) (@lem2653796)). Qed.
Lemma lem2653800 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653801 : term194 = term45.
Proof. exact (@lem2653800 term50). Qed.
Lemma lem2653802 : term229 = term45.
Proof. exact (TRANS (@lem2653798) (@lem2653801)). Qed.
Lemma lem2653803 : term45 = term229.
Proof. exact (SYM (@lem2653802)). Qed.
Lemma lem2653804 : term228 = term229.
Proof. exact (TRANS (@lem2653788) (@lem2653803)). Qed.
Lemma lem2653805 : term218 = term142.
Proof. exact (@lem2653755 (@lem2653804)). Qed.
Lemma lem2653806 : term217 = term142.
Proof. exact (TRANS (@lem2653721) (@lem2653805)). Qed.
Lemma lem2653808 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2653809 : term142 = term45.
Proof. exact (@lem2653808 term45). Qed.
Lemma lem2653810 : term217 = term45.
Proof. exact (TRANS (@lem2653806) (@lem2653809)). Qed.
Lemma lem2653811 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2653812 : term230 = term227.
Proof. exact (MK_COMB (@lem2653811) (@lem2653810)). Qed.
Lemma lem2653813 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2653814 (x : int) : (term214 x) = (term231 x).
Proof. exact (MK_COMB (@lem2653812) (@lem2653813 x)). Qed.
Lemma lem2653815 (x : int) : (term213 x) = (term231 x).
Proof. exact (TRANS (@lem2653712 x) (@lem2653814 x)). Qed.
Lemma lem2653816 (x : int) : (term231 x) = term45.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2653817 (x : int) : (term213 x) = term45.
Proof. exact (TRANS (@lem2653815 x) (@lem2653816 x)). Qed.
Lemma lem2653818 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653819 (x : int) : (term232 x) = term47.
Proof. exact (MK_COMB (@lem2653818) (@lem2653817 x)). Qed.
Lemma lem2653820 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2653821 (x : int) : (term284 x) = term285.
Proof. exact (MK_COMB (@lem2653819 x) (@lem2653820)). Qed.
Lemma lem2653822 (x : int) : (term283 x) = term285.
Proof. exact (TRANS (@lem2653711 x) (@lem2653821 x)). Qed.
Lemma lem2653823 : term285 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2653824 (x : int) : (term283 x) = term106.
Proof. exact (TRANS (@lem2653822 x) (@lem2653823)). Qed.
Lemma lem2653825 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2653826 (x : int) : (term286 x) = term287.
Proof. exact (MK_COMB (@lem2653825) (@lem2653824 x)). Qed.
Lemma lem2653827 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2653828 (x : int) : (term282 x) = term288.
Proof. exact (MK_COMB (@lem2653826 x) (@lem2653827)). Qed.
Lemma lem2653829 (x : int) (h1 : term306 x) : term288.
Proof. exact (EQ_MP (@lem2653828 x) (@lem2653710 x h1)). Qed.
Lemma lem2653831 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2653832 : term288 = term289.
Proof. exact (@lem2653831 term45 term106). Qed.
Lemma lem2653834 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2653835 : term106 = term107.
Proof. exact (@lem2653834 term50). Qed.
Lemma lem2653837 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2653838 : term45 = term142.
Proof. exact (@lem2653837 (NUMERAL 0)). Qed.
Lemma lem2653839 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2653840 : term80 = term263.
Proof. exact (MK_COMB (@lem2653839) (@lem2653838)). Qed.
Lemma lem2653841 : term289 = term290.
Proof. exact (MK_COMB (@lem2653840) (@lem2653835)). Qed.
Lemma lem2653842 : term291.
Proof. exact (@lem1980026 term45 term49 term106 term49). Qed.
Lemma lem2653844 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653845 : term183 = term189.
Proof. exact (@lem2653844 (NUMERAL 0) term50). Qed.
Lemma lem2653846 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653847 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653848 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653847 h1) (fun h1 : term189 = True => @lem2653846)). Qed.
Lemma lem2653849 : term189 = True.
Proof. exact (EQ_MP (@lem2653848) (@lem2653846)). Qed.
Lemma lem2653850 : term183 = True.
Proof. exact (TRANS (@lem2653845) (@lem2653849)). Qed.
Lemma lem2653851 : True = term183.
Proof. exact (SYM (@lem2653850)). Qed.
Lemma lem2653852 : term183.
Proof. exact (EQ_MP (@lem2653851) (@lem0)). Qed.
Lemma lem2653853 : term292.
Proof. exact (@lem2653842 (@lem2653852)). Qed.
Lemma lem2653855 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2653856 : term183 = term189.
Proof. exact (@lem2653855 (NUMERAL 0) term50). Qed.
Lemma lem2653857 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653858 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2653859 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653858 h1) (fun h1 : term189 = True => @lem2653857)). Qed.
Lemma lem2653860 : term189 = True.
Proof. exact (EQ_MP (@lem2653859) (@lem2653857)). Qed.
Lemma lem2653861 : term183 = True.
Proof. exact (TRANS (@lem2653856) (@lem2653860)). Qed.
Lemma lem2653862 : True = term183.
Proof. exact (SYM (@lem2653861)). Qed.
Lemma lem2653863 : term183.
Proof. exact (EQ_MP (@lem2653862) (@lem0)). Qed.
Lemma lem2653864 : term290 = term293.
Proof. exact (@lem2653853 (@lem2653863)). Qed.
Lemma lem2653866 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2653867 : term110 = term121.
Proof. exact (@lem2653866 term50 term50). Qed.
Lemma lem2653868 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2653869 : term118 = term50.
Proof. exact (EQ_MP (@lem2653868) (@lem940073)). Qed.
Lemma lem2653870 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2653871 : term116 = term49.
Proof. exact (MK_COMB (@lem2653870) (@lem2653869)). Qed.
Lemma lem2653872 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2653873 : term121 = term106.
Proof. exact (MK_COMB (@lem2653872) (@lem2653871)). Qed.
Lemma lem2653874 : term110 = term106.
Proof. exact (TRANS (@lem2653867) (@lem2653873)). Qed.
Lemma lem2653876 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2653877 : term194 = term45.
Proof. exact (@lem2653876 term50). Qed.
Lemma lem2653878 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2653879 : term268 = term80.
Proof. exact (MK_COMB (@lem2653878) (@lem2653877)). Qed.
Lemma lem2653880 : term293 = term289.
Proof. exact (MK_COMB (@lem2653879) (@lem2653874)). Qed.
Lemma lem2653882 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2653883 : term289 = term294.
Proof. exact (@lem2653882 (NUMERAL 0) term50). Qed.
Lemma lem2653884 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2653885 (h1 : term190 = (BIT1 0)) : (term50 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2653886 : (term190 = (BIT1 0)) = ((term50 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2653885 h1) (fun h1 : (term50 = (NUMERAL 0)) = False => @lem2653884)). Qed.
Lemma lem2653887 : (term50 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2653886) (@lem2653884)). Qed.
Lemma lem2653888 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2653889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2653890 : term273 = (and True).
Proof. exact (MK_COMB (@lem2653889) (@lem2653888)). Qed.
Lemma lem2653891 : term294 = (True /\ False).
Proof. exact (MK_COMB (@lem2653890) (@lem2653887)). Qed.
Lemma lem2653893 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2653894 : term294 = False.
Proof. exact (TRANS (@lem2653891) (@lem2653893)). Qed.
Lemma lem2653895 : term289 = False.
Proof. exact (TRANS (@lem2653883) (@lem2653894)). Qed.
Lemma lem2653896 : term293 = False.
Proof. exact (TRANS (@lem2653880) (@lem2653895)). Qed.
Lemma lem2653897 : term290 = False.
Proof. exact (TRANS (@lem2653864) (@lem2653896)). Qed.
Lemma lem2653898 : term289 = False.
Proof. exact (TRANS (@lem2653841) (@lem2653897)). Qed.
Lemma lem2653899 : term288 = False.
Proof. exact (TRANS (@lem2653832) (@lem2653898)). Qed.
Lemma lem2653900 (x : int) (h1 : term306 x) : False.
Proof. exact (EQ_MP (@lem2653899) (@lem2653829 x h1)). Qed.
Lemma lem2653901 (x : int) (h1 : term175 x) : False.
Proof. exact (or_elim (@lem2653204 x h1) (fun h0 : term295 x => @lem2653552 x h0) (fun h0 : term306 x => @lem2653900 x h0)). Qed.
Lemma lem2653902 (x : int) (h1 : term180 x) : False.
Proof. exact (or_elim (@lem2652448 x h1) (fun h0 : term178 x => @lem2653203 x h0) (fun h0 : term175 x => @lem2653901 x h0)). Qed.
Lemma lem2653904 (x : int) (h1 : term180 x) : term180 x.
Proof. exact (h1). Qed.
Lemma lem2653905 (x : int) (h1 : term180 x) : (term180 x) = False.
Proof. exact (prop_ext (fun h2 : term180 x => @lem2653902 x h1) (fun h2 : False => @lem2653904 x h1)). Qed.
Lemma lem2653906 (x : int) (h1 : term180 x) : False.
Proof. exact (EQ_MP (@lem2653905 x h1) (@lem2653904 x h1)). Qed.
Lemma lem2653907 (x : int) (h1 : term96 x) : term96 x.
Proof. exact (h1). Qed.
Lemma lem2653908 (x : int) (h1 : term96 x) : term180 x.
Proof. exact (EQ_MP (@lem2652426 x) (@lem2653907 x h1)). Qed.
Lemma lem2653909 (x : int) (h1 : term96 x) : (term180 x) = False.
Proof. exact (prop_ext (fun h2 : term180 x => @lem2653906 x h2) (fun h2 : False => @lem2653908 x h1)). Qed.
Lemma lem2653910 (x : int) (h1 : term96 x) : False.
Proof. exact (EQ_MP (@lem2653909 x h1) (@lem2653908 x h1)). Qed.
Lemma lem2653911 (x : int) : term314 x.
Proof. exact (fun h0 : term96 x => @lem2653910 x h0). Qed.
Lemma lem2653912 (x : int) : term315 x.
Proof. exact (@lem1386578 (term316 x)). Qed.
Lemma lem2653915 (x : int) : term316 x.
Proof. exact (@lem2653912 x (@lem2653911 x)). Qed.
Lemma lem2653916 (x : int) : (term94 x) = (term32 x).
Proof. exact (SYM (@lem2651910 x)). Qed.
Lemma lem2653917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2653918 (x : int) : (term316 x) = (term14 x).
Proof. exact (MK_COMB (@lem2653917) (@lem2653916 x)). Qed.
Lemma lem2653919 (x : int) : term14 x.
Proof. exact (EQ_MP (@lem2653918 x) (@lem2653915 x)). Qed.
Lemma lem2653921 (n : int) (m : int) (h1 : term317 n m) : term317 n m.
Proof. exact (h1). Qed.
Lemma lem2653922 (n : int) (m : int) (h1 : int_le n m) : int_le n m.
Proof. exact (h1). Qed.
Lemma lem2653923 (n : int) (h1 : term15 n) : term15 n.
Proof. exact (h1). Qed.
Lemma lem2653925 (x : int) : (term15 x) = (term16 x).
Proof. exact (EQ_MP (@lem2651697 x) (@lem2653919 x)). Qed.
Lemma lem2653926 (m : int) (n : int) : (term318 m n) = (term319 m n).
Proof. exact (@lem2653925 (div m n)). Qed.
Lemma lem2653931 (m : int) (n : int) : (term319 m n) = (term318 m n).
Proof. exact (SYM (@lem2653926 m n)). Qed.
Lemma lem2653933 (m : int) (n : int) : term9 m n.
Proof. exact (EQ_MP (@lem2651695 m n) (@lem2651694 m n)). Qed.
Lemma lem2653934 (m : int) (n : int) : (term320 m n) = (term321 m n).
Proof. exact (@lem2318604 (term321 m n)). Qed.
Lemma lem2653954 (m : int) (n : int) : (term322 m n) = (term323 m n).
Proof. exact (@lem17045 (term22 m) (term22 n)). Qed.
Lemma lem2653956 (n : int) (m : int) : (term324 n m) = (term324 n m).
Proof. exact (eq_refl (term324 n m)). Qed.
Lemma lem2653957 (m : int) (n : int) : (term325 m n) = (term326 m n).
Proof. exact (MK_COMB (@lem2653956 n m) (@lem2653954 m n)). Qed.
Lemma lem2653958 (m : int) (n : int) : (term327 m n) = (term325 m n).
Proof. exact (@lem17362 (int_le n m) (term10 m n)). Qed.
Lemma lem2653959 (m : int) (n : int) : (term327 m n) = (term326 m n).
Proof. exact (TRANS (@lem2653958 m n) (@lem2653957 m n)). Qed.
Lemma lem2653961 (n : int) : (term25 n) = (term25 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem2653962 (m : int) (n : int) : (term328 m n) = (term329 m n).
Proof. exact (MK_COMB (@lem2653961 n) (@lem2653959 m n)). Qed.
Lemma lem2653963 (m : int) (n : int) : (term330 m n) = (term328 m n).
Proof. exact (@lem17362 (term15 n) (term331 m n)). Qed.
Lemma lem2653983 (m : int) (n : int) : (term330 m n) = (term329 m n).
Proof. exact (TRANS (@lem2653963 m n) (@lem2653962 m n)). Qed.
Lemma lem2653985 (x : int) (y : int) : (int_lt x y) = (term33 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2653986 (n : int) : (term15 n) = (term34 n).
Proof. exact (@lem2653985 term3 n). Qed.
Lemma lem2653988 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2653989 (n : int) : (term34 n) = (term36 n).
Proof. exact (@lem2653988 term37 n). Qed.
Lemma lem2653991 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2653992 : term40 = term41.
Proof. exact (@lem2653991 term3 term42). Qed.
Lemma lem2653994 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2653995 : term44 = term45.
Proof. exact (@lem2653994 (NUMERAL 0)). Qed.
Lemma lem2653996 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2653997 : term46 = term47.
Proof. exact (MK_COMB (@lem2653996) (@lem2653995)). Qed.
Lemma lem2653999 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2654000 : term48 = term49.
Proof. exact (@lem2653999 term50). Qed.
Lemma lem2654001 : term41 = term51.
Proof. exact (MK_COMB (@lem2653997) (@lem2654000)). Qed.
Lemma lem2654002 : term40 = term51.
Proof. exact (TRANS (@lem2653992) (@lem2654001)). Qed.
Lemma lem2654003 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2654004 : term52 = term53.
Proof. exact (MK_COMB (@lem2654003) (@lem2654002)). Qed.
Lemma lem2654005 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2654006 (n : int) : (term36 n) = (term54 n).
Proof. exact (MK_COMB (@lem2654004) (@lem2654005 n)). Qed.
Lemma lem2654007 (n : int) : (term34 n) = (term54 n).
Proof. exact (TRANS (@lem2653989 n) (@lem2654006 n)). Qed.
Lemma lem2654008 (n : int) : (term15 n) = (term54 n).
Proof. exact (TRANS (@lem2653986 n) (@lem2654007 n)). Qed.
Lemma lem2654011 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2654013 (n : int) (m : int) : (int_le n m) = (term35 n m).
Proof. exact (@lem2654011 n m). Qed.
Lemma lem2654015 (y : int) (x : int) : (term55 x y) = (term33 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2654016 (m : int) : (term56 m) = (term57 m).
Proof. exact (@lem2654015 m term3). Qed.
Lemma lem2654018 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2654019 (m : int) : (term57 m) = (term58 m).
Proof. exact (@lem2654018 (term59 m) term3). Qed.
Lemma lem2654021 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2654022 (m : int) : (term60 m) = (term61 m).
Proof. exact (@lem2654021 m term42). Qed.
Lemma lem2654024 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2654025 : term48 = term49.
Proof. exact (@lem2654024 term50). Qed.
Lemma lem2654026 (m : int) : (term62 m) = (term62 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem2654027 (m : int) : (term61 m) = (term63 m).
Proof. exact (MK_COMB (@lem2654026 m) (@lem2654025)). Qed.
Lemma lem2654028 (m : int) : (term60 m) = (term63 m).
Proof. exact (TRANS (@lem2654022 m) (@lem2654027 m)). Qed.
Lemma lem2654029 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2654030 (m : int) : (term64 m) = (term65 m).
Proof. exact (MK_COMB (@lem2654029) (@lem2654028 m)). Qed.
Lemma lem2654032 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2654033 : term44 = term45.
Proof. exact (@lem2654032 (NUMERAL 0)). Qed.
Lemma lem2654034 (m : int) : (term58 m) = (term66 m).
Proof. exact (MK_COMB (@lem2654030 m) (@lem2654033)). Qed.
Lemma lem2654035 (m : int) : (term57 m) = (term66 m).
Proof. exact (TRANS (@lem2654019 m) (@lem2654034 m)). Qed.
Lemma lem2654036 (m : int) : (term56 m) = (term66 m).
Proof. exact (TRANS (@lem2654016 m) (@lem2654035 m)). Qed.
Lemma lem2654038 (y : int) (x : int) : (term55 x y) = (term33 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2654039 (n : int) : (term56 n) = (term57 n).
Proof. exact (@lem2654038 n term3). Qed.
Lemma lem2654041 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2654042 (n : int) : (term57 n) = (term58 n).
Proof. exact (@lem2654041 (term59 n) term3). Qed.
Lemma lem2654044 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2654045 (n : int) : (term60 n) = (term61 n).
Proof. exact (@lem2654044 n term42). Qed.
Lemma lem2654047 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2654048 : term48 = term49.
Proof. exact (@lem2654047 term50). Qed.
Lemma lem2654049 (n : int) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem2654050 (n : int) : (term61 n) = (term63 n).
Proof. exact (MK_COMB (@lem2654049 n) (@lem2654048)). Qed.
Lemma lem2654051 (n : int) : (term60 n) = (term63 n).
Proof. exact (TRANS (@lem2654045 n) (@lem2654050 n)). Qed.
Lemma lem2654052 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2654053 (n : int) : (term64 n) = (term65 n).
Proof. exact (MK_COMB (@lem2654052) (@lem2654051 n)). Qed.
Lemma lem2654055 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2654056 : term44 = term45.
Proof. exact (@lem2654055 (NUMERAL 0)). Qed.
Lemma lem2654057 (n : int) : (term58 n) = (term66 n).
Proof. exact (MK_COMB (@lem2654053 n) (@lem2654056)). Qed.
Lemma lem2654058 (n : int) : (term57 n) = (term66 n).
Proof. exact (TRANS (@lem2654042 n) (@lem2654057 n)). Qed.
Lemma lem2654059 (n : int) : (term56 n) = (term66 n).
Proof. exact (TRANS (@lem2654039 n) (@lem2654058 n)). Qed.
Lemma lem2654060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2654061 (m : int) : (term18 m) = (term68 m).
Proof. exact (MK_COMB (@lem2654060) (@lem2654036 m)). Qed.
Lemma lem2654062 (m : int) (n : int) : (term323 m n) = (term332 m n).
Proof. exact (MK_COMB (@lem2654061 m) (@lem2654059 n)). Qed.
Lemma lem2654063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2654064 (n : int) (m : int) : (term324 n m) = (term333 n m).
Proof. exact (MK_COMB (@lem2654063) (@lem2654013 n m)). Qed.
Lemma lem2654065 (m : int) (n : int) : (term326 m n) = (term334 m n).
Proof. exact (MK_COMB (@lem2654064 n m) (@lem2654062 m n)). Qed.
Lemma lem2654066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2654067 (n : int) : (term25 n) = (term70 n).
Proof. exact (MK_COMB (@lem2654066) (@lem2654008 n)). Qed.
Lemma lem2654068 (m : int) (n : int) : (term329 m n) = (term335 m n).
Proof. exact (MK_COMB (@lem2654067 n) (@lem2654065 m n)). Qed.
Lemma lem2654069 (m : int) (n : int) : (term330 m n) = (term335 m n).
Proof. exact (TRANS (@lem2653983 m n) (@lem2654068 m n)). Qed.
Lemma lem2654073 (t : Prop) : (term95 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2654109 (m : int) (n : int) : (term336 m n) = (term335 m n).
Proof. exact (@lem2654073 (term335 m n)). Qed.
Lemma lem2654110 (n : int) : (term54 n) = (term97 n).
Proof. exact (@lem1988287 (real_of_int n) term51). Qed.
Lemma lem2654117 : term51 = term49.
Proof. exact (@lem1982721 term49). Qed.
Lemma lem2654120 (n : int) : (term98 n) = (term98 n).
Proof. exact (eq_refl (term98 n)). Qed.
Lemma lem2654121 (n : int) : (term99 n) = (term100 n).
Proof. exact (MK_COMB (@lem2654120 n) (@lem2654117)). Qed.
Lemma lem2654122 (n : int) : (term100 n) = (term101 n).
Proof. exact (@lem1982792 (real_of_int n) term49). Qed.
Lemma lem2654124 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654125 : term49 = term103.
Proof. exact (@lem2654124 term50). Qed.
Lemma lem2654127 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2654128 : term106 = term107.
Proof. exact (@lem2654127 term50). Qed.
Lemma lem2654129 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2654130 : term108 = term109.
Proof. exact (MK_COMB (@lem2654129) (@lem2654128)). Qed.
Lemma lem2654131 : term110 = term111.
Proof. exact (MK_COMB (@lem2654130) (@lem2654125)). Qed.
Lemma lem2654132 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2654134 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654135 : term115 = term116.
Proof. exact (@lem2654134 term50 term50). Qed.
Lemma lem2654136 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654137 : term118 = term50.
Proof. exact (EQ_MP (@lem2654136) (@lem940073)). Qed.
Lemma lem2654138 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654139 : term116 = term49.
Proof. exact (MK_COMB (@lem2654138) (@lem2654137)). Qed.
Lemma lem2654140 : term115 = term49.
Proof. exact (TRANS (@lem2654135) (@lem2654139)). Qed.
Lemma lem2654142 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2654143 : term110 = term121.
Proof. exact (@lem2654142 term50 term50). Qed.
Lemma lem2654144 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654145 : term118 = term50.
Proof. exact (EQ_MP (@lem2654144) (@lem940073)). Qed.
Lemma lem2654146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654147 : term116 = term49.
Proof. exact (MK_COMB (@lem2654146) (@lem2654145)). Qed.
Lemma lem2654148 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2654149 : term121 = term106.
Proof. exact (MK_COMB (@lem2654148) (@lem2654147)). Qed.
Lemma lem2654150 : term110 = term106.
Proof. exact (TRANS (@lem2654143) (@lem2654149)). Qed.
Lemma lem2654151 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2654152 : term122 = term123.
Proof. exact (MK_COMB (@lem2654151) (@lem2654150)). Qed.
Lemma lem2654153 : term112 = term107.
Proof. exact (MK_COMB (@lem2654152) (@lem2654140)). Qed.
Lemma lem2654154 : term111 = term107.
Proof. exact (TRANS (@lem2654132) (@lem2654153)). Qed.
Lemma lem2654155 : term110 = term107.
Proof. exact (TRANS (@lem2654131) (@lem2654154)). Qed.
Lemma lem2654157 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2654158 : term107 = term106.
Proof. exact (@lem2654157 term106). Qed.
Lemma lem2654159 : term110 = term106.
Proof. exact (TRANS (@lem2654155) (@lem2654158)). Qed.
Lemma lem2654160 (n : int) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem2654163 (n : int) : (term101 n) = (term125 n).
Proof. exact (MK_COMB (@lem2654160 n) (@lem2654159)). Qed.
Lemma lem2654164 (n : int) : (term100 n) = (term125 n).
Proof. exact (TRANS (@lem2654122 n) (@lem2654163 n)). Qed.
Lemma lem2654165 (n : int) : (term99 n) = (term125 n).
Proof. exact (TRANS (@lem2654121 n) (@lem2654164 n)). Qed.
Lemma lem2654166 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654167 (n : int) : (term126 n) = (term127 n).
Proof. exact (MK_COMB (@lem2654166) (@lem2654165 n)). Qed.
Lemma lem2654168 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654169 (n : int) : (term97 n) = (term128 n).
Proof. exact (MK_COMB (@lem2654167 n) (@lem2654168)). Qed.
Lemma lem2654170 (n : int) : (term54 n) = (term128 n).
Proof. exact (TRANS (@lem2654110 n) (@lem2654169 n)). Qed.
Lemma lem2654171 (m : int) (n : int) : (term35 n m) = (term337 m n).
Proof. exact (@lem1988287 (real_of_int m) (real_of_int n)). Qed.
Lemma lem2654184 (m : int) (n : int) : (term338 m n) = (term339 m n).
Proof. exact (@lem1982792 (real_of_int m) (real_of_int n)). Qed.
Lemma lem2654185 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654186 (m : int) (n : int) : (term340 m n) = (term341 m n).
Proof. exact (MK_COMB (@lem2654185) (@lem2654184 m n)). Qed.
Lemma lem2654187 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654188 (m : int) (n : int) : (term337 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem2654186 m n) (@lem2654187)). Qed.
Lemma lem2654189 (m : int) (n : int) : (term35 n m) = (term342 m n).
Proof. exact (TRANS (@lem2654171 m n) (@lem2654188 m n)). Qed.
Lemma lem2654190 (m : int) : (term66 m) = (term129 m).
Proof. exact (@lem1988287 term45 (term63 m)). Qed.
Lemma lem2654202 (m : int) : (term130 m) = (term131 m).
Proof. exact (@lem1982792 term45 (term63 m)). Qed.
Lemma lem2654203 (m : int) : (term132 m) = (term133 m).
Proof. exact (@lem1982781 (real_of_int m) term106 term49). Qed.
Lemma lem2654205 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654206 : term49 = term103.
Proof. exact (@lem2654205 term50). Qed.
Lemma lem2654208 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2654209 : term106 = term107.
Proof. exact (@lem2654208 term50). Qed.
Lemma lem2654210 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2654211 : term108 = term109.
Proof. exact (MK_COMB (@lem2654210) (@lem2654209)). Qed.
Lemma lem2654212 : term110 = term111.
Proof. exact (MK_COMB (@lem2654211) (@lem2654206)). Qed.
Lemma lem2654213 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2654215 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654216 : term115 = term116.
Proof. exact (@lem2654215 term50 term50). Qed.
Lemma lem2654217 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654218 : term118 = term50.
Proof. exact (EQ_MP (@lem2654217) (@lem940073)). Qed.
Lemma lem2654219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654220 : term116 = term49.
Proof. exact (MK_COMB (@lem2654219) (@lem2654218)). Qed.
Lemma lem2654221 : term115 = term49.
Proof. exact (TRANS (@lem2654216) (@lem2654220)). Qed.
Lemma lem2654223 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2654224 : term110 = term121.
Proof. exact (@lem2654223 term50 term50). Qed.
Lemma lem2654225 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654226 : term118 = term50.
Proof. exact (EQ_MP (@lem2654225) (@lem940073)). Qed.
Lemma lem2654227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654228 : term116 = term49.
Proof. exact (MK_COMB (@lem2654227) (@lem2654226)). Qed.
Lemma lem2654229 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2654230 : term121 = term106.
Proof. exact (MK_COMB (@lem2654229) (@lem2654228)). Qed.
Lemma lem2654231 : term110 = term106.
Proof. exact (TRANS (@lem2654224) (@lem2654230)). Qed.
Lemma lem2654232 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2654233 : term122 = term123.
Proof. exact (MK_COMB (@lem2654232) (@lem2654231)). Qed.
Lemma lem2654234 : term112 = term107.
Proof. exact (MK_COMB (@lem2654233) (@lem2654221)). Qed.
Lemma lem2654235 : term111 = term107.
Proof. exact (TRANS (@lem2654213) (@lem2654234)). Qed.
Lemma lem2654236 : term110 = term107.
Proof. exact (TRANS (@lem2654212) (@lem2654235)). Qed.
Lemma lem2654238 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2654239 : term107 = term106.
Proof. exact (@lem2654238 term106). Qed.
Lemma lem2654240 : term110 = term106.
Proof. exact (TRANS (@lem2654236) (@lem2654239)). Qed.
Lemma lem2654243 (m : int) : (term134 m) = (term134 m).
Proof. exact (eq_refl (term134 m)). Qed.
Lemma lem2654244 (m : int) : (term133 m) = (term135 m).
Proof. exact (MK_COMB (@lem2654243 m) (@lem2654240)). Qed.
Lemma lem2654245 (m : int) : (term132 m) = (term135 m).
Proof. exact (TRANS (@lem2654203 m) (@lem2654244 m)). Qed.
Lemma lem2654246 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2654247 (m : int) : (term131 m) = (term136 m).
Proof. exact (MK_COMB (@lem2654246) (@lem2654245 m)). Qed.
Lemma lem2654248 (m : int) : (term136 m) = (term135 m).
Proof. exact (@lem1982721 (term135 m)). Qed.
Lemma lem2654249 (m : int) : (term131 m) = (term135 m).
Proof. exact (TRANS (@lem2654247 m) (@lem2654248 m)). Qed.
Lemma lem2654251 (m : int) : (term130 m) = (term135 m).
Proof. exact (TRANS (@lem2654202 m) (@lem2654249 m)). Qed.
Lemma lem2654252 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654253 (m : int) : (term137 m) = (term138 m).
Proof. exact (MK_COMB (@lem2654252) (@lem2654251 m)). Qed.
Lemma lem2654254 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654255 (m : int) : (term129 m) = (term139 m).
Proof. exact (MK_COMB (@lem2654253 m) (@lem2654254)). Qed.
Lemma lem2654256 (m : int) : (term66 m) = (term139 m).
Proof. exact (TRANS (@lem2654190 m) (@lem2654255 m)). Qed.
Lemma lem2654257 (n : int) : (term66 n) = (term129 n).
Proof. exact (@lem1988287 term45 (term63 n)). Qed.
Lemma lem2654269 (n : int) : (term130 n) = (term131 n).
Proof. exact (@lem1982792 term45 (term63 n)). Qed.
Lemma lem2654270 (n : int) : (term132 n) = (term133 n).
Proof. exact (@lem1982781 (real_of_int n) term106 term49). Qed.
Lemma lem2654272 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654273 : term49 = term103.
Proof. exact (@lem2654272 term50). Qed.
Lemma lem2654275 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2654276 : term106 = term107.
Proof. exact (@lem2654275 term50). Qed.
Lemma lem2654277 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2654278 : term108 = term109.
Proof. exact (MK_COMB (@lem2654277) (@lem2654276)). Qed.
Lemma lem2654279 : term110 = term111.
Proof. exact (MK_COMB (@lem2654278) (@lem2654273)). Qed.
Lemma lem2654280 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2654282 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654283 : term115 = term116.
Proof. exact (@lem2654282 term50 term50). Qed.
Lemma lem2654284 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654285 : term118 = term50.
Proof. exact (EQ_MP (@lem2654284) (@lem940073)). Qed.
Lemma lem2654286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654287 : term116 = term49.
Proof. exact (MK_COMB (@lem2654286) (@lem2654285)). Qed.
Lemma lem2654288 : term115 = term49.
Proof. exact (TRANS (@lem2654283) (@lem2654287)). Qed.
Lemma lem2654290 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2654291 : term110 = term121.
Proof. exact (@lem2654290 term50 term50). Qed.
Lemma lem2654292 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654293 : term118 = term50.
Proof. exact (EQ_MP (@lem2654292) (@lem940073)). Qed.
Lemma lem2654294 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654295 : term116 = term49.
Proof. exact (MK_COMB (@lem2654294) (@lem2654293)). Qed.
Lemma lem2654296 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2654297 : term121 = term106.
Proof. exact (MK_COMB (@lem2654296) (@lem2654295)). Qed.
Lemma lem2654298 : term110 = term106.
Proof. exact (TRANS (@lem2654291) (@lem2654297)). Qed.
Lemma lem2654299 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2654300 : term122 = term123.
Proof. exact (MK_COMB (@lem2654299) (@lem2654298)). Qed.
Lemma lem2654301 : term112 = term107.
Proof. exact (MK_COMB (@lem2654300) (@lem2654288)). Qed.
Lemma lem2654302 : term111 = term107.
Proof. exact (TRANS (@lem2654280) (@lem2654301)). Qed.
Lemma lem2654303 : term110 = term107.
Proof. exact (TRANS (@lem2654279) (@lem2654302)). Qed.
Lemma lem2654305 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2654306 : term107 = term106.
Proof. exact (@lem2654305 term106). Qed.
Lemma lem2654307 : term110 = term106.
Proof. exact (TRANS (@lem2654303) (@lem2654306)). Qed.
Lemma lem2654310 (n : int) : (term134 n) = (term134 n).
Proof. exact (eq_refl (term134 n)). Qed.
Lemma lem2654311 (n : int) : (term133 n) = (term135 n).
Proof. exact (MK_COMB (@lem2654310 n) (@lem2654307)). Qed.
Lemma lem2654312 (n : int) : (term132 n) = (term135 n).
Proof. exact (TRANS (@lem2654270 n) (@lem2654311 n)). Qed.
Lemma lem2654313 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem2654314 (n : int) : (term131 n) = (term136 n).
Proof. exact (MK_COMB (@lem2654313) (@lem2654312 n)). Qed.
Lemma lem2654315 (n : int) : (term136 n) = (term135 n).
Proof. exact (@lem1982721 (term135 n)). Qed.
Lemma lem2654316 (n : int) : (term131 n) = (term135 n).
Proof. exact (TRANS (@lem2654314 n) (@lem2654315 n)). Qed.
Lemma lem2654318 (n : int) : (term130 n) = (term135 n).
Proof. exact (TRANS (@lem2654269 n) (@lem2654316 n)). Qed.
Lemma lem2654319 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654320 (n : int) : (term137 n) = (term138 n).
Proof. exact (MK_COMB (@lem2654319) (@lem2654318 n)). Qed.
Lemma lem2654321 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654322 (n : int) : (term129 n) = (term139 n).
Proof. exact (MK_COMB (@lem2654320 n) (@lem2654321)). Qed.
Lemma lem2654323 (n : int) : (term66 n) = (term139 n).
Proof. exact (TRANS (@lem2654257 n) (@lem2654322 n)). Qed.
Lemma lem2654324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2654325 (m : int) : (term68 m) = (term151 m).
Proof. exact (MK_COMB (@lem2654324) (@lem2654256 m)). Qed.
Lemma lem2654326 (m : int) (n : int) : (term332 m n) = (term343 m n).
Proof. exact (MK_COMB (@lem2654325 m) (@lem2654323 n)). Qed.
Lemma lem2654327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2654328 (m : int) (n : int) : (term333 n m) = (term344 m n).
Proof. exact (MK_COMB (@lem2654327) (@lem2654189 m n)). Qed.
Lemma lem2654329 (m : int) (n : int) : (term334 m n) = (term345 m n).
Proof. exact (MK_COMB (@lem2654328 m n) (@lem2654326 m n)). Qed.
Lemma lem2654330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2654331 (n : int) : (term70 n) = (term153 n).
Proof. exact (MK_COMB (@lem2654330) (@lem2654170 n)). Qed.
Lemma lem2654332 (m : int) (n : int) : (term335 m n) = (term346 m n).
Proof. exact (MK_COMB (@lem2654331 n) (@lem2654329 m n)). Qed.
Lemma lem2654339 (m : int) (n : int) : (term336 m n) = (term346 m n).
Proof. exact (TRANS (@lem2654109 m n) (@lem2654332 m n)). Qed.
Lemma lem2654356 (m : int) (n : int) : (term345 m n) = (term347 m n).
Proof. exact (@lem19158 (term139 m) (term342 m n) (term139 n)). Qed.
Lemma lem2654359 (n : int) : (term153 n) = (term153 n).
Proof. exact (eq_refl (term153 n)). Qed.
Lemma lem2654360 (m : int) (n : int) : (term346 m n) = (term348 m n).
Proof. exact (MK_COMB (@lem2654359 n) (@lem2654356 m n)). Qed.
Lemma lem2654367 (m : int) (n : int) : (term348 m n) = (term349 m n).
Proof. exact (@lem19158 (term350 n m) (term128 n) (term351 m n)). Qed.
Lemma lem2654368 (m : int) (n : int) : (term346 m n) = (term349 m n).
Proof. exact (TRANS (@lem2654360 m n) (@lem2654367 m n)). Qed.
Lemma lem2654369 (m : int) (n : int) : (term336 m n) = (term349 m n).
Proof. exact (TRANS (@lem2654339 m n) (@lem2654368 m n)). Qed.
Lemma lem2654379 (m : int) (n : int) (h1 : term349 m n) : term349 m n.
Proof. exact (h1). Qed.
Lemma lem2654380 (n : int) (m : int) (h1 : term352 n m) : term352 n m.
Proof. exact (h1). Qed.
Lemma lem2654381 (n : int) (m : int) (h1 : term352 n m) : term350 n m.
Proof. exact (proj2 (@lem2654380 n m h1)). Qed.
Lemma lem2654382 (n : int) (m : int) (h1 : term352 n m) : term128 n.
Proof. exact (proj1 (@lem2654380 n m h1)). Qed.
Lemma lem2654383 (n : int) (m : int) (h1 : term352 n m) : term139 m.
Proof. exact (proj2 (@lem2654381 n m h1)). Qed.
Lemma lem2654384 (n : int) (m : int) (h1 : term352 n m) : term342 m n.
Proof. exact (proj1 (@lem2654381 n m h1)). Qed.
Lemma lem2654386 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2654387 : term182 = term183.
Proof. exact (@lem2654386 term45 term49). Qed.
Lemma lem2654389 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654390 : term49 = term103.
Proof. exact (@lem2654389 term50). Qed.
Lemma lem2654392 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654393 : term45 = term142.
Proof. exact (@lem2654392 (NUMERAL 0)). Qed.
Lemma lem2654394 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2654395 : term184 = term185.
Proof. exact (MK_COMB (@lem2654394) (@lem2654393)). Qed.
Lemma lem2654396 : term183 = term186.
Proof. exact (MK_COMB (@lem2654395) (@lem2654390)). Qed.
Lemma lem2654397 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2654399 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654400 : term183 = term189.
Proof. exact (@lem2654399 (NUMERAL 0) term50). Qed.
Lemma lem2654401 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654402 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654403 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654402 h1) (fun h1 : term189 = True => @lem2654401)). Qed.
Lemma lem2654404 : term189 = True.
Proof. exact (EQ_MP (@lem2654403) (@lem2654401)). Qed.
Lemma lem2654405 : term183 = True.
Proof. exact (TRANS (@lem2654400) (@lem2654404)). Qed.
Lemma lem2654406 : True = term183.
Proof. exact (SYM (@lem2654405)). Qed.
Lemma lem2654407 : term183.
Proof. exact (EQ_MP (@lem2654406) (@lem0)). Qed.
Lemma lem2654408 : term191.
Proof. exact (@lem2654397 (@lem2654407)). Qed.
Lemma lem2654410 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654411 : term183 = term189.
Proof. exact (@lem2654410 (NUMERAL 0) term50). Qed.
Lemma lem2654412 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654413 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654414 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654413 h1) (fun h1 : term189 = True => @lem2654412)). Qed.
Lemma lem2654415 : term189 = True.
Proof. exact (EQ_MP (@lem2654414) (@lem2654412)). Qed.
Lemma lem2654416 : term183 = True.
Proof. exact (TRANS (@lem2654411) (@lem2654415)). Qed.
Lemma lem2654417 : True = term183.
Proof. exact (SYM (@lem2654416)). Qed.
Lemma lem2654418 : term183.
Proof. exact (EQ_MP (@lem2654417) (@lem0)). Qed.
Lemma lem2654419 : term186 = term192.
Proof. exact (@lem2654408 (@lem2654418)). Qed.
Lemma lem2654421 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654422 : term115 = term116.
Proof. exact (@lem2654421 term50 term50). Qed.
Lemma lem2654423 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654424 : term118 = term50.
Proof. exact (EQ_MP (@lem2654423) (@lem940073)). Qed.
Lemma lem2654425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654426 : term116 = term49.
Proof. exact (MK_COMB (@lem2654425) (@lem2654424)). Qed.
Lemma lem2654427 : term115 = term49.
Proof. exact (TRANS (@lem2654422) (@lem2654426)). Qed.
Lemma lem2654429 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2654430 : term194 = term45.
Proof. exact (@lem2654429 term50). Qed.
Lemma lem2654431 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2654432 : term195 = term184.
Proof. exact (MK_COMB (@lem2654431) (@lem2654430)). Qed.
Lemma lem2654433 : term192 = term183.
Proof. exact (MK_COMB (@lem2654432) (@lem2654427)). Qed.
Lemma lem2654435 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654436 : term183 = term189.
Proof. exact (@lem2654435 (NUMERAL 0) term50). Qed.
Lemma lem2654437 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654438 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654439 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654438 h1) (fun h1 : term189 = True => @lem2654437)). Qed.
Lemma lem2654440 : term189 = True.
Proof. exact (EQ_MP (@lem2654439) (@lem2654437)). Qed.
Lemma lem2654441 : term183 = True.
Proof. exact (TRANS (@lem2654436) (@lem2654440)). Qed.
Lemma lem2654442 : term192 = True.
Proof. exact (TRANS (@lem2654433) (@lem2654441)). Qed.
Lemma lem2654443 : term186 = True.
Proof. exact (TRANS (@lem2654419) (@lem2654442)). Qed.
Lemma lem2654444 : term183 = True.
Proof. exact (TRANS (@lem2654396) (@lem2654443)). Qed.
Lemma lem2654445 : term182 = True.
Proof. exact (TRANS (@lem2654387) (@lem2654444)). Qed.
Lemma lem2654446 : True = term182.
Proof. exact (SYM (@lem2654445)). Qed.
Lemma lem2654447 : term182.
Proof. exact (EQ_MP (@lem2654446) (@lem0)). Qed.
Lemma lem2654448 (n : int) (m : int) (h1 : term352 n m) : term196 n.
Proof. exact (conj (@lem2654447) (@lem2654382 n m h1)). Qed.
Lemma lem2654450 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2654451 (n : int) : term198 n.
Proof. exact (@lem2654450 term49 (term125 n)). Qed.
Lemma lem2654452 (n : int) (m : int) (h1 : term352 n m) : term199 n.
Proof. exact (@lem2654451 n (@lem2654448 n m h1)). Qed.
Lemma lem2654453 (n : int) : (term200 n) = (term125 n).
Proof. exact (@lem1982733 (term125 n)). Qed.
Lemma lem2654454 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654455 (n : int) : (term201 n) = (term127 n).
Proof. exact (MK_COMB (@lem2654454) (@lem2654453 n)). Qed.
Lemma lem2654456 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654457 (n : int) : (term199 n) = (term128 n).
Proof. exact (MK_COMB (@lem2654455 n) (@lem2654456)). Qed.
Lemma lem2654458 (n : int) (m : int) (h1 : term352 n m) : term128 n.
Proof. exact (EQ_MP (@lem2654457 n) (@lem2654452 n m h1)). Qed.
Lemma lem2654460 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2654461 : term182 = term183.
Proof. exact (@lem2654460 term45 term49). Qed.
Lemma lem2654463 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654464 : term49 = term103.
Proof. exact (@lem2654463 term50). Qed.
Lemma lem2654466 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654467 : term45 = term142.
Proof. exact (@lem2654466 (NUMERAL 0)). Qed.
Lemma lem2654468 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2654469 : term184 = term185.
Proof. exact (MK_COMB (@lem2654468) (@lem2654467)). Qed.
Lemma lem2654470 : term183 = term186.
Proof. exact (MK_COMB (@lem2654469) (@lem2654464)). Qed.
Lemma lem2654471 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2654473 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654474 : term183 = term189.
Proof. exact (@lem2654473 (NUMERAL 0) term50). Qed.
Lemma lem2654475 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654476 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654477 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654476 h1) (fun h1 : term189 = True => @lem2654475)). Qed.
Lemma lem2654478 : term189 = True.
Proof. exact (EQ_MP (@lem2654477) (@lem2654475)). Qed.
Lemma lem2654479 : term183 = True.
Proof. exact (TRANS (@lem2654474) (@lem2654478)). Qed.
Lemma lem2654480 : True = term183.
Proof. exact (SYM (@lem2654479)). Qed.
Lemma lem2654481 : term183.
Proof. exact (EQ_MP (@lem2654480) (@lem0)). Qed.
Lemma lem2654482 : term191.
Proof. exact (@lem2654471 (@lem2654481)). Qed.
Lemma lem2654484 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654485 : term183 = term189.
Proof. exact (@lem2654484 (NUMERAL 0) term50). Qed.
Lemma lem2654486 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654487 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654488 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654487 h1) (fun h1 : term189 = True => @lem2654486)). Qed.
Lemma lem2654489 : term189 = True.
Proof. exact (EQ_MP (@lem2654488) (@lem2654486)). Qed.
Lemma lem2654490 : term183 = True.
Proof. exact (TRANS (@lem2654485) (@lem2654489)). Qed.
Lemma lem2654491 : True = term183.
Proof. exact (SYM (@lem2654490)). Qed.
Lemma lem2654492 : term183.
Proof. exact (EQ_MP (@lem2654491) (@lem0)). Qed.
Lemma lem2654493 : term186 = term192.
Proof. exact (@lem2654482 (@lem2654492)). Qed.
Lemma lem2654495 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654496 : term115 = term116.
Proof. exact (@lem2654495 term50 term50). Qed.
Lemma lem2654497 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654498 : term118 = term50.
Proof. exact (EQ_MP (@lem2654497) (@lem940073)). Qed.
Lemma lem2654499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654500 : term116 = term49.
Proof. exact (MK_COMB (@lem2654499) (@lem2654498)). Qed.
Lemma lem2654501 : term115 = term49.
Proof. exact (TRANS (@lem2654496) (@lem2654500)). Qed.
Lemma lem2654503 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2654504 : term194 = term45.
Proof. exact (@lem2654503 term50). Qed.
Lemma lem2654505 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2654506 : term195 = term184.
Proof. exact (MK_COMB (@lem2654505) (@lem2654504)). Qed.
Lemma lem2654507 : term192 = term183.
Proof. exact (MK_COMB (@lem2654506) (@lem2654501)). Qed.
Lemma lem2654509 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654510 : term183 = term189.
Proof. exact (@lem2654509 (NUMERAL 0) term50). Qed.
Lemma lem2654511 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654512 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654513 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654512 h1) (fun h1 : term189 = True => @lem2654511)). Qed.
Lemma lem2654514 : term189 = True.
Proof. exact (EQ_MP (@lem2654513) (@lem2654511)). Qed.
Lemma lem2654515 : term183 = True.
Proof. exact (TRANS (@lem2654510) (@lem2654514)). Qed.
Lemma lem2654516 : term192 = True.
Proof. exact (TRANS (@lem2654507) (@lem2654515)). Qed.
Lemma lem2654517 : term186 = True.
Proof. exact (TRANS (@lem2654493) (@lem2654516)). Qed.
Lemma lem2654518 : term183 = True.
Proof. exact (TRANS (@lem2654470) (@lem2654517)). Qed.
Lemma lem2654519 : term182 = True.
Proof. exact (TRANS (@lem2654461) (@lem2654518)). Qed.
Lemma lem2654520 : True = term182.
Proof. exact (SYM (@lem2654519)). Qed.
Lemma lem2654521 : term182.
Proof. exact (EQ_MP (@lem2654520) (@lem0)). Qed.
Lemma lem2654522 (n : int) (m : int) (h1 : term352 n m) : term353 m n.
Proof. exact (conj (@lem2654521) (@lem2654384 n m h1)). Qed.
Lemma lem2654524 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2654525 (m : int) (n : int) : term354 m n.
Proof. exact (@lem2654524 term49 (term339 m n)). Qed.
Lemma lem2654526 (n : int) (m : int) (h1 : term352 n m) : term355 m n.
Proof. exact (@lem2654525 m n (@lem2654522 n m h1)). Qed.
Lemma lem2654527 (m : int) (n : int) : (term356 m n) = (term339 m n).
Proof. exact (@lem1982733 (term339 m n)). Qed.
Lemma lem2654528 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654529 (m : int) (n : int) : (term357 m n) = (term341 m n).
Proof. exact (MK_COMB (@lem2654528) (@lem2654527 m n)). Qed.
Lemma lem2654530 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654531 (m : int) (n : int) : (term355 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem2654529 m n) (@lem2654530)). Qed.
Lemma lem2654532 (n : int) (m : int) (h1 : term352 n m) : term342 m n.
Proof. exact (EQ_MP (@lem2654531 m n) (@lem2654526 n m h1)). Qed.
Lemma lem2654533 (n : int) (m : int) (h1 : term352 n m) : term358 m n.
Proof. exact (conj (@lem2654532 n m h1) (@lem2654458 n m h1)). Qed.
Lemma lem2654535 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2654536 (m : int) (n : int) : term359 m n.
Proof. exact (@lem2654535 (term339 m n) (term125 n)). Qed.
Lemma lem2654537 (n : int) (m : int) (h1 : term352 n m) : term360 m n.
Proof. exact (@lem2654536 m n (@lem2654533 n m h1)). Qed.
Lemma lem2654538 (m : int) (n : int) : (term361 m n) = (term362 m n).
Proof. exact (@lem1982755 (real_of_int m) (term158 n) (term125 n)). Qed.
Lemma lem2654539 (n : int) : (term283 n) = (term284 n).
Proof. exact (@lem1982763 (term158 n) (real_of_int n) term106). Qed.
Lemma lem2654540 (n : int) : (term213 n) = (term214 n).
Proof. exact (@lem1982713 term106 (real_of_int n)). Qed.
Lemma lem2654542 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654543 : term49 = term103.
Proof. exact (@lem2654542 term50). Qed.
Lemma lem2654545 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2654546 : term106 = term107.
Proof. exact (@lem2654545 term50). Qed.
Lemma lem2654547 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2654548 : term215 = term216.
Proof. exact (MK_COMB (@lem2654547) (@lem2654546)). Qed.
Lemma lem2654549 : term217 = term218.
Proof. exact (MK_COMB (@lem2654548) (@lem2654543)). Qed.
Lemma lem2654550 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2654552 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654553 : term183 = term189.
Proof. exact (@lem2654552 (NUMERAL 0) term50). Qed.
Lemma lem2654554 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654555 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654556 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654555 h1) (fun h1 : term189 = True => @lem2654554)). Qed.
Lemma lem2654557 : term189 = True.
Proof. exact (EQ_MP (@lem2654556) (@lem2654554)). Qed.
Lemma lem2654558 : term183 = True.
Proof. exact (TRANS (@lem2654553) (@lem2654557)). Qed.
Lemma lem2654559 : True = term183.
Proof. exact (SYM (@lem2654558)). Qed.
Lemma lem2654560 : term183.
Proof. exact (EQ_MP (@lem2654559) (@lem0)). Qed.
Lemma lem2654561 : term220.
Proof. exact (@lem2654550 (@lem2654560)). Qed.
Lemma lem2654563 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654564 : term183 = term189.
Proof. exact (@lem2654563 (NUMERAL 0) term50). Qed.
Lemma lem2654565 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654566 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654567 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654566 h1) (fun h1 : term189 = True => @lem2654565)). Qed.
Lemma lem2654568 : term189 = True.
Proof. exact (EQ_MP (@lem2654567) (@lem2654565)). Qed.
Lemma lem2654569 : term183 = True.
Proof. exact (TRANS (@lem2654564) (@lem2654568)). Qed.
Lemma lem2654570 : True = term183.
Proof. exact (SYM (@lem2654569)). Qed.
Lemma lem2654571 : term183.
Proof. exact (EQ_MP (@lem2654570) (@lem0)). Qed.
Lemma lem2654572 : term221.
Proof. exact (@lem2654561 (@lem2654571)). Qed.
Lemma lem2654574 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654575 : term183 = term189.
Proof. exact (@lem2654574 (NUMERAL 0) term50). Qed.
Lemma lem2654576 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654577 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654578 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654577 h1) (fun h1 : term189 = True => @lem2654576)). Qed.
Lemma lem2654579 : term189 = True.
Proof. exact (EQ_MP (@lem2654578) (@lem2654576)). Qed.
Lemma lem2654580 : term183 = True.
Proof. exact (TRANS (@lem2654575) (@lem2654579)). Qed.
Lemma lem2654581 : True = term183.
Proof. exact (SYM (@lem2654580)). Qed.
Lemma lem2654582 : term183.
Proof. exact (EQ_MP (@lem2654581) (@lem0)). Qed.
Lemma lem2654583 : term222.
Proof. exact (@lem2654572 (@lem2654582)). Qed.
Lemma lem2654585 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654586 : term115 = term116.
Proof. exact (@lem2654585 term50 term50). Qed.
Lemma lem2654587 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654588 : term118 = term50.
Proof. exact (EQ_MP (@lem2654587) (@lem940073)). Qed.
Lemma lem2654589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654590 : term116 = term49.
Proof. exact (MK_COMB (@lem2654589) (@lem2654588)). Qed.
Lemma lem2654591 : term115 = term49.
Proof. exact (TRANS (@lem2654586) (@lem2654590)). Qed.
Lemma lem2654593 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2654594 : term110 = term121.
Proof. exact (@lem2654593 term50 term50). Qed.
Lemma lem2654595 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654596 : term118 = term50.
Proof. exact (EQ_MP (@lem2654595) (@lem940073)). Qed.
Lemma lem2654597 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654598 : term116 = term49.
Proof. exact (MK_COMB (@lem2654597) (@lem2654596)). Qed.
Lemma lem2654599 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2654600 : term121 = term106.
Proof. exact (MK_COMB (@lem2654599) (@lem2654598)). Qed.
Lemma lem2654601 : term110 = term106.
Proof. exact (TRANS (@lem2654594) (@lem2654600)). Qed.
Lemma lem2654602 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2654603 : term223 = term215.
Proof. exact (MK_COMB (@lem2654602) (@lem2654601)). Qed.
Lemma lem2654604 : term224 = term217.
Proof. exact (MK_COMB (@lem2654603) (@lem2654591)). Qed.
Lemma lem2654606 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2654607 : term217 = term45.
Proof. exact (@lem2654606 term50). Qed.
Lemma lem2654608 : term224 = term45.
Proof. exact (TRANS (@lem2654604) (@lem2654607)). Qed.
Lemma lem2654609 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2654610 : term226 = term227.
Proof. exact (MK_COMB (@lem2654609) (@lem2654608)). Qed.
Lemma lem2654611 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2654612 : term228 = term194.
Proof. exact (MK_COMB (@lem2654610) (@lem2654611)). Qed.
Lemma lem2654614 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2654615 : term194 = term45.
Proof. exact (@lem2654614 term50). Qed.
Lemma lem2654616 : term228 = term45.
Proof. exact (TRANS (@lem2654612) (@lem2654615)). Qed.
Lemma lem2654618 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654619 : term115 = term116.
Proof. exact (@lem2654618 term50 term50). Qed.
Lemma lem2654620 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654621 : term118 = term50.
Proof. exact (EQ_MP (@lem2654620) (@lem940073)). Qed.
Lemma lem2654622 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654623 : term116 = term49.
Proof. exact (MK_COMB (@lem2654622) (@lem2654621)). Qed.
Lemma lem2654624 : term115 = term49.
Proof. exact (TRANS (@lem2654619) (@lem2654623)). Qed.
Lemma lem2654625 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2654626 : term229 = term194.
Proof. exact (MK_COMB (@lem2654625) (@lem2654624)). Qed.
Lemma lem2654628 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2654629 : term194 = term45.
Proof. exact (@lem2654628 term50). Qed.
Lemma lem2654630 : term229 = term45.
Proof. exact (TRANS (@lem2654626) (@lem2654629)). Qed.
Lemma lem2654631 : term45 = term229.
Proof. exact (SYM (@lem2654630)). Qed.
Lemma lem2654632 : term228 = term229.
Proof. exact (TRANS (@lem2654616) (@lem2654631)). Qed.
Lemma lem2654633 : term218 = term142.
Proof. exact (@lem2654583 (@lem2654632)). Qed.
Lemma lem2654634 : term217 = term142.
Proof. exact (TRANS (@lem2654549) (@lem2654633)). Qed.
Lemma lem2654636 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2654637 : term142 = term45.
Proof. exact (@lem2654636 term45). Qed.
Lemma lem2654638 : term217 = term45.
Proof. exact (TRANS (@lem2654634) (@lem2654637)). Qed.
Lemma lem2654639 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2654640 : term230 = term227.
Proof. exact (MK_COMB (@lem2654639) (@lem2654638)). Qed.
Lemma lem2654641 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2654642 (n : int) : (term214 n) = (term231 n).
Proof. exact (MK_COMB (@lem2654640) (@lem2654641 n)). Qed.
Lemma lem2654643 (n : int) : (term213 n) = (term231 n).
Proof. exact (TRANS (@lem2654540 n) (@lem2654642 n)). Qed.
Lemma lem2654644 (n : int) : (term231 n) = term45.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2654645 (n : int) : (term213 n) = term45.
Proof. exact (TRANS (@lem2654643 n) (@lem2654644 n)). Qed.
Lemma lem2654646 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2654647 (n : int) : (term232 n) = term47.
Proof. exact (MK_COMB (@lem2654646) (@lem2654645 n)). Qed.
Lemma lem2654648 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2654649 (n : int) : (term284 n) = term285.
Proof. exact (MK_COMB (@lem2654647 n) (@lem2654648)). Qed.
Lemma lem2654650 (n : int) : (term283 n) = term285.
Proof. exact (TRANS (@lem2654539 n) (@lem2654649 n)). Qed.
Lemma lem2654651 : term285 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2654652 (n : int) : (term283 n) = term106.
Proof. exact (TRANS (@lem2654650 n) (@lem2654651)). Qed.
Lemma lem2654653 (m : int) : (term62 m) = (term62 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem2654654 (n : int) (m : int) : (term362 m n) = (term125 m).
Proof. exact (MK_COMB (@lem2654653 m) (@lem2654652 n)). Qed.
Lemma lem2654655 (n : int) (m : int) : (term361 m n) = (term125 m).
Proof. exact (TRANS (@lem2654538 m n) (@lem2654654 n m)). Qed.
Lemma lem2654656 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654657 (n : int) (m : int) : (term363 m n) = (term127 m).
Proof. exact (MK_COMB (@lem2654656) (@lem2654655 n m)). Qed.
Lemma lem2654658 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654659 (n : int) (m : int) : (term360 m n) = (term128 m).
Proof. exact (MK_COMB (@lem2654657 n m) (@lem2654658)). Qed.
Lemma lem2654660 (n : int) (m : int) (h1 : term352 n m) : term128 m.
Proof. exact (EQ_MP (@lem2654659 n m) (@lem2654537 n m h1)). Qed.
Lemma lem2654662 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2654663 : term182 = term183.
Proof. exact (@lem2654662 term45 term49). Qed.
Lemma lem2654665 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654666 : term49 = term103.
Proof. exact (@lem2654665 term50). Qed.
Lemma lem2654668 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654669 : term45 = term142.
Proof. exact (@lem2654668 (NUMERAL 0)). Qed.
Lemma lem2654670 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2654671 : term184 = term185.
Proof. exact (MK_COMB (@lem2654670) (@lem2654669)). Qed.
Lemma lem2654672 : term183 = term186.
Proof. exact (MK_COMB (@lem2654671) (@lem2654666)). Qed.
Lemma lem2654673 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2654675 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654676 : term183 = term189.
Proof. exact (@lem2654675 (NUMERAL 0) term50). Qed.
Lemma lem2654677 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654678 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654679 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654678 h1) (fun h1 : term189 = True => @lem2654677)). Qed.
Lemma lem2654680 : term189 = True.
Proof. exact (EQ_MP (@lem2654679) (@lem2654677)). Qed.
Lemma lem2654681 : term183 = True.
Proof. exact (TRANS (@lem2654676) (@lem2654680)). Qed.
Lemma lem2654682 : True = term183.
Proof. exact (SYM (@lem2654681)). Qed.
Lemma lem2654683 : term183.
Proof. exact (EQ_MP (@lem2654682) (@lem0)). Qed.
Lemma lem2654684 : term191.
Proof. exact (@lem2654673 (@lem2654683)). Qed.
Lemma lem2654686 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654687 : term183 = term189.
Proof. exact (@lem2654686 (NUMERAL 0) term50). Qed.
Lemma lem2654688 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654689 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654690 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654689 h1) (fun h1 : term189 = True => @lem2654688)). Qed.
Lemma lem2654691 : term189 = True.
Proof. exact (EQ_MP (@lem2654690) (@lem2654688)). Qed.
Lemma lem2654692 : term183 = True.
Proof. exact (TRANS (@lem2654687) (@lem2654691)). Qed.
Lemma lem2654693 : True = term183.
Proof. exact (SYM (@lem2654692)). Qed.
Lemma lem2654694 : term183.
Proof. exact (EQ_MP (@lem2654693) (@lem0)). Qed.
Lemma lem2654695 : term186 = term192.
Proof. exact (@lem2654684 (@lem2654694)). Qed.
Lemma lem2654697 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654698 : term115 = term116.
Proof. exact (@lem2654697 term50 term50). Qed.
Lemma lem2654699 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654700 : term118 = term50.
Proof. exact (EQ_MP (@lem2654699) (@lem940073)). Qed.
Lemma lem2654701 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654702 : term116 = term49.
Proof. exact (MK_COMB (@lem2654701) (@lem2654700)). Qed.
Lemma lem2654703 : term115 = term49.
Proof. exact (TRANS (@lem2654698) (@lem2654702)). Qed.
Lemma lem2654705 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2654706 : term194 = term45.
Proof. exact (@lem2654705 term50). Qed.
Lemma lem2654707 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2654708 : term195 = term184.
Proof. exact (MK_COMB (@lem2654707) (@lem2654706)). Qed.
Lemma lem2654709 : term192 = term183.
Proof. exact (MK_COMB (@lem2654708) (@lem2654703)). Qed.
Lemma lem2654711 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654712 : term183 = term189.
Proof. exact (@lem2654711 (NUMERAL 0) term50). Qed.
Lemma lem2654713 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654714 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654715 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654714 h1) (fun h1 : term189 = True => @lem2654713)). Qed.
Lemma lem2654716 : term189 = True.
Proof. exact (EQ_MP (@lem2654715) (@lem2654713)). Qed.
Lemma lem2654717 : term183 = True.
Proof. exact (TRANS (@lem2654712) (@lem2654716)). Qed.
Lemma lem2654718 : term192 = True.
Proof. exact (TRANS (@lem2654709) (@lem2654717)). Qed.
Lemma lem2654719 : term186 = True.
Proof. exact (TRANS (@lem2654695) (@lem2654718)). Qed.
Lemma lem2654720 : term183 = True.
Proof. exact (TRANS (@lem2654672) (@lem2654719)). Qed.
Lemma lem2654721 : term182 = True.
Proof. exact (TRANS (@lem2654663) (@lem2654720)). Qed.
Lemma lem2654722 : True = term182.
Proof. exact (SYM (@lem2654721)). Qed.
Lemma lem2654723 : term182.
Proof. exact (EQ_MP (@lem2654722) (@lem0)). Qed.
Lemma lem2654724 (n : int) (m : int) (h1 : term352 n m) : term196 m.
Proof. exact (conj (@lem2654723) (@lem2654660 n m h1)). Qed.
Lemma lem2654726 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2654727 (m : int) : term198 m.
Proof. exact (@lem2654726 term49 (term125 m)). Qed.
Lemma lem2654728 (n : int) (m : int) (h1 : term352 n m) : term199 m.
Proof. exact (@lem2654727 m (@lem2654724 n m h1)). Qed.
Lemma lem2654729 (m : int) : (term200 m) = (term125 m).
Proof. exact (@lem1982733 (term125 m)). Qed.
Lemma lem2654730 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654731 (m : int) : (term201 m) = (term127 m).
Proof. exact (MK_COMB (@lem2654730) (@lem2654729 m)). Qed.
Lemma lem2654732 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654733 (m : int) : (term199 m) = (term128 m).
Proof. exact (MK_COMB (@lem2654731 m) (@lem2654732)). Qed.
Lemma lem2654734 (n : int) (m : int) (h1 : term352 n m) : term128 m.
Proof. exact (EQ_MP (@lem2654733 m) (@lem2654728 n m h1)). Qed.
Lemma lem2654736 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2654737 : term182 = term183.
Proof. exact (@lem2654736 term45 term49). Qed.
Lemma lem2654739 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654740 : term49 = term103.
Proof. exact (@lem2654739 term50). Qed.
Lemma lem2654742 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654743 : term45 = term142.
Proof. exact (@lem2654742 (NUMERAL 0)). Qed.
Lemma lem2654744 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2654745 : term184 = term185.
Proof. exact (MK_COMB (@lem2654744) (@lem2654743)). Qed.
Lemma lem2654746 : term183 = term186.
Proof. exact (MK_COMB (@lem2654745) (@lem2654740)). Qed.
Lemma lem2654747 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2654749 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654750 : term183 = term189.
Proof. exact (@lem2654749 (NUMERAL 0) term50). Qed.
Lemma lem2654751 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654752 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654753 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654752 h1) (fun h1 : term189 = True => @lem2654751)). Qed.
Lemma lem2654754 : term189 = True.
Proof. exact (EQ_MP (@lem2654753) (@lem2654751)). Qed.
Lemma lem2654755 : term183 = True.
Proof. exact (TRANS (@lem2654750) (@lem2654754)). Qed.
Lemma lem2654756 : True = term183.
Proof. exact (SYM (@lem2654755)). Qed.
Lemma lem2654757 : term183.
Proof. exact (EQ_MP (@lem2654756) (@lem0)). Qed.
Lemma lem2654758 : term191.
Proof. exact (@lem2654747 (@lem2654757)). Qed.
Lemma lem2654760 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654761 : term183 = term189.
Proof. exact (@lem2654760 (NUMERAL 0) term50). Qed.
Lemma lem2654762 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654763 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654764 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654763 h1) (fun h1 : term189 = True => @lem2654762)). Qed.
Lemma lem2654765 : term189 = True.
Proof. exact (EQ_MP (@lem2654764) (@lem2654762)). Qed.
Lemma lem2654766 : term183 = True.
Proof. exact (TRANS (@lem2654761) (@lem2654765)). Qed.
Lemma lem2654767 : True = term183.
Proof. exact (SYM (@lem2654766)). Qed.
Lemma lem2654768 : term183.
Proof. exact (EQ_MP (@lem2654767) (@lem0)). Qed.
Lemma lem2654769 : term186 = term192.
Proof. exact (@lem2654758 (@lem2654768)). Qed.
Lemma lem2654771 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654772 : term115 = term116.
Proof. exact (@lem2654771 term50 term50). Qed.
Lemma lem2654773 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654774 : term118 = term50.
Proof. exact (EQ_MP (@lem2654773) (@lem940073)). Qed.
Lemma lem2654775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654776 : term116 = term49.
Proof. exact (MK_COMB (@lem2654775) (@lem2654774)). Qed.
Lemma lem2654777 : term115 = term49.
Proof. exact (TRANS (@lem2654772) (@lem2654776)). Qed.
Lemma lem2654779 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2654780 : term194 = term45.
Proof. exact (@lem2654779 term50). Qed.
Lemma lem2654781 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2654782 : term195 = term184.
Proof. exact (MK_COMB (@lem2654781) (@lem2654780)). Qed.
Lemma lem2654783 : term192 = term183.
Proof. exact (MK_COMB (@lem2654782) (@lem2654777)). Qed.
Lemma lem2654785 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654786 : term183 = term189.
Proof. exact (@lem2654785 (NUMERAL 0) term50). Qed.
Lemma lem2654787 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654788 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654789 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654788 h1) (fun h1 : term189 = True => @lem2654787)). Qed.
Lemma lem2654790 : term189 = True.
Proof. exact (EQ_MP (@lem2654789) (@lem2654787)). Qed.
Lemma lem2654791 : term183 = True.
Proof. exact (TRANS (@lem2654786) (@lem2654790)). Qed.
Lemma lem2654792 : term192 = True.
Proof. exact (TRANS (@lem2654783) (@lem2654791)). Qed.
Lemma lem2654793 : term186 = True.
Proof. exact (TRANS (@lem2654769) (@lem2654792)). Qed.
Lemma lem2654794 : term183 = True.
Proof. exact (TRANS (@lem2654746) (@lem2654793)). Qed.
Lemma lem2654795 : term182 = True.
Proof. exact (TRANS (@lem2654737) (@lem2654794)). Qed.
Lemma lem2654796 : True = term182.
Proof. exact (SYM (@lem2654795)). Qed.
Lemma lem2654797 : term182.
Proof. exact (EQ_MP (@lem2654796) (@lem0)). Qed.
Lemma lem2654798 (n : int) (m : int) (h1 : term352 n m) : term202 m.
Proof. exact (conj (@lem2654797) (@lem2654383 n m h1)). Qed.
Lemma lem2654800 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2654801 (m : int) : term203 m.
Proof. exact (@lem2654800 term49 (term135 m)). Qed.
Lemma lem2654802 (n : int) (m : int) (h1 : term352 n m) : term204 m.
Proof. exact (@lem2654801 m (@lem2654798 n m h1)). Qed.
Lemma lem2654803 (m : int) : (term205 m) = (term135 m).
Proof. exact (@lem1982733 (term135 m)). Qed.
Lemma lem2654804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2654805 (m : int) : (term206 m) = (term138 m).
Proof. exact (MK_COMB (@lem2654804) (@lem2654803 m)). Qed.
Lemma lem2654806 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2654807 (m : int) : (term204 m) = (term139 m).
Proof. exact (MK_COMB (@lem2654805 m) (@lem2654806)). Qed.
Lemma lem2654808 (n : int) (m : int) (h1 : term352 n m) : term139 m.
Proof. exact (EQ_MP (@lem2654807 m) (@lem2654802 n m h1)). Qed.
Lemma lem2654809 (n : int) (m : int) (h1 : term352 n m) : term207 m.
Proof. exact (conj (@lem2654808 n m h1) (@lem2654734 n m h1)). Qed.
Lemma lem2654811 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2654812 (m : int) : term209 m.
Proof. exact (@lem2654811 (term135 m) (term125 m)). Qed.
Lemma lem2654813 (n : int) (m : int) (h1 : term352 n m) : term210 m.
Proof. exact (@lem2654812 m (@lem2654809 n m h1)). Qed.
Lemma lem2654814 (m : int) : (term211 m) = (term212 m).
Proof. exact (@lem1982753 (term158 m) (real_of_int m) term106 term106). Qed.
Lemma lem2654815 (m : int) : (term213 m) = (term214 m).
Proof. exact (@lem1982713 term106 (real_of_int m)). Qed.
Lemma lem2654817 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2654818 : term49 = term103.
Proof. exact (@lem2654817 term50). Qed.
Lemma lem2654820 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2654821 : term106 = term107.
Proof. exact (@lem2654820 term50). Qed.
Lemma lem2654822 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2654823 : term215 = term216.
Proof. exact (MK_COMB (@lem2654822) (@lem2654821)). Qed.
Lemma lem2654824 : term217 = term218.
Proof. exact (MK_COMB (@lem2654823) (@lem2654818)). Qed.
Lemma lem2654825 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2654827 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654828 : term183 = term189.
Proof. exact (@lem2654827 (NUMERAL 0) term50). Qed.
Lemma lem2654829 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654830 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654831 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654830 h1) (fun h1 : term189 = True => @lem2654829)). Qed.
Lemma lem2654832 : term189 = True.
Proof. exact (EQ_MP (@lem2654831) (@lem2654829)). Qed.
Lemma lem2654833 : term183 = True.
Proof. exact (TRANS (@lem2654828) (@lem2654832)). Qed.
Lemma lem2654834 : True = term183.
Proof. exact (SYM (@lem2654833)). Qed.
Lemma lem2654835 : term183.
Proof. exact (EQ_MP (@lem2654834) (@lem0)). Qed.
Lemma lem2654836 : term220.
Proof. exact (@lem2654825 (@lem2654835)). Qed.
Lemma lem2654838 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654839 : term183 = term189.
Proof. exact (@lem2654838 (NUMERAL 0) term50). Qed.
Lemma lem2654840 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654841 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654842 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654841 h1) (fun h1 : term189 = True => @lem2654840)). Qed.
Lemma lem2654843 : term189 = True.
Proof. exact (EQ_MP (@lem2654842) (@lem2654840)). Qed.
Lemma lem2654844 : term183 = True.
Proof. exact (TRANS (@lem2654839) (@lem2654843)). Qed.
Lemma lem2654845 : True = term183.
Proof. exact (SYM (@lem2654844)). Qed.
Lemma lem2654846 : term183.
Proof. exact (EQ_MP (@lem2654845) (@lem0)). Qed.
Lemma lem2654847 : term221.
Proof. exact (@lem2654836 (@lem2654846)). Qed.
Lemma lem2654849 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654850 : term183 = term189.
Proof. exact (@lem2654849 (NUMERAL 0) term50). Qed.
Lemma lem2654851 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654852 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654853 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654852 h1) (fun h1 : term189 = True => @lem2654851)). Qed.
Lemma lem2654854 : term189 = True.
Proof. exact (EQ_MP (@lem2654853) (@lem2654851)). Qed.
Lemma lem2654855 : term183 = True.
Proof. exact (TRANS (@lem2654850) (@lem2654854)). Qed.
Lemma lem2654856 : True = term183.
Proof. exact (SYM (@lem2654855)). Qed.
Lemma lem2654857 : term183.
Proof. exact (EQ_MP (@lem2654856) (@lem0)). Qed.
Lemma lem2654858 : term222.
Proof. exact (@lem2654847 (@lem2654857)). Qed.
Lemma lem2654860 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654861 : term115 = term116.
Proof. exact (@lem2654860 term50 term50). Qed.
Lemma lem2654862 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654863 : term118 = term50.
Proof. exact (EQ_MP (@lem2654862) (@lem940073)). Qed.
Lemma lem2654864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654865 : term116 = term49.
Proof. exact (MK_COMB (@lem2654864) (@lem2654863)). Qed.
Lemma lem2654866 : term115 = term49.
Proof. exact (TRANS (@lem2654861) (@lem2654865)). Qed.
Lemma lem2654868 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2654869 : term110 = term121.
Proof. exact (@lem2654868 term50 term50). Qed.
Lemma lem2654870 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654871 : term118 = term50.
Proof. exact (EQ_MP (@lem2654870) (@lem940073)). Qed.
Lemma lem2654872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654873 : term116 = term49.
Proof. exact (MK_COMB (@lem2654872) (@lem2654871)). Qed.
Lemma lem2654874 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2654875 : term121 = term106.
Proof. exact (MK_COMB (@lem2654874) (@lem2654873)). Qed.
Lemma lem2654876 : term110 = term106.
Proof. exact (TRANS (@lem2654869) (@lem2654875)). Qed.
Lemma lem2654877 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2654878 : term223 = term215.
Proof. exact (MK_COMB (@lem2654877) (@lem2654876)). Qed.
Lemma lem2654879 : term224 = term217.
Proof. exact (MK_COMB (@lem2654878) (@lem2654866)). Qed.
Lemma lem2654881 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2654882 : term217 = term45.
Proof. exact (@lem2654881 term50). Qed.
Lemma lem2654883 : term224 = term45.
Proof. exact (TRANS (@lem2654879) (@lem2654882)). Qed.
Lemma lem2654884 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2654885 : term226 = term227.
Proof. exact (MK_COMB (@lem2654884) (@lem2654883)). Qed.
Lemma lem2654886 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2654887 : term228 = term194.
Proof. exact (MK_COMB (@lem2654885) (@lem2654886)). Qed.
Lemma lem2654889 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2654890 : term194 = term45.
Proof. exact (@lem2654889 term50). Qed.
Lemma lem2654891 : term228 = term45.
Proof. exact (TRANS (@lem2654887) (@lem2654890)). Qed.
Lemma lem2654893 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2654894 : term115 = term116.
Proof. exact (@lem2654893 term50 term50). Qed.
Lemma lem2654895 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654896 : term118 = term50.
Proof. exact (EQ_MP (@lem2654895) (@lem940073)). Qed.
Lemma lem2654897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654898 : term116 = term49.
Proof. exact (MK_COMB (@lem2654897) (@lem2654896)). Qed.
Lemma lem2654899 : term115 = term49.
Proof. exact (TRANS (@lem2654894) (@lem2654898)). Qed.
Lemma lem2654900 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2654901 : term229 = term194.
Proof. exact (MK_COMB (@lem2654900) (@lem2654899)). Qed.
Lemma lem2654903 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2654904 : term194 = term45.
Proof. exact (@lem2654903 term50). Qed.
Lemma lem2654905 : term229 = term45.
Proof. exact (TRANS (@lem2654901) (@lem2654904)). Qed.
Lemma lem2654906 : term45 = term229.
Proof. exact (SYM (@lem2654905)). Qed.
Lemma lem2654907 : term228 = term229.
Proof. exact (TRANS (@lem2654891) (@lem2654906)). Qed.
Lemma lem2654908 : term218 = term142.
Proof. exact (@lem2654858 (@lem2654907)). Qed.
Lemma lem2654909 : term217 = term142.
Proof. exact (TRANS (@lem2654824) (@lem2654908)). Qed.
Lemma lem2654911 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2654912 : term142 = term45.
Proof. exact (@lem2654911 term45). Qed.
Lemma lem2654913 : term217 = term45.
Proof. exact (TRANS (@lem2654909) (@lem2654912)). Qed.
Lemma lem2654914 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2654915 : term230 = term227.
Proof. exact (MK_COMB (@lem2654914) (@lem2654913)). Qed.
Lemma lem2654916 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2654917 (m : int) : (term214 m) = (term231 m).
Proof. exact (MK_COMB (@lem2654915) (@lem2654916 m)). Qed.
Lemma lem2654918 (m : int) : (term213 m) = (term231 m).
Proof. exact (TRANS (@lem2654815 m) (@lem2654917 m)). Qed.
Lemma lem2654919 (m : int) : (term231 m) = term45.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2654920 (m : int) : (term213 m) = term45.
Proof. exact (TRANS (@lem2654918 m) (@lem2654919 m)). Qed.
Lemma lem2654921 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2654922 (m : int) : (term232 m) = term47.
Proof. exact (MK_COMB (@lem2654921) (@lem2654920 m)). Qed.
Lemma lem2654924 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2654925 : term106 = term107.
Proof. exact (@lem2654924 term50). Qed.
Lemma lem2654927 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2654928 : term106 = term107.
Proof. exact (@lem2654927 term50). Qed.
Lemma lem2654929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2654930 : term215 = term216.
Proof. exact (MK_COMB (@lem2654929) (@lem2654928)). Qed.
Lemma lem2654931 : term233 = term234.
Proof. exact (MK_COMB (@lem2654930) (@lem2654925)). Qed.
Lemma lem2654932 : term235.
Proof. exact (@lem1981473 term106 term49 term106 term49 term236 term49). Qed.
Lemma lem2654934 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654935 : term183 = term189.
Proof. exact (@lem2654934 (NUMERAL 0) term50). Qed.
Lemma lem2654936 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654937 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654938 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654937 h1) (fun h1 : term189 = True => @lem2654936)). Qed.
Lemma lem2654939 : term189 = True.
Proof. exact (EQ_MP (@lem2654938) (@lem2654936)). Qed.
Lemma lem2654940 : term183 = True.
Proof. exact (TRANS (@lem2654935) (@lem2654939)). Qed.
Lemma lem2654941 : True = term183.
Proof. exact (SYM (@lem2654940)). Qed.
Lemma lem2654942 : term183.
Proof. exact (EQ_MP (@lem2654941) (@lem0)). Qed.
Lemma lem2654943 : term237.
Proof. exact (@lem2654932 (@lem2654942)). Qed.
Lemma lem2654945 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654946 : term183 = term189.
Proof. exact (@lem2654945 (NUMERAL 0) term50). Qed.
Lemma lem2654947 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654948 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654949 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654948 h1) (fun h1 : term189 = True => @lem2654947)). Qed.
Lemma lem2654950 : term189 = True.
Proof. exact (EQ_MP (@lem2654949) (@lem2654947)). Qed.
Lemma lem2654951 : term183 = True.
Proof. exact (TRANS (@lem2654946) (@lem2654950)). Qed.
Lemma lem2654952 : True = term183.
Proof. exact (SYM (@lem2654951)). Qed.
Lemma lem2654953 : term183.
Proof. exact (EQ_MP (@lem2654952) (@lem0)). Qed.
Lemma lem2654954 : term238.
Proof. exact (@lem2654943 (@lem2654953)). Qed.
Lemma lem2654956 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2654957 : term183 = term189.
Proof. exact (@lem2654956 (NUMERAL 0) term50). Qed.
Lemma lem2654958 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2654959 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2654960 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2654959 h1) (fun h1 : term189 = True => @lem2654958)). Qed.
Lemma lem2654961 : term189 = True.
Proof. exact (EQ_MP (@lem2654960) (@lem2654958)). Qed.
Lemma lem2654962 : term183 = True.
Proof. exact (TRANS (@lem2654957) (@lem2654961)). Qed.
Lemma lem2654963 : True = term183.
Proof. exact (SYM (@lem2654962)). Qed.
Lemma lem2654964 : term183.
Proof. exact (EQ_MP (@lem2654963) (@lem0)). Qed.
Lemma lem2654965 : term239.
Proof. exact (@lem2654954 (@lem2654964)). Qed.
Lemma lem2654967 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2654968 : term110 = term121.
Proof. exact (@lem2654967 term50 term50). Qed.
Lemma lem2654969 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654970 : term118 = term50.
Proof. exact (EQ_MP (@lem2654969) (@lem940073)). Qed.
Lemma lem2654971 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654972 : term116 = term49.
Proof. exact (MK_COMB (@lem2654971) (@lem2654970)). Qed.
Lemma lem2654973 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2654974 : term121 = term106.
Proof. exact (MK_COMB (@lem2654973) (@lem2654972)). Qed.
Lemma lem2654975 : term110 = term106.
Proof. exact (TRANS (@lem2654968) (@lem2654974)). Qed.
Lemma lem2654977 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2654978 : term110 = term121.
Proof. exact (@lem2654977 term50 term50). Qed.
Lemma lem2654979 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2654980 : term118 = term50.
Proof. exact (EQ_MP (@lem2654979) (@lem940073)). Qed.
Lemma lem2654981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654982 : term116 = term49.
Proof. exact (MK_COMB (@lem2654981) (@lem2654980)). Qed.
Lemma lem2654983 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2654984 : term121 = term106.
Proof. exact (MK_COMB (@lem2654983) (@lem2654982)). Qed.
Lemma lem2654985 : term110 = term106.
Proof. exact (TRANS (@lem2654978) (@lem2654984)). Qed.
Lemma lem2654986 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2654987 : term223 = term215.
Proof. exact (MK_COMB (@lem2654986) (@lem2654985)). Qed.
Lemma lem2654988 : term240 = term233.
Proof. exact (MK_COMB (@lem2654987) (@lem2654975)). Qed.
Lemma lem2654989 : term233 = term241.
Proof. exact (@lem1367763 term50 term50). Qed.
Lemma lem2654990 : term242 = term243.
Proof. exact (@lem706885). Qed.
Lemma lem2654991 : (term242 = term243) = (term244 = term245).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term243). Qed.
Lemma lem2654992 : term244 = term245.
Proof. exact (EQ_MP (@lem2654991) (@lem2654990)). Qed.
Lemma lem2654993 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2654994 : term246 = term247.
Proof. exact (MK_COMB (@lem2654993) (@lem2654992)). Qed.
Lemma lem2654995 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2654996 : term241 = term236.
Proof. exact (MK_COMB (@lem2654995) (@lem2654994)). Qed.
Lemma lem2654997 : term233 = term236.
Proof. exact (TRANS (@lem2654989) (@lem2654996)). Qed.
Lemma lem2654998 : term240 = term236.
Proof. exact (TRANS (@lem2654988) (@lem2654997)). Qed.
Lemma lem2654999 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2655000 : term248 = term249.
Proof. exact (MK_COMB (@lem2654999) (@lem2654998)). Qed.
Lemma lem2655001 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2655002 : term250 = term251.
Proof. exact (MK_COMB (@lem2655000) (@lem2655001)). Qed.
Lemma lem2655004 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655005 : term251 = term252.
Proof. exact (@lem2655004 term245 term50). Qed.
Lemma lem2655006 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2655007 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2655008 : term254 = term245.
Proof. exact (EQ_MP (@lem2655007) (@lem2655006)). Qed.
Lemma lem2655009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655010 : term255 = term247.
Proof. exact (MK_COMB (@lem2655009) (@lem2655008)). Qed.
Lemma lem2655011 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655012 : term252 = term236.
Proof. exact (MK_COMB (@lem2655011) (@lem2655010)). Qed.
Lemma lem2655013 : term251 = term236.
Proof. exact (TRANS (@lem2655005) (@lem2655012)). Qed.
Lemma lem2655014 : term250 = term236.
Proof. exact (TRANS (@lem2655002) (@lem2655013)). Qed.
Lemma lem2655016 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655017 : term115 = term116.
Proof. exact (@lem2655016 term50 term50). Qed.
Lemma lem2655018 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655019 : term118 = term50.
Proof. exact (EQ_MP (@lem2655018) (@lem940073)). Qed.
Lemma lem2655020 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655021 : term116 = term49.
Proof. exact (MK_COMB (@lem2655020) (@lem2655019)). Qed.
Lemma lem2655022 : term115 = term49.
Proof. exact (TRANS (@lem2655017) (@lem2655021)). Qed.
Lemma lem2655023 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem2655024 : term256 = term251.
Proof. exact (MK_COMB (@lem2655023) (@lem2655022)). Qed.
Lemma lem2655026 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655027 : term251 = term252.
Proof. exact (@lem2655026 term245 term50). Qed.
Lemma lem2655028 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2655029 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2655030 : term254 = term245.
Proof. exact (EQ_MP (@lem2655029) (@lem2655028)). Qed.
Lemma lem2655031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655032 : term255 = term247.
Proof. exact (MK_COMB (@lem2655031) (@lem2655030)). Qed.
Lemma lem2655033 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655034 : term252 = term236.
Proof. exact (MK_COMB (@lem2655033) (@lem2655032)). Qed.
Lemma lem2655035 : term251 = term236.
Proof. exact (TRANS (@lem2655027) (@lem2655034)). Qed.
Lemma lem2655036 : term256 = term236.
Proof. exact (TRANS (@lem2655024) (@lem2655035)). Qed.
Lemma lem2655037 : term236 = term256.
Proof. exact (SYM (@lem2655036)). Qed.
Lemma lem2655038 : term250 = term256.
Proof. exact (TRANS (@lem2655014) (@lem2655037)). Qed.
Lemma lem2655039 : term234 = term257.
Proof. exact (@lem2654965 (@lem2655038)). Qed.
Lemma lem2655040 : term233 = term257.
Proof. exact (TRANS (@lem2654931) (@lem2655039)). Qed.
Lemma lem2655042 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2655043 : term257 = term236.
Proof. exact (@lem2655042 term236). Qed.
Lemma lem2655044 : term233 = term236.
Proof. exact (TRANS (@lem2655040) (@lem2655043)). Qed.
Lemma lem2655045 (m : int) : (term212 m) = term258.
Proof. exact (MK_COMB (@lem2654922 m) (@lem2655044)). Qed.
Lemma lem2655046 (m : int) : (term211 m) = term258.
Proof. exact (TRANS (@lem2654814 m) (@lem2655045 m)). Qed.
Lemma lem2655047 : term258 = term236.
Proof. exact (@lem1982721 term236). Qed.
Lemma lem2655048 (m : int) : (term211 m) = term236.
Proof. exact (TRANS (@lem2655046 m) (@lem2655047)). Qed.
Lemma lem2655049 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2655050 (m : int) : (term259 m) = term260.
Proof. exact (MK_COMB (@lem2655049) (@lem2655048 m)). Qed.
Lemma lem2655051 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2655052 (m : int) : (term210 m) = term261.
Proof. exact (MK_COMB (@lem2655050 m) (@lem2655051)). Qed.
Lemma lem2655053 (n : int) (m : int) (h1 : term352 n m) : term261.
Proof. exact (EQ_MP (@lem2655052 m) (@lem2654813 n m h1)). Qed.
Lemma lem2655055 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2655056 : term261 = term262.
Proof. exact (@lem2655055 term45 term236). Qed.
Lemma lem2655058 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2655059 : term236 = term257.
Proof. exact (@lem2655058 term245). Qed.
Lemma lem2655061 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655062 : term45 = term142.
Proof. exact (@lem2655061 (NUMERAL 0)). Qed.
Lemma lem2655063 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2655064 : term80 = term263.
Proof. exact (MK_COMB (@lem2655063) (@lem2655062)). Qed.
Lemma lem2655065 : term262 = term264.
Proof. exact (MK_COMB (@lem2655064) (@lem2655059)). Qed.
Lemma lem2655066 : term265.
Proof. exact (@lem1980026 term45 term49 term236 term49). Qed.
Lemma lem2655068 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655069 : term183 = term189.
Proof. exact (@lem2655068 (NUMERAL 0) term50). Qed.
Lemma lem2655070 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655071 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655072 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655071 h1) (fun h1 : term189 = True => @lem2655070)). Qed.
Lemma lem2655073 : term189 = True.
Proof. exact (EQ_MP (@lem2655072) (@lem2655070)). Qed.
Lemma lem2655074 : term183 = True.
Proof. exact (TRANS (@lem2655069) (@lem2655073)). Qed.
Lemma lem2655075 : True = term183.
Proof. exact (SYM (@lem2655074)). Qed.
Lemma lem2655076 : term183.
Proof. exact (EQ_MP (@lem2655075) (@lem0)). Qed.
Lemma lem2655077 : term266.
Proof. exact (@lem2655066 (@lem2655076)). Qed.
Lemma lem2655079 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655080 : term183 = term189.
Proof. exact (@lem2655079 (NUMERAL 0) term50). Qed.
Lemma lem2655081 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655082 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655083 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655082 h1) (fun h1 : term189 = True => @lem2655081)). Qed.
Lemma lem2655084 : term189 = True.
Proof. exact (EQ_MP (@lem2655083) (@lem2655081)). Qed.
Lemma lem2655085 : term183 = True.
Proof. exact (TRANS (@lem2655080) (@lem2655084)). Qed.
Lemma lem2655086 : True = term183.
Proof. exact (SYM (@lem2655085)). Qed.
Lemma lem2655087 : term183.
Proof. exact (EQ_MP (@lem2655086) (@lem0)). Qed.
Lemma lem2655088 : term264 = term267.
Proof. exact (@lem2655077 (@lem2655087)). Qed.
Lemma lem2655090 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655091 : term251 = term252.
Proof. exact (@lem2655090 term245 term50). Qed.
Lemma lem2655092 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2655093 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2655094 : term254 = term245.
Proof. exact (EQ_MP (@lem2655093) (@lem2655092)). Qed.
Lemma lem2655095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655096 : term255 = term247.
Proof. exact (MK_COMB (@lem2655095) (@lem2655094)). Qed.
Lemma lem2655097 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655098 : term252 = term236.
Proof. exact (MK_COMB (@lem2655097) (@lem2655096)). Qed.
Lemma lem2655099 : term251 = term236.
Proof. exact (TRANS (@lem2655091) (@lem2655098)). Qed.
Lemma lem2655101 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2655102 : term194 = term45.
Proof. exact (@lem2655101 term50). Qed.
Lemma lem2655103 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2655104 : term268 = term80.
Proof. exact (MK_COMB (@lem2655103) (@lem2655102)). Qed.
Lemma lem2655105 : term267 = term262.
Proof. exact (MK_COMB (@lem2655104) (@lem2655099)). Qed.
Lemma lem2655107 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2655108 : term262 = term271.
Proof. exact (@lem2655107 (NUMERAL 0) term245). Qed.
Lemma lem2655109 : term272 = term243.
Proof. exact (@lem912803). Qed.
Lemma lem2655110 (h1 : term272 = term243) : (term245 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term243 h1). Qed.
Lemma lem2655111 : (term272 = term243) = ((term245 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term272 = term243 => @lem2655110 h1) (fun h1 : (term245 = (NUMERAL 0)) = False => @lem2655109)). Qed.
Lemma lem2655112 : (term245 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2655111) (@lem2655109)). Qed.
Lemma lem2655113 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2655114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2655115 : term273 = (and True).
Proof. exact (MK_COMB (@lem2655114) (@lem2655113)). Qed.
Lemma lem2655116 : term271 = (True /\ False).
Proof. exact (MK_COMB (@lem2655115) (@lem2655112)). Qed.
Lemma lem2655118 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2655119 : term271 = False.
Proof. exact (TRANS (@lem2655116) (@lem2655118)). Qed.
Lemma lem2655120 : term262 = False.
Proof. exact (TRANS (@lem2655108) (@lem2655119)). Qed.
Lemma lem2655121 : term267 = False.
Proof. exact (TRANS (@lem2655105) (@lem2655120)). Qed.
Lemma lem2655122 : term264 = False.
Proof. exact (TRANS (@lem2655088) (@lem2655121)). Qed.
Lemma lem2655123 : term262 = False.
Proof. exact (TRANS (@lem2655065) (@lem2655122)). Qed.
Lemma lem2655124 : term261 = False.
Proof. exact (TRANS (@lem2655056) (@lem2655123)). Qed.
Lemma lem2655125 (n : int) (m : int) (h1 : term352 n m) : False.
Proof. exact (EQ_MP (@lem2655124) (@lem2655053 n m h1)). Qed.
Lemma lem2655126 (m : int) (n : int) (h1 : term364 m n) : term364 m n.
Proof. exact (h1). Qed.
Lemma lem2655127 (m : int) (n : int) (h1 : term364 m n) : term351 m n.
Proof. exact (proj2 (@lem2655126 m n h1)). Qed.
Lemma lem2655128 (m : int) (n : int) (h1 : term364 m n) : term128 n.
Proof. exact (proj1 (@lem2655126 m n h1)). Qed.
Lemma lem2655129 (m : int) (n : int) (h1 : term364 m n) : term139 n.
Proof. exact (proj2 (@lem2655127 m n h1)). Qed.
Lemma lem2655132 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2655133 : term182 = term183.
Proof. exact (@lem2655132 term45 term49). Qed.
Lemma lem2655135 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655136 : term49 = term103.
Proof. exact (@lem2655135 term50). Qed.
Lemma lem2655138 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655139 : term45 = term142.
Proof. exact (@lem2655138 (NUMERAL 0)). Qed.
Lemma lem2655140 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2655141 : term184 = term185.
Proof. exact (MK_COMB (@lem2655140) (@lem2655139)). Qed.
Lemma lem2655142 : term183 = term186.
Proof. exact (MK_COMB (@lem2655141) (@lem2655136)). Qed.
Lemma lem2655143 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2655145 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655146 : term183 = term189.
Proof. exact (@lem2655145 (NUMERAL 0) term50). Qed.
Lemma lem2655147 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655148 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655149 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655148 h1) (fun h1 : term189 = True => @lem2655147)). Qed.
Lemma lem2655150 : term189 = True.
Proof. exact (EQ_MP (@lem2655149) (@lem2655147)). Qed.
Lemma lem2655151 : term183 = True.
Proof. exact (TRANS (@lem2655146) (@lem2655150)). Qed.
Lemma lem2655152 : True = term183.
Proof. exact (SYM (@lem2655151)). Qed.
Lemma lem2655153 : term183.
Proof. exact (EQ_MP (@lem2655152) (@lem0)). Qed.
Lemma lem2655154 : term191.
Proof. exact (@lem2655143 (@lem2655153)). Qed.
Lemma lem2655156 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655157 : term183 = term189.
Proof. exact (@lem2655156 (NUMERAL 0) term50). Qed.
Lemma lem2655158 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655159 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655160 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655159 h1) (fun h1 : term189 = True => @lem2655158)). Qed.
Lemma lem2655161 : term189 = True.
Proof. exact (EQ_MP (@lem2655160) (@lem2655158)). Qed.
Lemma lem2655162 : term183 = True.
Proof. exact (TRANS (@lem2655157) (@lem2655161)). Qed.
Lemma lem2655163 : True = term183.
Proof. exact (SYM (@lem2655162)). Qed.
Lemma lem2655164 : term183.
Proof. exact (EQ_MP (@lem2655163) (@lem0)). Qed.
Lemma lem2655165 : term186 = term192.
Proof. exact (@lem2655154 (@lem2655164)). Qed.
Lemma lem2655167 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655168 : term115 = term116.
Proof. exact (@lem2655167 term50 term50). Qed.
Lemma lem2655169 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655170 : term118 = term50.
Proof. exact (EQ_MP (@lem2655169) (@lem940073)). Qed.
Lemma lem2655171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655172 : term116 = term49.
Proof. exact (MK_COMB (@lem2655171) (@lem2655170)). Qed.
Lemma lem2655173 : term115 = term49.
Proof. exact (TRANS (@lem2655168) (@lem2655172)). Qed.
Lemma lem2655175 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2655176 : term194 = term45.
Proof. exact (@lem2655175 term50). Qed.
Lemma lem2655177 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2655178 : term195 = term184.
Proof. exact (MK_COMB (@lem2655177) (@lem2655176)). Qed.
Lemma lem2655179 : term192 = term183.
Proof. exact (MK_COMB (@lem2655178) (@lem2655173)). Qed.
Lemma lem2655181 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655182 : term183 = term189.
Proof. exact (@lem2655181 (NUMERAL 0) term50). Qed.
Lemma lem2655183 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655184 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655185 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655184 h1) (fun h1 : term189 = True => @lem2655183)). Qed.
Lemma lem2655186 : term189 = True.
Proof. exact (EQ_MP (@lem2655185) (@lem2655183)). Qed.
Lemma lem2655187 : term183 = True.
Proof. exact (TRANS (@lem2655182) (@lem2655186)). Qed.
Lemma lem2655188 : term192 = True.
Proof. exact (TRANS (@lem2655179) (@lem2655187)). Qed.
Lemma lem2655189 : term186 = True.
Proof. exact (TRANS (@lem2655165) (@lem2655188)). Qed.
Lemma lem2655190 : term183 = True.
Proof. exact (TRANS (@lem2655142) (@lem2655189)). Qed.
Lemma lem2655191 : term182 = True.
Proof. exact (TRANS (@lem2655133) (@lem2655190)). Qed.
Lemma lem2655192 : True = term182.
Proof. exact (SYM (@lem2655191)). Qed.
Lemma lem2655193 : term182.
Proof. exact (EQ_MP (@lem2655192) (@lem0)). Qed.
Lemma lem2655194 (m : int) (n : int) (h1 : term364 m n) : term196 n.
Proof. exact (conj (@lem2655193) (@lem2655128 m n h1)). Qed.
Lemma lem2655196 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2655197 (n : int) : term198 n.
Proof. exact (@lem2655196 term49 (term125 n)). Qed.
Lemma lem2655198 (m : int) (n : int) (h1 : term364 m n) : term199 n.
Proof. exact (@lem2655197 n (@lem2655194 m n h1)). Qed.
Lemma lem2655199 (n : int) : (term200 n) = (term125 n).
Proof. exact (@lem1982733 (term125 n)). Qed.
Lemma lem2655200 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2655201 (n : int) : (term201 n) = (term127 n).
Proof. exact (MK_COMB (@lem2655200) (@lem2655199 n)). Qed.
Lemma lem2655202 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2655203 (n : int) : (term199 n) = (term128 n).
Proof. exact (MK_COMB (@lem2655201 n) (@lem2655202)). Qed.
Lemma lem2655204 (m : int) (n : int) (h1 : term364 m n) : term128 n.
Proof. exact (EQ_MP (@lem2655203 n) (@lem2655198 m n h1)). Qed.
Lemma lem2655206 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2655207 : term182 = term183.
Proof. exact (@lem2655206 term45 term49). Qed.
Lemma lem2655209 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655210 : term49 = term103.
Proof. exact (@lem2655209 term50). Qed.
Lemma lem2655212 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655213 : term45 = term142.
Proof. exact (@lem2655212 (NUMERAL 0)). Qed.
Lemma lem2655214 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2655215 : term184 = term185.
Proof. exact (MK_COMB (@lem2655214) (@lem2655213)). Qed.
Lemma lem2655216 : term183 = term186.
Proof. exact (MK_COMB (@lem2655215) (@lem2655210)). Qed.
Lemma lem2655217 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2655219 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655220 : term183 = term189.
Proof. exact (@lem2655219 (NUMERAL 0) term50). Qed.
Lemma lem2655221 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655222 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655223 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655222 h1) (fun h1 : term189 = True => @lem2655221)). Qed.
Lemma lem2655224 : term189 = True.
Proof. exact (EQ_MP (@lem2655223) (@lem2655221)). Qed.
Lemma lem2655225 : term183 = True.
Proof. exact (TRANS (@lem2655220) (@lem2655224)). Qed.
Lemma lem2655226 : True = term183.
Proof. exact (SYM (@lem2655225)). Qed.
Lemma lem2655227 : term183.
Proof. exact (EQ_MP (@lem2655226) (@lem0)). Qed.
Lemma lem2655228 : term191.
Proof. exact (@lem2655217 (@lem2655227)). Qed.
Lemma lem2655230 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655231 : term183 = term189.
Proof. exact (@lem2655230 (NUMERAL 0) term50). Qed.
Lemma lem2655232 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655233 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655234 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655233 h1) (fun h1 : term189 = True => @lem2655232)). Qed.
Lemma lem2655235 : term189 = True.
Proof. exact (EQ_MP (@lem2655234) (@lem2655232)). Qed.
Lemma lem2655236 : term183 = True.
Proof. exact (TRANS (@lem2655231) (@lem2655235)). Qed.
Lemma lem2655237 : True = term183.
Proof. exact (SYM (@lem2655236)). Qed.
Lemma lem2655238 : term183.
Proof. exact (EQ_MP (@lem2655237) (@lem0)). Qed.
Lemma lem2655239 : term186 = term192.
Proof. exact (@lem2655228 (@lem2655238)). Qed.
Lemma lem2655241 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655242 : term115 = term116.
Proof. exact (@lem2655241 term50 term50). Qed.
Lemma lem2655243 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655244 : term118 = term50.
Proof. exact (EQ_MP (@lem2655243) (@lem940073)). Qed.
Lemma lem2655245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655246 : term116 = term49.
Proof. exact (MK_COMB (@lem2655245) (@lem2655244)). Qed.
Lemma lem2655247 : term115 = term49.
Proof. exact (TRANS (@lem2655242) (@lem2655246)). Qed.
Lemma lem2655249 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2655250 : term194 = term45.
Proof. exact (@lem2655249 term50). Qed.
Lemma lem2655251 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2655252 : term195 = term184.
Proof. exact (MK_COMB (@lem2655251) (@lem2655250)). Qed.
Lemma lem2655253 : term192 = term183.
Proof. exact (MK_COMB (@lem2655252) (@lem2655247)). Qed.
Lemma lem2655255 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655256 : term183 = term189.
Proof. exact (@lem2655255 (NUMERAL 0) term50). Qed.
Lemma lem2655257 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655258 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655259 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655258 h1) (fun h1 : term189 = True => @lem2655257)). Qed.
Lemma lem2655260 : term189 = True.
Proof. exact (EQ_MP (@lem2655259) (@lem2655257)). Qed.
Lemma lem2655261 : term183 = True.
Proof. exact (TRANS (@lem2655256) (@lem2655260)). Qed.
Lemma lem2655262 : term192 = True.
Proof. exact (TRANS (@lem2655253) (@lem2655261)). Qed.
Lemma lem2655263 : term186 = True.
Proof. exact (TRANS (@lem2655239) (@lem2655262)). Qed.
Lemma lem2655264 : term183 = True.
Proof. exact (TRANS (@lem2655216) (@lem2655263)). Qed.
Lemma lem2655265 : term182 = True.
Proof. exact (TRANS (@lem2655207) (@lem2655264)). Qed.
Lemma lem2655266 : True = term182.
Proof. exact (SYM (@lem2655265)). Qed.
Lemma lem2655267 : term182.
Proof. exact (EQ_MP (@lem2655266) (@lem0)). Qed.
Lemma lem2655268 (m : int) (n : int) (h1 : term364 m n) : term202 n.
Proof. exact (conj (@lem2655267) (@lem2655129 m n h1)). Qed.
Lemma lem2655270 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2655271 (n : int) : term203 n.
Proof. exact (@lem2655270 term49 (term135 n)). Qed.
Lemma lem2655272 (m : int) (n : int) (h1 : term364 m n) : term204 n.
Proof. exact (@lem2655271 n (@lem2655268 m n h1)). Qed.
Lemma lem2655273 (n : int) : (term205 n) = (term135 n).
Proof. exact (@lem1982733 (term135 n)). Qed.
Lemma lem2655274 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2655275 (n : int) : (term206 n) = (term138 n).
Proof. exact (MK_COMB (@lem2655274) (@lem2655273 n)). Qed.
Lemma lem2655276 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2655277 (n : int) : (term204 n) = (term139 n).
Proof. exact (MK_COMB (@lem2655275 n) (@lem2655276)). Qed.
Lemma lem2655278 (m : int) (n : int) (h1 : term364 m n) : term139 n.
Proof. exact (EQ_MP (@lem2655277 n) (@lem2655272 m n h1)). Qed.
Lemma lem2655279 (m : int) (n : int) (h1 : term364 m n) : term207 n.
Proof. exact (conj (@lem2655278 m n h1) (@lem2655204 m n h1)). Qed.
Lemma lem2655281 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2655282 (n : int) : term209 n.
Proof. exact (@lem2655281 (term135 n) (term125 n)). Qed.
Lemma lem2655283 (m : int) (n : int) (h1 : term364 m n) : term210 n.
Proof. exact (@lem2655282 n (@lem2655279 m n h1)). Qed.
Lemma lem2655284 (n : int) : (term211 n) = (term212 n).
Proof. exact (@lem1982753 (term158 n) (real_of_int n) term106 term106). Qed.
Lemma lem2655285 (n : int) : (term213 n) = (term214 n).
Proof. exact (@lem1982713 term106 (real_of_int n)). Qed.
Lemma lem2655287 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655288 : term49 = term103.
Proof. exact (@lem2655287 term50). Qed.
Lemma lem2655290 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2655291 : term106 = term107.
Proof. exact (@lem2655290 term50). Qed.
Lemma lem2655292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2655293 : term215 = term216.
Proof. exact (MK_COMB (@lem2655292) (@lem2655291)). Qed.
Lemma lem2655294 : term217 = term218.
Proof. exact (MK_COMB (@lem2655293) (@lem2655288)). Qed.
Lemma lem2655295 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2655297 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655298 : term183 = term189.
Proof. exact (@lem2655297 (NUMERAL 0) term50). Qed.
Lemma lem2655299 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655300 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655301 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655300 h1) (fun h1 : term189 = True => @lem2655299)). Qed.
Lemma lem2655302 : term189 = True.
Proof. exact (EQ_MP (@lem2655301) (@lem2655299)). Qed.
Lemma lem2655303 : term183 = True.
Proof. exact (TRANS (@lem2655298) (@lem2655302)). Qed.
Lemma lem2655304 : True = term183.
Proof. exact (SYM (@lem2655303)). Qed.
Lemma lem2655305 : term183.
Proof. exact (EQ_MP (@lem2655304) (@lem0)). Qed.
Lemma lem2655306 : term220.
Proof. exact (@lem2655295 (@lem2655305)). Qed.
Lemma lem2655308 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655309 : term183 = term189.
Proof. exact (@lem2655308 (NUMERAL 0) term50). Qed.
Lemma lem2655310 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655311 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655312 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655311 h1) (fun h1 : term189 = True => @lem2655310)). Qed.
Lemma lem2655313 : term189 = True.
Proof. exact (EQ_MP (@lem2655312) (@lem2655310)). Qed.
Lemma lem2655314 : term183 = True.
Proof. exact (TRANS (@lem2655309) (@lem2655313)). Qed.
Lemma lem2655315 : True = term183.
Proof. exact (SYM (@lem2655314)). Qed.
Lemma lem2655316 : term183.
Proof. exact (EQ_MP (@lem2655315) (@lem0)). Qed.
Lemma lem2655317 : term221.
Proof. exact (@lem2655306 (@lem2655316)). Qed.
Lemma lem2655319 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655320 : term183 = term189.
Proof. exact (@lem2655319 (NUMERAL 0) term50). Qed.
Lemma lem2655321 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655322 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655323 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655322 h1) (fun h1 : term189 = True => @lem2655321)). Qed.
Lemma lem2655324 : term189 = True.
Proof. exact (EQ_MP (@lem2655323) (@lem2655321)). Qed.
Lemma lem2655325 : term183 = True.
Proof. exact (TRANS (@lem2655320) (@lem2655324)). Qed.
Lemma lem2655326 : True = term183.
Proof. exact (SYM (@lem2655325)). Qed.
Lemma lem2655327 : term183.
Proof. exact (EQ_MP (@lem2655326) (@lem0)). Qed.
Lemma lem2655328 : term222.
Proof. exact (@lem2655317 (@lem2655327)). Qed.
Lemma lem2655330 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655331 : term115 = term116.
Proof. exact (@lem2655330 term50 term50). Qed.
Lemma lem2655332 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655333 : term118 = term50.
Proof. exact (EQ_MP (@lem2655332) (@lem940073)). Qed.
Lemma lem2655334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655335 : term116 = term49.
Proof. exact (MK_COMB (@lem2655334) (@lem2655333)). Qed.
Lemma lem2655336 : term115 = term49.
Proof. exact (TRANS (@lem2655331) (@lem2655335)). Qed.
Lemma lem2655338 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655339 : term110 = term121.
Proof. exact (@lem2655338 term50 term50). Qed.
Lemma lem2655340 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655341 : term118 = term50.
Proof. exact (EQ_MP (@lem2655340) (@lem940073)). Qed.
Lemma lem2655342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655343 : term116 = term49.
Proof. exact (MK_COMB (@lem2655342) (@lem2655341)). Qed.
Lemma lem2655344 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655345 : term121 = term106.
Proof. exact (MK_COMB (@lem2655344) (@lem2655343)). Qed.
Lemma lem2655346 : term110 = term106.
Proof. exact (TRANS (@lem2655339) (@lem2655345)). Qed.
Lemma lem2655347 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2655348 : term223 = term215.
Proof. exact (MK_COMB (@lem2655347) (@lem2655346)). Qed.
Lemma lem2655349 : term224 = term217.
Proof. exact (MK_COMB (@lem2655348) (@lem2655336)). Qed.
Lemma lem2655351 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2655352 : term217 = term45.
Proof. exact (@lem2655351 term50). Qed.
Lemma lem2655353 : term224 = term45.
Proof. exact (TRANS (@lem2655349) (@lem2655352)). Qed.
Lemma lem2655354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2655355 : term226 = term227.
Proof. exact (MK_COMB (@lem2655354) (@lem2655353)). Qed.
Lemma lem2655356 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2655357 : term228 = term194.
Proof. exact (MK_COMB (@lem2655355) (@lem2655356)). Qed.
Lemma lem2655359 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2655360 : term194 = term45.
Proof. exact (@lem2655359 term50). Qed.
Lemma lem2655361 : term228 = term45.
Proof. exact (TRANS (@lem2655357) (@lem2655360)). Qed.
Lemma lem2655363 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655364 : term115 = term116.
Proof. exact (@lem2655363 term50 term50). Qed.
Lemma lem2655365 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655366 : term118 = term50.
Proof. exact (EQ_MP (@lem2655365) (@lem940073)). Qed.
Lemma lem2655367 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655368 : term116 = term49.
Proof. exact (MK_COMB (@lem2655367) (@lem2655366)). Qed.
Lemma lem2655369 : term115 = term49.
Proof. exact (TRANS (@lem2655364) (@lem2655368)). Qed.
Lemma lem2655370 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2655371 : term229 = term194.
Proof. exact (MK_COMB (@lem2655370) (@lem2655369)). Qed.
Lemma lem2655373 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2655374 : term194 = term45.
Proof. exact (@lem2655373 term50). Qed.
Lemma lem2655375 : term229 = term45.
Proof. exact (TRANS (@lem2655371) (@lem2655374)). Qed.
Lemma lem2655376 : term45 = term229.
Proof. exact (SYM (@lem2655375)). Qed.
Lemma lem2655377 : term228 = term229.
Proof. exact (TRANS (@lem2655361) (@lem2655376)). Qed.
Lemma lem2655378 : term218 = term142.
Proof. exact (@lem2655328 (@lem2655377)). Qed.
Lemma lem2655379 : term217 = term142.
Proof. exact (TRANS (@lem2655294) (@lem2655378)). Qed.
Lemma lem2655381 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2655382 : term142 = term45.
Proof. exact (@lem2655381 term45). Qed.
Lemma lem2655383 : term217 = term45.
Proof. exact (TRANS (@lem2655379) (@lem2655382)). Qed.
Lemma lem2655384 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2655385 : term230 = term227.
Proof. exact (MK_COMB (@lem2655384) (@lem2655383)). Qed.
Lemma lem2655386 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2655387 (n : int) : (term214 n) = (term231 n).
Proof. exact (MK_COMB (@lem2655385) (@lem2655386 n)). Qed.
Lemma lem2655388 (n : int) : (term213 n) = (term231 n).
Proof. exact (TRANS (@lem2655285 n) (@lem2655387 n)). Qed.
Lemma lem2655389 (n : int) : (term231 n) = term45.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2655390 (n : int) : (term213 n) = term45.
Proof. exact (TRANS (@lem2655388 n) (@lem2655389 n)). Qed.
Lemma lem2655391 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2655392 (n : int) : (term232 n) = term47.
Proof. exact (MK_COMB (@lem2655391) (@lem2655390 n)). Qed.
Lemma lem2655394 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2655395 : term106 = term107.
Proof. exact (@lem2655394 term50). Qed.
Lemma lem2655397 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2655398 : term106 = term107.
Proof. exact (@lem2655397 term50). Qed.
Lemma lem2655399 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2655400 : term215 = term216.
Proof. exact (MK_COMB (@lem2655399) (@lem2655398)). Qed.
Lemma lem2655401 : term233 = term234.
Proof. exact (MK_COMB (@lem2655400) (@lem2655395)). Qed.
Lemma lem2655402 : term235.
Proof. exact (@lem1981473 term106 term49 term106 term49 term236 term49). Qed.
Lemma lem2655404 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655405 : term183 = term189.
Proof. exact (@lem2655404 (NUMERAL 0) term50). Qed.
Lemma lem2655406 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655407 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655408 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655407 h1) (fun h1 : term189 = True => @lem2655406)). Qed.
Lemma lem2655409 : term189 = True.
Proof. exact (EQ_MP (@lem2655408) (@lem2655406)). Qed.
Lemma lem2655410 : term183 = True.
Proof. exact (TRANS (@lem2655405) (@lem2655409)). Qed.
Lemma lem2655411 : True = term183.
Proof. exact (SYM (@lem2655410)). Qed.
Lemma lem2655412 : term183.
Proof. exact (EQ_MP (@lem2655411) (@lem0)). Qed.
Lemma lem2655413 : term237.
Proof. exact (@lem2655402 (@lem2655412)). Qed.
Lemma lem2655415 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655416 : term183 = term189.
Proof. exact (@lem2655415 (NUMERAL 0) term50). Qed.
Lemma lem2655417 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655418 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655419 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655418 h1) (fun h1 : term189 = True => @lem2655417)). Qed.
Lemma lem2655420 : term189 = True.
Proof. exact (EQ_MP (@lem2655419) (@lem2655417)). Qed.
Lemma lem2655421 : term183 = True.
Proof. exact (TRANS (@lem2655416) (@lem2655420)). Qed.
Lemma lem2655422 : True = term183.
Proof. exact (SYM (@lem2655421)). Qed.
Lemma lem2655423 : term183.
Proof. exact (EQ_MP (@lem2655422) (@lem0)). Qed.
Lemma lem2655424 : term238.
Proof. exact (@lem2655413 (@lem2655423)). Qed.
Lemma lem2655426 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655427 : term183 = term189.
Proof. exact (@lem2655426 (NUMERAL 0) term50). Qed.
Lemma lem2655428 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655429 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655430 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655429 h1) (fun h1 : term189 = True => @lem2655428)). Qed.
Lemma lem2655431 : term189 = True.
Proof. exact (EQ_MP (@lem2655430) (@lem2655428)). Qed.
Lemma lem2655432 : term183 = True.
Proof. exact (TRANS (@lem2655427) (@lem2655431)). Qed.
Lemma lem2655433 : True = term183.
Proof. exact (SYM (@lem2655432)). Qed.
Lemma lem2655434 : term183.
Proof. exact (EQ_MP (@lem2655433) (@lem0)). Qed.
Lemma lem2655435 : term239.
Proof. exact (@lem2655424 (@lem2655434)). Qed.
Lemma lem2655437 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655438 : term110 = term121.
Proof. exact (@lem2655437 term50 term50). Qed.
Lemma lem2655439 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655440 : term118 = term50.
Proof. exact (EQ_MP (@lem2655439) (@lem940073)). Qed.
Lemma lem2655441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655442 : term116 = term49.
Proof. exact (MK_COMB (@lem2655441) (@lem2655440)). Qed.
Lemma lem2655443 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655444 : term121 = term106.
Proof. exact (MK_COMB (@lem2655443) (@lem2655442)). Qed.
Lemma lem2655445 : term110 = term106.
Proof. exact (TRANS (@lem2655438) (@lem2655444)). Qed.
Lemma lem2655447 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655448 : term110 = term121.
Proof. exact (@lem2655447 term50 term50). Qed.
Lemma lem2655449 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655450 : term118 = term50.
Proof. exact (EQ_MP (@lem2655449) (@lem940073)). Qed.
Lemma lem2655451 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655452 : term116 = term49.
Proof. exact (MK_COMB (@lem2655451) (@lem2655450)). Qed.
Lemma lem2655453 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655454 : term121 = term106.
Proof. exact (MK_COMB (@lem2655453) (@lem2655452)). Qed.
Lemma lem2655455 : term110 = term106.
Proof. exact (TRANS (@lem2655448) (@lem2655454)). Qed.
Lemma lem2655456 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2655457 : term223 = term215.
Proof. exact (MK_COMB (@lem2655456) (@lem2655455)). Qed.
Lemma lem2655458 : term240 = term233.
Proof. exact (MK_COMB (@lem2655457) (@lem2655445)). Qed.
Lemma lem2655459 : term233 = term241.
Proof. exact (@lem1367763 term50 term50). Qed.
Lemma lem2655460 : term242 = term243.
Proof. exact (@lem706885). Qed.
Lemma lem2655461 : (term242 = term243) = (term244 = term245).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term243). Qed.
Lemma lem2655462 : term244 = term245.
Proof. exact (EQ_MP (@lem2655461) (@lem2655460)). Qed.
Lemma lem2655463 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655464 : term246 = term247.
Proof. exact (MK_COMB (@lem2655463) (@lem2655462)). Qed.
Lemma lem2655465 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655466 : term241 = term236.
Proof. exact (MK_COMB (@lem2655465) (@lem2655464)). Qed.
Lemma lem2655467 : term233 = term236.
Proof. exact (TRANS (@lem2655459) (@lem2655466)). Qed.
Lemma lem2655468 : term240 = term236.
Proof. exact (TRANS (@lem2655458) (@lem2655467)). Qed.
Lemma lem2655469 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2655470 : term248 = term249.
Proof. exact (MK_COMB (@lem2655469) (@lem2655468)). Qed.
Lemma lem2655471 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2655472 : term250 = term251.
Proof. exact (MK_COMB (@lem2655470) (@lem2655471)). Qed.
Lemma lem2655474 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655475 : term251 = term252.
Proof. exact (@lem2655474 term245 term50). Qed.
Lemma lem2655476 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2655477 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2655478 : term254 = term245.
Proof. exact (EQ_MP (@lem2655477) (@lem2655476)). Qed.
Lemma lem2655479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655480 : term255 = term247.
Proof. exact (MK_COMB (@lem2655479) (@lem2655478)). Qed.
Lemma lem2655481 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655482 : term252 = term236.
Proof. exact (MK_COMB (@lem2655481) (@lem2655480)). Qed.
Lemma lem2655483 : term251 = term236.
Proof. exact (TRANS (@lem2655475) (@lem2655482)). Qed.
Lemma lem2655484 : term250 = term236.
Proof. exact (TRANS (@lem2655472) (@lem2655483)). Qed.
Lemma lem2655486 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655487 : term115 = term116.
Proof. exact (@lem2655486 term50 term50). Qed.
Lemma lem2655488 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655489 : term118 = term50.
Proof. exact (EQ_MP (@lem2655488) (@lem940073)). Qed.
Lemma lem2655490 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655491 : term116 = term49.
Proof. exact (MK_COMB (@lem2655490) (@lem2655489)). Qed.
Lemma lem2655492 : term115 = term49.
Proof. exact (TRANS (@lem2655487) (@lem2655491)). Qed.
Lemma lem2655493 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem2655494 : term256 = term251.
Proof. exact (MK_COMB (@lem2655493) (@lem2655492)). Qed.
Lemma lem2655496 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655497 : term251 = term252.
Proof. exact (@lem2655496 term245 term50). Qed.
Lemma lem2655498 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2655499 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2655500 : term254 = term245.
Proof. exact (EQ_MP (@lem2655499) (@lem2655498)). Qed.
Lemma lem2655501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655502 : term255 = term247.
Proof. exact (MK_COMB (@lem2655501) (@lem2655500)). Qed.
Lemma lem2655503 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655504 : term252 = term236.
Proof. exact (MK_COMB (@lem2655503) (@lem2655502)). Qed.
Lemma lem2655505 : term251 = term236.
Proof. exact (TRANS (@lem2655497) (@lem2655504)). Qed.
Lemma lem2655506 : term256 = term236.
Proof. exact (TRANS (@lem2655494) (@lem2655505)). Qed.
Lemma lem2655507 : term236 = term256.
Proof. exact (SYM (@lem2655506)). Qed.
Lemma lem2655508 : term250 = term256.
Proof. exact (TRANS (@lem2655484) (@lem2655507)). Qed.
Lemma lem2655509 : term234 = term257.
Proof. exact (@lem2655435 (@lem2655508)). Qed.
Lemma lem2655510 : term233 = term257.
Proof. exact (TRANS (@lem2655401) (@lem2655509)). Qed.
Lemma lem2655512 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2655513 : term257 = term236.
Proof. exact (@lem2655512 term236). Qed.
Lemma lem2655514 : term233 = term236.
Proof. exact (TRANS (@lem2655510) (@lem2655513)). Qed.
Lemma lem2655515 (n : int) : (term212 n) = term258.
Proof. exact (MK_COMB (@lem2655392 n) (@lem2655514)). Qed.
Lemma lem2655516 (n : int) : (term211 n) = term258.
Proof. exact (TRANS (@lem2655284 n) (@lem2655515 n)). Qed.
Lemma lem2655517 : term258 = term236.
Proof. exact (@lem1982721 term236). Qed.
Lemma lem2655518 (n : int) : (term211 n) = term236.
Proof. exact (TRANS (@lem2655516 n) (@lem2655517)). Qed.
Lemma lem2655519 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2655520 (n : int) : (term259 n) = term260.
Proof. exact (MK_COMB (@lem2655519) (@lem2655518 n)). Qed.
Lemma lem2655521 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2655522 (n : int) : (term210 n) = term261.
Proof. exact (MK_COMB (@lem2655520 n) (@lem2655521)). Qed.
Lemma lem2655523 (m : int) (n : int) (h1 : term364 m n) : term261.
Proof. exact (EQ_MP (@lem2655522 n) (@lem2655283 m n h1)). Qed.
Lemma lem2655525 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2655526 : term261 = term262.
Proof. exact (@lem2655525 term45 term236). Qed.
Lemma lem2655528 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2655529 : term236 = term257.
Proof. exact (@lem2655528 term245). Qed.
Lemma lem2655531 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655532 : term45 = term142.
Proof. exact (@lem2655531 (NUMERAL 0)). Qed.
Lemma lem2655533 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2655534 : term80 = term263.
Proof. exact (MK_COMB (@lem2655533) (@lem2655532)). Qed.
Lemma lem2655535 : term262 = term264.
Proof. exact (MK_COMB (@lem2655534) (@lem2655529)). Qed.
Lemma lem2655536 : term265.
Proof. exact (@lem1980026 term45 term49 term236 term49). Qed.
Lemma lem2655538 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655539 : term183 = term189.
Proof. exact (@lem2655538 (NUMERAL 0) term50). Qed.
Lemma lem2655540 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655541 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655542 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655541 h1) (fun h1 : term189 = True => @lem2655540)). Qed.
Lemma lem2655543 : term189 = True.
Proof. exact (EQ_MP (@lem2655542) (@lem2655540)). Qed.
Lemma lem2655544 : term183 = True.
Proof. exact (TRANS (@lem2655539) (@lem2655543)). Qed.
Lemma lem2655545 : True = term183.
Proof. exact (SYM (@lem2655544)). Qed.
Lemma lem2655546 : term183.
Proof. exact (EQ_MP (@lem2655545) (@lem0)). Qed.
Lemma lem2655547 : term266.
Proof. exact (@lem2655536 (@lem2655546)). Qed.
Lemma lem2655549 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2655550 : term183 = term189.
Proof. exact (@lem2655549 (NUMERAL 0) term50). Qed.
Lemma lem2655551 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2655552 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2655553 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2655552 h1) (fun h1 : term189 = True => @lem2655551)). Qed.
Lemma lem2655554 : term189 = True.
Proof. exact (EQ_MP (@lem2655553) (@lem2655551)). Qed.
Lemma lem2655555 : term183 = True.
Proof. exact (TRANS (@lem2655550) (@lem2655554)). Qed.
Lemma lem2655556 : True = term183.
Proof. exact (SYM (@lem2655555)). Qed.
Lemma lem2655557 : term183.
Proof. exact (EQ_MP (@lem2655556) (@lem0)). Qed.
Lemma lem2655558 : term264 = term267.
Proof. exact (@lem2655547 (@lem2655557)). Qed.
Lemma lem2655560 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655561 : term251 = term252.
Proof. exact (@lem2655560 term245 term50). Qed.
Lemma lem2655562 : term253 = term243.
Proof. exact (@lem996237 term243). Qed.
Lemma lem2655563 : (term253 = term243) = (term254 = term245).
Proof. exact (@lem1007663 term243 (BIT1 0) term243). Qed.
Lemma lem2655564 : term254 = term245.
Proof. exact (EQ_MP (@lem2655563) (@lem2655562)). Qed.
Lemma lem2655565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655566 : term255 = term247.
Proof. exact (MK_COMB (@lem2655565) (@lem2655564)). Qed.
Lemma lem2655567 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655568 : term252 = term236.
Proof. exact (MK_COMB (@lem2655567) (@lem2655566)). Qed.
Lemma lem2655569 : term251 = term236.
Proof. exact (TRANS (@lem2655561) (@lem2655568)). Qed.
Lemma lem2655571 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2655572 : term194 = term45.
Proof. exact (@lem2655571 term50). Qed.
Lemma lem2655573 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2655574 : term268 = term80.
Proof. exact (MK_COMB (@lem2655573) (@lem2655572)). Qed.
Lemma lem2655575 : term267 = term262.
Proof. exact (MK_COMB (@lem2655574) (@lem2655569)). Qed.
Lemma lem2655577 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2655578 : term262 = term271.
Proof. exact (@lem2655577 (NUMERAL 0) term245). Qed.
Lemma lem2655579 : term272 = term243.
Proof. exact (@lem912803). Qed.
Lemma lem2655580 (h1 : term272 = term243) : (term245 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term243 h1). Qed.
Lemma lem2655581 : (term272 = term243) = ((term245 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term272 = term243 => @lem2655580 h1) (fun h1 : (term245 = (NUMERAL 0)) = False => @lem2655579)). Qed.
Lemma lem2655582 : (term245 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2655581) (@lem2655579)). Qed.
Lemma lem2655583 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2655584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2655585 : term273 = (and True).
Proof. exact (MK_COMB (@lem2655584) (@lem2655583)). Qed.
Lemma lem2655586 : term271 = (True /\ False).
Proof. exact (MK_COMB (@lem2655585) (@lem2655582)). Qed.
Lemma lem2655588 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2655589 : term271 = False.
Proof. exact (TRANS (@lem2655586) (@lem2655588)). Qed.
Lemma lem2655590 : term262 = False.
Proof. exact (TRANS (@lem2655578) (@lem2655589)). Qed.
Lemma lem2655591 : term267 = False.
Proof. exact (TRANS (@lem2655575) (@lem2655590)). Qed.
Lemma lem2655592 : term264 = False.
Proof. exact (TRANS (@lem2655558) (@lem2655591)). Qed.
Lemma lem2655593 : term262 = False.
Proof. exact (TRANS (@lem2655535) (@lem2655592)). Qed.
Lemma lem2655594 : term261 = False.
Proof. exact (TRANS (@lem2655526) (@lem2655593)). Qed.
Lemma lem2655595 (m : int) (n : int) (h1 : term364 m n) : False.
Proof. exact (EQ_MP (@lem2655594) (@lem2655523 m n h1)). Qed.
Lemma lem2655596 (m : int) (n : int) (h1 : term349 m n) : False.
Proof. exact (or_elim (@lem2654379 m n h1) (fun h0 : term352 n m => @lem2655125 n m h0) (fun h0 : term364 m n => @lem2655595 m n h0)). Qed.
Lemma lem2655598 (m : int) (n : int) (h1 : term349 m n) : term349 m n.
Proof. exact (h1). Qed.
Lemma lem2655599 (m : int) (n : int) (h1 : term349 m n) : (term349 m n) = False.
Proof. exact (prop_ext (fun h2 : term349 m n => @lem2655596 m n h1) (fun h2 : False => @lem2655598 m n h1)). Qed.
Lemma lem2655600 (m : int) (n : int) (h1 : term349 m n) : False.
Proof. exact (EQ_MP (@lem2655599 m n h1) (@lem2655598 m n h1)). Qed.
Lemma lem2655601 (m : int) (n : int) (h1 : term336 m n) : term336 m n.
Proof. exact (h1). Qed.
Lemma lem2655602 (m : int) (n : int) (h1 : term336 m n) : term349 m n.
Proof. exact (EQ_MP (@lem2654369 m n) (@lem2655601 m n h1)). Qed.
Lemma lem2655603 (m : int) (n : int) (h1 : term336 m n) : (term349 m n) = False.
Proof. exact (prop_ext (fun h2 : term349 m n => @lem2655600 m n h2) (fun h2 : False => @lem2655602 m n h1)). Qed.
Lemma lem2655604 (m : int) (n : int) (h1 : term336 m n) : False.
Proof. exact (EQ_MP (@lem2655603 m n h1) (@lem2655602 m n h1)). Qed.
Lemma lem2655605 (m : int) (n : int) : term365 m n.
Proof. exact (fun h0 : term336 m n => @lem2655604 m n h0). Qed.
Lemma lem2655606 (m : int) (n : int) : term366 m n.
Proof. exact (@lem1386578 (term367 m n)). Qed.
Lemma lem2655609 (m : int) (n : int) : term367 m n.
Proof. exact (@lem2655606 m n (@lem2655605 m n)). Qed.
Lemma lem2655610 (m : int) (n : int) : (term335 m n) = (term330 m n).
Proof. exact (SYM (@lem2654069 m n)). Qed.
Lemma lem2655611 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2655612 (m : int) (n : int) : (term367 m n) = (term320 m n).
Proof. exact (MK_COMB (@lem2655611) (@lem2655610 m n)). Qed.
Lemma lem2655613 (m : int) (n : int) : term320 m n.
Proof. exact (EQ_MP (@lem2655612 m n) (@lem2655609 m n)). Qed.
Lemma lem2655614 (m : int) (n : int) : term321 m n.
Proof. exact (EQ_MP (@lem2653934 m n) (@lem2655613 m n)). Qed.
Lemma lem2655615 (m : int) (n : int) : (term321 m n) = ((term321 m n) = True).
Proof. exact (@lem7 (term321 m n)). Qed.
Lemma lem2655616 (m : int) (n : int) : (term321 m n) = True.
Proof. exact (EQ_MP (@lem2655615 m n) (@lem2655614 m n)). Qed.
Lemma lem2655617 (m : int) (n : int) : True = (term321 m n).
Proof. exact (SYM (@lem2655616 m n)). Qed.
Lemma lem2655618 (m : int) (n : int) : term321 m n.
Proof. exact (EQ_MP (@lem2655617 m n) (@lem0)). Qed.
Lemma lem2655619 (m : int) (n : int) (h1 : term15 n) : term331 m n.
Proof. exact (@lem2655618 m n (@lem2653923 n h1)). Qed.
Lemma lem2655620 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : term10 m n.
Proof. exact (@lem2655619 m n h2 (@lem2653922 n m h1)). Qed.
Lemma lem2655621 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : term11 m n.
Proof. exact (@lem2653933 m n (@lem2655620 m n h1 h2)). Qed.
Lemma lem2655623 (m : int) (n : int) : ((div m n) = term3) = (term4 m n).
Proof. exact (EQ_MP (@lem2651672 m n) (@lem2651671 m n)). Qed.
Lemma lem2655630 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2655631 (m : int) (n : int) : (term368 m n) = (term369 m n).
Proof. exact (MK_COMB (@lem2655630) (@lem2655623 m n)). Qed.
Lemma lem2655632 (m : int) (n : int) : (term369 m n) = (term368 m n).
Proof. exact (SYM (@lem2655631 m n)). Qed.
Lemma lem2655633 (m : int) (n : int) : (term370 m n) = (term371 m n).
Proof. exact (@lem2318604 (term371 m n)). Qed.
Lemma lem2655659 (m : int) (n : int) : (term372 m n) = (term4 m n).
Proof. exact (@lem16933 (term4 m n)). Qed.
Lemma lem2655661 (n : int) (m : int) : (term324 n m) = (term324 n m).
Proof. exact (eq_refl (term324 n m)). Qed.
Lemma lem2655662 (m : int) (n : int) : (term373 m n) = (term374 m n).
Proof. exact (MK_COMB (@lem2655661 n m) (@lem2655659 m n)). Qed.
Lemma lem2655663 (m : int) (n : int) : (term375 m n) = (term373 m n).
Proof. exact (@lem17362 (int_le n m) (term369 m n)). Qed.
Lemma lem2655664 (m : int) (n : int) : (term375 m n) = (term374 m n).
Proof. exact (TRANS (@lem2655663 m n) (@lem2655662 m n)). Qed.
Lemma lem2655666 (n : int) : (term25 n) = (term25 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem2655667 (m : int) (n : int) : (term376 m n) = (term377 m n).
Proof. exact (MK_COMB (@lem2655666 n) (@lem2655664 m n)). Qed.
Lemma lem2655668 (m : int) (n : int) : (term378 m n) = (term376 m n).
Proof. exact (@lem17362 (term15 n) (term379 m n)). Qed.
Lemma lem2655688 (m : int) (n : int) : (term378 m n) = (term377 m n).
Proof. exact (TRANS (@lem2655668 m n) (@lem2655667 m n)). Qed.
Lemma lem2655690 (x : int) (y : int) : (int_lt x y) = (term33 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2655691 (n : int) : (term15 n) = (term34 n).
Proof. exact (@lem2655690 term3 n). Qed.
Lemma lem2655693 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2655694 (n : int) : (term34 n) = (term36 n).
Proof. exact (@lem2655693 term37 n). Qed.
Lemma lem2655696 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2655697 : term40 = term41.
Proof. exact (@lem2655696 term3 term42). Qed.
Lemma lem2655699 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2655700 : term44 = term45.
Proof. exact (@lem2655699 (NUMERAL 0)). Qed.
Lemma lem2655701 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2655702 : term46 = term47.
Proof. exact (MK_COMB (@lem2655701) (@lem2655700)). Qed.
Lemma lem2655704 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2655705 : term48 = term49.
Proof. exact (@lem2655704 term50). Qed.
Lemma lem2655706 : term41 = term51.
Proof. exact (MK_COMB (@lem2655702) (@lem2655705)). Qed.
Lemma lem2655707 : term40 = term51.
Proof. exact (TRANS (@lem2655697) (@lem2655706)). Qed.
Lemma lem2655708 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2655709 : term52 = term53.
Proof. exact (MK_COMB (@lem2655708) (@lem2655707)). Qed.
Lemma lem2655710 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2655711 (n : int) : (term36 n) = (term54 n).
Proof. exact (MK_COMB (@lem2655709) (@lem2655710 n)). Qed.
Lemma lem2655712 (n : int) : (term34 n) = (term54 n).
Proof. exact (TRANS (@lem2655694 n) (@lem2655711 n)). Qed.
Lemma lem2655713 (n : int) : (term15 n) = (term54 n).
Proof. exact (TRANS (@lem2655691 n) (@lem2655712 n)). Qed.
Lemma lem2655716 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2655718 (n : int) (m : int) : (int_le n m) = (term35 n m).
Proof. exact (@lem2655716 n m). Qed.
Lemma lem2655721 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2655722 (n : int) : (n = term3) = ((real_of_int n) = term44).
Proof. exact (@lem2655721 n term3). Qed.
Lemma lem2655726 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2655727 : term44 = term45.
Proof. exact (@lem2655726 (NUMERAL 0)). Qed.
Lemma lem2655728 (n : int) : (term67 n) = (term67 n).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem2655729 (n : int) : ((real_of_int n) = term44) = ((real_of_int n) = term45).
Proof. exact (MK_COMB (@lem2655728 n) (@lem2655727)). Qed.
Lemma lem2655731 (n : int) : (n = term3) = ((real_of_int n) = term45).
Proof. exact (TRANS (@lem2655722 n) (@lem2655729 n)). Qed.
Lemma lem2655734 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2655735 (m : int) : (term22 m) = (term78 m).
Proof. exact (@lem2655734 term3 m). Qed.
Lemma lem2655737 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2655738 : term44 = term45.
Proof. exact (@lem2655737 (NUMERAL 0)). Qed.
Lemma lem2655739 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2655740 : term79 = term80.
Proof. exact (MK_COMB (@lem2655739) (@lem2655738)). Qed.
Lemma lem2655741 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2655742 (m : int) : (term78 m) = (term81 m).
Proof. exact (MK_COMB (@lem2655740) (@lem2655741 m)). Qed.
Lemma lem2655744 (m : int) : (term22 m) = (term81 m).
Proof. exact (TRANS (@lem2655735 m) (@lem2655742 m)). Qed.
Lemma lem2655746 (x : int) (y : int) : (int_lt x y) = (term33 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2655747 (m : int) (n : int) : (term380 m n) = (term381 m n).
Proof. exact (@lem2655746 m (int_abs n)). Qed.
Lemma lem2655749 (x : int) (y : int) : (int_le x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2655750 (m : int) (n : int) : (term381 m n) = (term382 m n).
Proof. exact (@lem2655749 (term59 m) (int_abs n)). Qed.
Lemma lem2655752 (x : int) (y : int) : (term38 x y) = (term39 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2655753 (m : int) : (term60 m) = (term61 m).
Proof. exact (@lem2655752 m term42). Qed.
Lemma lem2655755 (n : nat) : (term43 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2655756 : term48 = term49.
Proof. exact (@lem2655755 term50). Qed.
Lemma lem2655757 (m : int) : (term62 m) = (term62 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem2655758 (m : int) : (term61 m) = (term63 m).
Proof. exact (MK_COMB (@lem2655757 m) (@lem2655756)). Qed.
Lemma lem2655759 (m : int) : (term60 m) = (term63 m).
Proof. exact (TRANS (@lem2655753 m) (@lem2655758 m)). Qed.
Lemma lem2655760 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2655761 (m : int) : (term64 m) = (term65 m).
Proof. exact (MK_COMB (@lem2655760) (@lem2655759 m)). Qed.
Lemma lem2655763 (x : int) : (term383 x) = (term384 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2655764 (n : int) : (term383 n) = (term384 n).
Proof. exact (@lem2655763 n). Qed.
Lemma lem2655765 (m : int) (n : int) : (term382 m n) = (term385 m n).
Proof. exact (MK_COMB (@lem2655761 m) (@lem2655764 n)). Qed.
Lemma lem2655766 (m : int) (n : int) : (term381 m n) = (term385 m n).
Proof. exact (TRANS (@lem2655750 m n) (@lem2655765 m n)). Qed.
Lemma lem2655767 (m : int) (n : int) : (term380 m n) = (term385 m n).
Proof. exact (TRANS (@lem2655747 m n) (@lem2655766 m n)). Qed.
Lemma lem2655768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2655769 (m : int) : (term87 m) = (term88 m).
Proof. exact (MK_COMB (@lem2655768) (@lem2655744 m)). Qed.
Lemma lem2655770 (m : int) (n : int) : (term386 m n) = (term387 m n).
Proof. exact (MK_COMB (@lem2655769 m) (@lem2655767 m n)). Qed.
Lemma lem2655771 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2655772 (n : int) : (term388 n) = (term389 n).
Proof. exact (MK_COMB (@lem2655771) (@lem2655731 n)). Qed.
Lemma lem2655773 (m : int) (n : int) : (term4 m n) = (term390 m n).
Proof. exact (MK_COMB (@lem2655772 n) (@lem2655770 m n)). Qed.
Lemma lem2655774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2655775 (n : int) (m : int) : (term324 n m) = (term333 n m).
Proof. exact (MK_COMB (@lem2655774) (@lem2655718 n m)). Qed.
Lemma lem2655776 (m : int) (n : int) : (term374 m n) = (term391 m n).
Proof. exact (MK_COMB (@lem2655775 n m) (@lem2655773 m n)). Qed.
Lemma lem2655777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2655778 (n : int) : (term25 n) = (term70 n).
Proof. exact (MK_COMB (@lem2655777) (@lem2655713 n)). Qed.
Lemma lem2655779 (m : int) (n : int) : (term377 m n) = (term392 m n).
Proof. exact (MK_COMB (@lem2655778 n) (@lem2655776 m n)). Qed.
Lemma lem2655780 (m : int) (n : int) : (term378 m n) = (term392 m n).
Proof. exact (TRANS (@lem2655688 m n) (@lem2655779 m n)). Qed.
Lemma lem2655784 (t : Prop) : (term95 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2655830 (m : int) (n : int) : (term393 m n) = (term392 m n).
Proof. exact (@lem2655784 (term392 m n)). Qed.
Lemma lem2655831 (n : int) : (term54 n) = (term97 n).
Proof. exact (@lem1988287 (real_of_int n) term51). Qed.
Lemma lem2655838 : term51 = term49.
Proof. exact (@lem1982721 term49). Qed.
Lemma lem2655841 (n : int) : (term98 n) = (term98 n).
Proof. exact (eq_refl (term98 n)). Qed.
Lemma lem2655842 (n : int) : (term99 n) = (term100 n).
Proof. exact (MK_COMB (@lem2655841 n) (@lem2655838)). Qed.
Lemma lem2655843 (n : int) : (term100 n) = (term101 n).
Proof. exact (@lem1982792 (real_of_int n) term49). Qed.
Lemma lem2655845 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655846 : term49 = term103.
Proof. exact (@lem2655845 term50). Qed.
Lemma lem2655848 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2655849 : term106 = term107.
Proof. exact (@lem2655848 term50). Qed.
Lemma lem2655850 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2655851 : term108 = term109.
Proof. exact (MK_COMB (@lem2655850) (@lem2655849)). Qed.
Lemma lem2655852 : term110 = term111.
Proof. exact (MK_COMB (@lem2655851) (@lem2655846)). Qed.
Lemma lem2655853 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2655855 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655856 : term115 = term116.
Proof. exact (@lem2655855 term50 term50). Qed.
Lemma lem2655857 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655858 : term118 = term50.
Proof. exact (EQ_MP (@lem2655857) (@lem940073)). Qed.
Lemma lem2655859 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655860 : term116 = term49.
Proof. exact (MK_COMB (@lem2655859) (@lem2655858)). Qed.
Lemma lem2655861 : term115 = term49.
Proof. exact (TRANS (@lem2655856) (@lem2655860)). Qed.
Lemma lem2655863 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2655864 : term110 = term121.
Proof. exact (@lem2655863 term50 term50). Qed.
Lemma lem2655865 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655866 : term118 = term50.
Proof. exact (EQ_MP (@lem2655865) (@lem940073)). Qed.
Lemma lem2655867 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655868 : term116 = term49.
Proof. exact (MK_COMB (@lem2655867) (@lem2655866)). Qed.
Lemma lem2655869 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2655870 : term121 = term106.
Proof. exact (MK_COMB (@lem2655869) (@lem2655868)). Qed.
Lemma lem2655871 : term110 = term106.
Proof. exact (TRANS (@lem2655864) (@lem2655870)). Qed.
Lemma lem2655872 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2655873 : term122 = term123.
Proof. exact (MK_COMB (@lem2655872) (@lem2655871)). Qed.
Lemma lem2655874 : term112 = term107.
Proof. exact (MK_COMB (@lem2655873) (@lem2655861)). Qed.
Lemma lem2655875 : term111 = term107.
Proof. exact (TRANS (@lem2655853) (@lem2655874)). Qed.
Lemma lem2655876 : term110 = term107.
Proof. exact (TRANS (@lem2655852) (@lem2655875)). Qed.
Lemma lem2655878 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2655879 : term107 = term106.
Proof. exact (@lem2655878 term106). Qed.
Lemma lem2655880 : term110 = term106.
Proof. exact (TRANS (@lem2655876) (@lem2655879)). Qed.
Lemma lem2655881 (n : int) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem2655884 (n : int) : (term101 n) = (term125 n).
Proof. exact (MK_COMB (@lem2655881 n) (@lem2655880)). Qed.
Lemma lem2655885 (n : int) : (term100 n) = (term125 n).
Proof. exact (TRANS (@lem2655843 n) (@lem2655884 n)). Qed.
Lemma lem2655886 (n : int) : (term99 n) = (term125 n).
Proof. exact (TRANS (@lem2655842 n) (@lem2655885 n)). Qed.
Lemma lem2655887 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2655888 (n : int) : (term126 n) = (term127 n).
Proof. exact (MK_COMB (@lem2655887) (@lem2655886 n)). Qed.
Lemma lem2655889 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2655890 (n : int) : (term97 n) = (term128 n).
Proof. exact (MK_COMB (@lem2655888 n) (@lem2655889)). Qed.
Lemma lem2655891 (n : int) : (term54 n) = (term128 n).
Proof. exact (TRANS (@lem2655831 n) (@lem2655890 n)). Qed.
Lemma lem2655892 (m : int) (n : int) : (term35 n m) = (term337 m n).
Proof. exact (@lem1988287 (real_of_int m) (real_of_int n)). Qed.
Lemma lem2655905 (m : int) (n : int) : (term338 m n) = (term339 m n).
Proof. exact (@lem1982792 (real_of_int m) (real_of_int n)). Qed.
Lemma lem2655906 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2655907 (m : int) (n : int) : (term340 m n) = (term341 m n).
Proof. exact (MK_COMB (@lem2655906) (@lem2655905 m n)). Qed.
Lemma lem2655908 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2655909 (m : int) (n : int) : (term337 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem2655907 m n) (@lem2655908)). Qed.
Lemma lem2655910 (m : int) (n : int) : (term35 n m) = (term342 m n).
Proof. exact (TRANS (@lem2655892 m n) (@lem2655909 m n)). Qed.
Lemma lem2655911 (n : int) : ((real_of_int n) = term45) = ((term140 n) = term45).
Proof. exact (@lem1988293 (real_of_int n) term45). Qed.
Lemma lem2655917 (n : int) : (term140 n) = (term141 n).
Proof. exact (@lem1982792 (real_of_int n) term45). Qed.
Lemma lem2655919 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655920 : term45 = term142.
Proof. exact (@lem2655919 (NUMERAL 0)). Qed.
Lemma lem2655922 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2655923 : term106 = term107.
Proof. exact (@lem2655922 term50). Qed.
Lemma lem2655924 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2655925 : term108 = term109.
Proof. exact (MK_COMB (@lem2655924) (@lem2655923)). Qed.
Lemma lem2655926 : term143 = term144.
Proof. exact (MK_COMB (@lem2655925) (@lem2655920)). Qed.
Lemma lem2655927 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2655929 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655930 : term115 = term116.
Proof. exact (@lem2655929 term50 term50). Qed.
Lemma lem2655931 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655932 : term118 = term50.
Proof. exact (EQ_MP (@lem2655931) (@lem940073)). Qed.
Lemma lem2655933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655934 : term116 = term49.
Proof. exact (MK_COMB (@lem2655933) (@lem2655932)). Qed.
Lemma lem2655935 : term115 = term49.
Proof. exact (TRANS (@lem2655930) (@lem2655934)). Qed.
Lemma lem2655937 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2655938 : term143 = term45.
Proof. exact (@lem2655937 term50). Qed.
Lemma lem2655939 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2655940 : term147 = term148.
Proof. exact (MK_COMB (@lem2655939) (@lem2655938)). Qed.
Lemma lem2655941 : term145 = term142.
Proof. exact (MK_COMB (@lem2655940) (@lem2655935)). Qed.
Lemma lem2655942 : term144 = term142.
Proof. exact (TRANS (@lem2655927) (@lem2655941)). Qed.
Lemma lem2655943 : term143 = term142.
Proof. exact (TRANS (@lem2655926) (@lem2655942)). Qed.
Lemma lem2655945 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2655946 : term142 = term45.
Proof. exact (@lem2655945 term45). Qed.
Lemma lem2655947 : term143 = term45.
Proof. exact (TRANS (@lem2655943) (@lem2655946)). Qed.
Lemma lem2655948 (n : int) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem2655949 (n : int) : (term141 n) = (term149 n).
Proof. exact (MK_COMB (@lem2655948 n) (@lem2655947)). Qed.
Lemma lem2655950 (n : int) : (term149 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem2655951 (n : int) : (term141 n) = (real_of_int n).
Proof. exact (TRANS (@lem2655949 n) (@lem2655950 n)). Qed.
Lemma lem2655953 (n : int) : (term140 n) = (real_of_int n).
Proof. exact (TRANS (@lem2655917 n) (@lem2655951 n)). Qed.
Lemma lem2655954 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2655955 (n : int) : (term150 n) = (term67 n).
Proof. exact (MK_COMB (@lem2655954) (@lem2655953 n)). Qed.
Lemma lem2655956 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2655957 (n : int) : ((term140 n) = term45) = ((real_of_int n) = term45).
Proof. exact (MK_COMB (@lem2655955 n) (@lem2655956)). Qed.
Lemma lem2655958 (n : int) : ((real_of_int n) = term45) = ((real_of_int n) = term45).
Proof. exact (TRANS (@lem2655911 n) (@lem2655957 n)). Qed.
Lemma lem2655959 (m : int) : (term81 m) = (term162 m).
Proof. exact (@lem1988287 (real_of_int m) term45). Qed.
Lemma lem2655965 (m : int) : (term140 m) = (term141 m).
Proof. exact (@lem1982792 (real_of_int m) term45). Qed.
Lemma lem2655967 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2655968 : term45 = term142.
Proof. exact (@lem2655967 (NUMERAL 0)). Qed.
Lemma lem2655970 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2655971 : term106 = term107.
Proof. exact (@lem2655970 term50). Qed.
Lemma lem2655972 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2655973 : term108 = term109.
Proof. exact (MK_COMB (@lem2655972) (@lem2655971)). Qed.
Lemma lem2655974 : term143 = term144.
Proof. exact (MK_COMB (@lem2655973) (@lem2655968)). Qed.
Lemma lem2655975 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2655977 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2655978 : term115 = term116.
Proof. exact (@lem2655977 term50 term50). Qed.
Lemma lem2655979 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2655980 : term118 = term50.
Proof. exact (EQ_MP (@lem2655979) (@lem940073)). Qed.
Lemma lem2655981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2655982 : term116 = term49.
Proof. exact (MK_COMB (@lem2655981) (@lem2655980)). Qed.
Lemma lem2655983 : term115 = term49.
Proof. exact (TRANS (@lem2655978) (@lem2655982)). Qed.
Lemma lem2655985 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2655986 : term143 = term45.
Proof. exact (@lem2655985 term50). Qed.
Lemma lem2655987 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2655988 : term147 = term148.
Proof. exact (MK_COMB (@lem2655987) (@lem2655986)). Qed.
Lemma lem2655989 : term145 = term142.
Proof. exact (MK_COMB (@lem2655988) (@lem2655983)). Qed.
Lemma lem2655990 : term144 = term142.
Proof. exact (TRANS (@lem2655975) (@lem2655989)). Qed.
Lemma lem2655991 : term143 = term142.
Proof. exact (TRANS (@lem2655974) (@lem2655990)). Qed.
Lemma lem2655993 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2655994 : term142 = term45.
Proof. exact (@lem2655993 term45). Qed.
Lemma lem2655995 : term143 = term45.
Proof. exact (TRANS (@lem2655991) (@lem2655994)). Qed.
Lemma lem2655996 (m : int) : (term62 m) = (term62 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem2655997 (m : int) : (term141 m) = (term149 m).
Proof. exact (MK_COMB (@lem2655996 m) (@lem2655995)). Qed.
Lemma lem2655998 (m : int) : (term149 m) = (real_of_int m).
Proof. exact (@lem1982723 (real_of_int m)). Qed.
Lemma lem2655999 (m : int) : (term141 m) = (real_of_int m).
Proof. exact (TRANS (@lem2655997 m) (@lem2655998 m)). Qed.
Lemma lem2656001 (m : int) : (term140 m) = (real_of_int m).
Proof. exact (TRANS (@lem2655965 m) (@lem2655999 m)). Qed.
Lemma lem2656002 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656003 (m : int) : (term163 m) = (term164 m).
Proof. exact (MK_COMB (@lem2656002) (@lem2656001 m)). Qed.
Lemma lem2656004 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656005 (m : int) : (term162 m) = (term165 m).
Proof. exact (MK_COMB (@lem2656003 m) (@lem2656004)). Qed.
Lemma lem2656006 (m : int) : (term81 m) = (term165 m).
Proof. exact (TRANS (@lem2655959 m) (@lem2656005 m)). Qed.
Lemma lem2656007 (n : int) (m : int) : (term385 m n) = (term394 n m).
Proof. exact (@lem1988287 (term384 n) (term63 m)). Qed.
Lemma lem2656021 (n : int) (m : int) : (term395 n m) = (term396 n m).
Proof. exact (@lem1982792 (term384 n) (term63 m)). Qed.
Lemma lem2656022 (m : int) : (term132 m) = (term133 m).
Proof. exact (@lem1982781 (real_of_int m) term106 term49). Qed.
Lemma lem2656024 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656025 : term49 = term103.
Proof. exact (@lem2656024 term50). Qed.
Lemma lem2656027 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656028 : term106 = term107.
Proof. exact (@lem2656027 term50). Qed.
Lemma lem2656029 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656030 : term108 = term109.
Proof. exact (MK_COMB (@lem2656029) (@lem2656028)). Qed.
Lemma lem2656031 : term110 = term111.
Proof. exact (MK_COMB (@lem2656030) (@lem2656025)). Qed.
Lemma lem2656032 : term111 = term112.
Proof. exact (@lem1981613 term106 term49 term49 term49). Qed.
Lemma lem2656034 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656035 : term115 = term116.
Proof. exact (@lem2656034 term50 term50). Qed.
Lemma lem2656036 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656037 : term118 = term50.
Proof. exact (EQ_MP (@lem2656036) (@lem940073)). Qed.
Lemma lem2656038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656039 : term116 = term49.
Proof. exact (MK_COMB (@lem2656038) (@lem2656037)). Qed.
Lemma lem2656040 : term115 = term49.
Proof. exact (TRANS (@lem2656035) (@lem2656039)). Qed.
Lemma lem2656042 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2656043 : term110 = term121.
Proof. exact (@lem2656042 term50 term50). Qed.
Lemma lem2656044 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656045 : term118 = term50.
Proof. exact (EQ_MP (@lem2656044) (@lem940073)). Qed.
Lemma lem2656046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656047 : term116 = term49.
Proof. exact (MK_COMB (@lem2656046) (@lem2656045)). Qed.
Lemma lem2656048 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2656049 : term121 = term106.
Proof. exact (MK_COMB (@lem2656048) (@lem2656047)). Qed.
Lemma lem2656050 : term110 = term106.
Proof. exact (TRANS (@lem2656043) (@lem2656049)). Qed.
Lemma lem2656051 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2656052 : term122 = term123.
Proof. exact (MK_COMB (@lem2656051) (@lem2656050)). Qed.
Lemma lem2656053 : term112 = term107.
Proof. exact (MK_COMB (@lem2656052) (@lem2656040)). Qed.
Lemma lem2656054 : term111 = term107.
Proof. exact (TRANS (@lem2656032) (@lem2656053)). Qed.
Lemma lem2656055 : term110 = term107.
Proof. exact (TRANS (@lem2656031) (@lem2656054)). Qed.
Lemma lem2656057 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2656058 : term107 = term106.
Proof. exact (@lem2656057 term106). Qed.
Lemma lem2656059 : term110 = term106.
Proof. exact (TRANS (@lem2656055) (@lem2656058)). Qed.
Lemma lem2656062 (m : int) : (term134 m) = (term134 m).
Proof. exact (eq_refl (term134 m)). Qed.
Lemma lem2656063 (m : int) : (term133 m) = (term135 m).
Proof. exact (MK_COMB (@lem2656062 m) (@lem2656059)). Qed.
Lemma lem2656064 (m : int) : (term132 m) = (term135 m).
Proof. exact (TRANS (@lem2656022 m) (@lem2656063 m)). Qed.
Lemma lem2656065 (n : int) : (term397 n) = (term397 n).
Proof. exact (eq_refl (term397 n)). Qed.
Lemma lem2656068 (n : int) (m : int) : (term396 n m) = (term398 n m).
Proof. exact (MK_COMB (@lem2656065 n) (@lem2656064 m)). Qed.
Lemma lem2656070 (n : int) (m : int) : (term395 n m) = (term398 n m).
Proof. exact (TRANS (@lem2656021 n m) (@lem2656068 n m)). Qed.
Lemma lem2656071 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656072 (n : int) (m : int) : (term399 n m) = (term400 n m).
Proof. exact (MK_COMB (@lem2656071) (@lem2656070 n m)). Qed.
Lemma lem2656073 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656074 (n : int) (m : int) : (term394 n m) = (term401 n m).
Proof. exact (MK_COMB (@lem2656072 n m) (@lem2656073)). Qed.
Lemma lem2656075 (n : int) (m : int) : (term385 m n) = (term401 n m).
Proof. exact (TRANS (@lem2656007 n m) (@lem2656074 n m)). Qed.
Lemma lem2656076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656077 (m : int) : (term88 m) = (term167 m).
Proof. exact (MK_COMB (@lem2656076) (@lem2656006 m)). Qed.
Lemma lem2656078 (n : int) (m : int) : (term387 m n) = (term402 n m).
Proof. exact (MK_COMB (@lem2656077 m) (@lem2656075 n m)). Qed.
Lemma lem2656079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2656080 (n : int) : (term389 n) = (term389 n).
Proof. exact (MK_COMB (@lem2656079) (@lem2655958 n)). Qed.
Lemma lem2656081 (n : int) (m : int) : (term390 m n) = (term403 n m).
Proof. exact (MK_COMB (@lem2656080 n) (@lem2656078 n m)). Qed.
Lemma lem2656082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656083 (m : int) (n : int) : (term333 n m) = (term344 m n).
Proof. exact (MK_COMB (@lem2656082) (@lem2655910 m n)). Qed.
Lemma lem2656084 (n : int) (m : int) : (term391 m n) = (term404 n m).
Proof. exact (MK_COMB (@lem2656083 m n) (@lem2656081 n m)). Qed.
Lemma lem2656085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656086 (n : int) : (term70 n) = (term153 n).
Proof. exact (MK_COMB (@lem2656085) (@lem2655891 n)). Qed.
Lemma lem2656087 (n : int) (m : int) : (term392 m n) = (term405 n m).
Proof. exact (MK_COMB (@lem2656086 n) (@lem2656084 n m)). Qed.
Lemma lem2656094 (n : int) (m : int) : (term393 m n) = (term405 n m).
Proof. exact (TRANS (@lem2655830 m n) (@lem2656087 n m)). Qed.
Lemma lem2656117 (n : int) (m : int) : (term404 n m) = (term406 n m).
Proof. exact (@lem19158 ((real_of_int n) = term45) (term342 m n) (term402 n m)). Qed.
Lemma lem2656120 (n : int) : (term153 n) = (term153 n).
Proof. exact (eq_refl (term153 n)). Qed.
Lemma lem2656121 (n : int) (m : int) : (term405 n m) = (term407 n m).
Proof. exact (MK_COMB (@lem2656120 n) (@lem2656117 n m)). Qed.
Lemma lem2656128 (n : int) (m : int) : (term407 n m) = (term408 n m).
Proof. exact (@lem19158 (term409 m n) (term128 n) (term410 n m)). Qed.
Lemma lem2656129 (n : int) (m : int) : (term405 n m) = (term408 n m).
Proof. exact (TRANS (@lem2656121 n m) (@lem2656128 n m)). Qed.
Lemma lem2656130 (n : int) (m : int) : (term393 m n) = (term408 n m).
Proof. exact (TRANS (@lem2656094 n m) (@lem2656129 n m)). Qed.
Lemma lem2656135 (n : int) (m : int) : (term411 m n) = (term412 n m).
Proof. exact (eq_refl (term411 m n)). Qed.
Lemma lem2656136 (m : int) (n : int) : (term412 n m) = (term411 m n).
Proof. exact (SYM (@lem2656135 n m)). Qed.
Lemma lem2656137 (m : int) (n : int) : (term411 m n) = (term413 m n).
Proof. exact (@lem1482981 (term414 n m) (real_of_int n)). Qed.
Lemma lem2656138 (m : int) (n : int) : (term412 n m) = (term413 m n).
Proof. exact (TRANS (@lem2656136 m n) (@lem2656137 m n)). Qed.
Lemma lem2656139 (n : int) (m : int) : (term415 m n) = (term416 n m).
Proof. exact (eq_refl (term415 m n)). Qed.
Lemma lem2656140 (n : int) : (term417 n) = (term417 n).
Proof. exact (eq_refl (term417 n)). Qed.
Lemma lem2656141 (n : int) (m : int) : (term418 m n) = (term419 n m).
Proof. exact (MK_COMB (@lem2656140 n) (@lem2656139 n m)). Qed.
Lemma lem2656142 (n : int) (m : int) : (term420 m n) = (term421 n m).
Proof. exact (eq_refl (term420 m n)). Qed.
Lemma lem2656143 (n : int) : (term167 n) = (term167 n).
Proof. exact (eq_refl (term167 n)). Qed.
Lemma lem2656144 (n : int) (m : int) : (term422 m n) = (term423 n m).
Proof. exact (MK_COMB (@lem2656143 n) (@lem2656142 n m)). Qed.
Lemma lem2656145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2656146 (n : int) (m : int) : (term424 m n) = (term425 n m).
Proof. exact (MK_COMB (@lem2656145) (@lem2656144 n m)). Qed.
Lemma lem2656147 (n : int) (m : int) : (term413 m n) = (term426 n m).
Proof. exact (MK_COMB (@lem2656146 n m) (@lem2656141 n m)). Qed.
Lemma lem2656148 (n : int) (m : int) : (term427 n m) = (term427 n m).
Proof. exact (eq_refl (term427 n m)). Qed.
Lemma lem2656149 (n : int) (m : int) : ((term412 n m) = (term413 m n)) = ((term412 n m) = (term426 n m)).
Proof. exact (MK_COMB (@lem2656148 n m) (@lem2656147 n m)). Qed.
Lemma lem2656150 (n : int) (m : int) : (term412 n m) = (term426 n m).
Proof. exact (EQ_MP (@lem2656149 n m) (@lem2656138 m n)). Qed.
Lemma lem2656151 (n : int) : (term165 n) = (term162 n).
Proof. exact (@lem1988291 (real_of_int n) term45). Qed.
Lemma lem2656157 (n : int) : (term140 n) = (term141 n).
Proof. exact (@lem1982792 (real_of_int n) term45). Qed.
Lemma lem2656159 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656160 : term45 = term142.
Proof. exact (@lem2656159 (NUMERAL 0)). Qed.
Lemma lem2656162 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656163 : term106 = term107.
Proof. exact (@lem2656162 term50). Qed.
Lemma lem2656164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656165 : term108 = term109.
Proof. exact (MK_COMB (@lem2656164) (@lem2656163)). Qed.
Lemma lem2656166 : term143 = term144.
Proof. exact (MK_COMB (@lem2656165) (@lem2656160)). Qed.
Lemma lem2656167 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2656169 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656170 : term115 = term116.
Proof. exact (@lem2656169 term50 term50). Qed.
Lemma lem2656171 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656172 : term118 = term50.
Proof. exact (EQ_MP (@lem2656171) (@lem940073)). Qed.
Lemma lem2656173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656174 : term116 = term49.
Proof. exact (MK_COMB (@lem2656173) (@lem2656172)). Qed.
Lemma lem2656175 : term115 = term49.
Proof. exact (TRANS (@lem2656170) (@lem2656174)). Qed.
Lemma lem2656177 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2656178 : term143 = term45.
Proof. exact (@lem2656177 term50). Qed.
Lemma lem2656179 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2656180 : term147 = term148.
Proof. exact (MK_COMB (@lem2656179) (@lem2656178)). Qed.
Lemma lem2656181 : term145 = term142.
Proof. exact (MK_COMB (@lem2656180) (@lem2656175)). Qed.
Lemma lem2656182 : term144 = term142.
Proof. exact (TRANS (@lem2656167) (@lem2656181)). Qed.
Lemma lem2656183 : term143 = term142.
Proof. exact (TRANS (@lem2656166) (@lem2656182)). Qed.
Lemma lem2656185 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2656186 : term142 = term45.
Proof. exact (@lem2656185 term45). Qed.
Lemma lem2656187 : term143 = term45.
Proof. exact (TRANS (@lem2656183) (@lem2656186)). Qed.
Lemma lem2656188 (n : int) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem2656189 (n : int) : (term141 n) = (term149 n).
Proof. exact (MK_COMB (@lem2656188 n) (@lem2656187)). Qed.
Lemma lem2656190 (n : int) : (term149 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem2656191 (n : int) : (term141 n) = (real_of_int n).
Proof. exact (TRANS (@lem2656189 n) (@lem2656190 n)). Qed.
Lemma lem2656193 (n : int) : (term140 n) = (real_of_int n).
Proof. exact (TRANS (@lem2656157 n) (@lem2656191 n)). Qed.
Lemma lem2656194 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656195 (n : int) : (term163 n) = (term164 n).
Proof. exact (MK_COMB (@lem2656194) (@lem2656193 n)). Qed.
Lemma lem2656196 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656197 (n : int) : (term162 n) = (term165 n).
Proof. exact (MK_COMB (@lem2656195 n) (@lem2656196)). Qed.
Lemma lem2656198 (n : int) : (term165 n) = (term165 n).
Proof. exact (TRANS (@lem2656151 n) (@lem2656197 n)). Qed.
Lemma lem2656199 (n : int) : (term128 n) = (term428 n).
Proof. exact (@lem1988291 (term125 n) term45). Qed.
Lemma lem2656211 (n : int) : (term429 n) = (term430 n).
Proof. exact (@lem1982792 (term125 n) term45). Qed.
Lemma lem2656213 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656214 : term45 = term142.
Proof. exact (@lem2656213 (NUMERAL 0)). Qed.
Lemma lem2656216 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656217 : term106 = term107.
Proof. exact (@lem2656216 term50). Qed.
Lemma lem2656218 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656219 : term108 = term109.
Proof. exact (MK_COMB (@lem2656218) (@lem2656217)). Qed.
Lemma lem2656220 : term143 = term144.
Proof. exact (MK_COMB (@lem2656219) (@lem2656214)). Qed.
Lemma lem2656221 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2656223 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656224 : term115 = term116.
Proof. exact (@lem2656223 term50 term50). Qed.
Lemma lem2656225 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656226 : term118 = term50.
Proof. exact (EQ_MP (@lem2656225) (@lem940073)). Qed.
Lemma lem2656227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656228 : term116 = term49.
Proof. exact (MK_COMB (@lem2656227) (@lem2656226)). Qed.
Lemma lem2656229 : term115 = term49.
Proof. exact (TRANS (@lem2656224) (@lem2656228)). Qed.
Lemma lem2656231 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2656232 : term143 = term45.
Proof. exact (@lem2656231 term50). Qed.
Lemma lem2656233 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2656234 : term147 = term148.
Proof. exact (MK_COMB (@lem2656233) (@lem2656232)). Qed.
Lemma lem2656235 : term145 = term142.
Proof. exact (MK_COMB (@lem2656234) (@lem2656229)). Qed.
Lemma lem2656236 : term144 = term142.
Proof. exact (TRANS (@lem2656221) (@lem2656235)). Qed.
Lemma lem2656237 : term143 = term142.
Proof. exact (TRANS (@lem2656220) (@lem2656236)). Qed.
Lemma lem2656239 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2656240 : term142 = term45.
Proof. exact (@lem2656239 term45). Qed.
Lemma lem2656241 : term143 = term45.
Proof. exact (TRANS (@lem2656237) (@lem2656240)). Qed.
Lemma lem2656242 (n : int) : (term431 n) = (term431 n).
Proof. exact (eq_refl (term431 n)). Qed.
Lemma lem2656243 (n : int) : (term430 n) = (term432 n).
Proof. exact (MK_COMB (@lem2656242 n) (@lem2656241)). Qed.
Lemma lem2656244 (n : int) : (term432 n) = (term125 n).
Proof. exact (@lem1982723 (term125 n)). Qed.
Lemma lem2656245 (n : int) : (term430 n) = (term125 n).
Proof. exact (TRANS (@lem2656243 n) (@lem2656244 n)). Qed.
Lemma lem2656247 (n : int) : (term429 n) = (term125 n).
Proof. exact (TRANS (@lem2656211 n) (@lem2656245 n)). Qed.
Lemma lem2656248 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656249 (n : int) : (term433 n) = (term127 n).
Proof. exact (MK_COMB (@lem2656248) (@lem2656247 n)). Qed.
Lemma lem2656250 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656251 (n : int) : (term428 n) = (term128 n).
Proof. exact (MK_COMB (@lem2656249 n) (@lem2656250)). Qed.
Lemma lem2656252 (n : int) : (term128 n) = (term128 n).
Proof. exact (TRANS (@lem2656199 n) (@lem2656251 n)). Qed.
Lemma lem2656253 (m : int) (n : int) : (term342 m n) = (term434 m n).
Proof. exact (@lem1988291 (term339 m n) term45). Qed.
Lemma lem2656271 (m : int) (n : int) : (term435 m n) = (term436 m n).
Proof. exact (@lem1982792 (term339 m n) term45). Qed.
Lemma lem2656273 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656274 : term45 = term142.
Proof. exact (@lem2656273 (NUMERAL 0)). Qed.
Lemma lem2656276 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656277 : term106 = term107.
Proof. exact (@lem2656276 term50). Qed.
Lemma lem2656278 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656279 : term108 = term109.
Proof. exact (MK_COMB (@lem2656278) (@lem2656277)). Qed.
Lemma lem2656280 : term143 = term144.
Proof. exact (MK_COMB (@lem2656279) (@lem2656274)). Qed.
Lemma lem2656281 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2656283 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656284 : term115 = term116.
Proof. exact (@lem2656283 term50 term50). Qed.
Lemma lem2656285 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656286 : term118 = term50.
Proof. exact (EQ_MP (@lem2656285) (@lem940073)). Qed.
Lemma lem2656287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656288 : term116 = term49.
Proof. exact (MK_COMB (@lem2656287) (@lem2656286)). Qed.
Lemma lem2656289 : term115 = term49.
Proof. exact (TRANS (@lem2656284) (@lem2656288)). Qed.
Lemma lem2656291 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2656292 : term143 = term45.
Proof. exact (@lem2656291 term50). Qed.
Lemma lem2656293 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2656294 : term147 = term148.
Proof. exact (MK_COMB (@lem2656293) (@lem2656292)). Qed.
Lemma lem2656295 : term145 = term142.
Proof. exact (MK_COMB (@lem2656294) (@lem2656289)). Qed.
Lemma lem2656296 : term144 = term142.
Proof. exact (TRANS (@lem2656281) (@lem2656295)). Qed.
Lemma lem2656297 : term143 = term142.
Proof. exact (TRANS (@lem2656280) (@lem2656296)). Qed.
Lemma lem2656299 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2656300 : term142 = term45.
Proof. exact (@lem2656299 term45). Qed.
Lemma lem2656301 : term143 = term45.
Proof. exact (TRANS (@lem2656297) (@lem2656300)). Qed.
Lemma lem2656302 (m : int) (n : int) : (term437 m n) = (term437 m n).
Proof. exact (eq_refl (term437 m n)). Qed.
Lemma lem2656303 (m : int) (n : int) : (term436 m n) = (term438 m n).
Proof. exact (MK_COMB (@lem2656302 m n) (@lem2656301)). Qed.
Lemma lem2656304 (m : int) (n : int) : (term438 m n) = (term339 m n).
Proof. exact (@lem1982723 (term339 m n)). Qed.
Lemma lem2656305 (m : int) (n : int) : (term436 m n) = (term339 m n).
Proof. exact (TRANS (@lem2656303 m n) (@lem2656304 m n)). Qed.
Lemma lem2656307 (m : int) (n : int) : (term435 m n) = (term339 m n).
Proof. exact (TRANS (@lem2656271 m n) (@lem2656305 m n)). Qed.
Lemma lem2656308 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656309 (m : int) (n : int) : (term439 m n) = (term341 m n).
Proof. exact (MK_COMB (@lem2656308) (@lem2656307 m n)). Qed.
Lemma lem2656310 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656311 (m : int) (n : int) : (term434 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem2656309 m n) (@lem2656310)). Qed.
Lemma lem2656312 (m : int) (n : int) : (term342 m n) = (term342 m n).
Proof. exact (TRANS (@lem2656253 m n) (@lem2656311 m n)). Qed.
Lemma lem2656313 (m : int) : (term165 m) = (term162 m).
Proof. exact (@lem1988291 (real_of_int m) term45). Qed.
Lemma lem2656319 (m : int) : (term140 m) = (term141 m).
Proof. exact (@lem1982792 (real_of_int m) term45). Qed.
Lemma lem2656321 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656322 : term45 = term142.
Proof. exact (@lem2656321 (NUMERAL 0)). Qed.
Lemma lem2656324 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656325 : term106 = term107.
Proof. exact (@lem2656324 term50). Qed.
Lemma lem2656326 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656327 : term108 = term109.
Proof. exact (MK_COMB (@lem2656326) (@lem2656325)). Qed.
Lemma lem2656328 : term143 = term144.
Proof. exact (MK_COMB (@lem2656327) (@lem2656322)). Qed.
Lemma lem2656329 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2656331 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656332 : term115 = term116.
Proof. exact (@lem2656331 term50 term50). Qed.
Lemma lem2656333 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656334 : term118 = term50.
Proof. exact (EQ_MP (@lem2656333) (@lem940073)). Qed.
Lemma lem2656335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656336 : term116 = term49.
Proof. exact (MK_COMB (@lem2656335) (@lem2656334)). Qed.
Lemma lem2656337 : term115 = term49.
Proof. exact (TRANS (@lem2656332) (@lem2656336)). Qed.
Lemma lem2656339 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2656340 : term143 = term45.
Proof. exact (@lem2656339 term50). Qed.
Lemma lem2656341 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2656342 : term147 = term148.
Proof. exact (MK_COMB (@lem2656341) (@lem2656340)). Qed.
Lemma lem2656343 : term145 = term142.
Proof. exact (MK_COMB (@lem2656342) (@lem2656337)). Qed.
Lemma lem2656344 : term144 = term142.
Proof. exact (TRANS (@lem2656329) (@lem2656343)). Qed.
Lemma lem2656345 : term143 = term142.
Proof. exact (TRANS (@lem2656328) (@lem2656344)). Qed.
Lemma lem2656347 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2656348 : term142 = term45.
Proof. exact (@lem2656347 term45). Qed.
Lemma lem2656349 : term143 = term45.
Proof. exact (TRANS (@lem2656345) (@lem2656348)). Qed.
Lemma lem2656350 (m : int) : (term62 m) = (term62 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem2656351 (m : int) : (term141 m) = (term149 m).
Proof. exact (MK_COMB (@lem2656350 m) (@lem2656349)). Qed.
Lemma lem2656352 (m : int) : (term149 m) = (real_of_int m).
Proof. exact (@lem1982723 (real_of_int m)). Qed.
Lemma lem2656353 (m : int) : (term141 m) = (real_of_int m).
Proof. exact (TRANS (@lem2656351 m) (@lem2656352 m)). Qed.
Lemma lem2656355 (m : int) : (term140 m) = (real_of_int m).
Proof. exact (TRANS (@lem2656319 m) (@lem2656353 m)). Qed.
Lemma lem2656356 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656357 (m : int) : (term163 m) = (term164 m).
Proof. exact (MK_COMB (@lem2656356) (@lem2656355 m)). Qed.
Lemma lem2656358 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656359 (m : int) : (term162 m) = (term165 m).
Proof. exact (MK_COMB (@lem2656357 m) (@lem2656358)). Qed.
Lemma lem2656360 (m : int) : (term165 m) = (term165 m).
Proof. exact (TRANS (@lem2656313 m) (@lem2656359 m)). Qed.
Lemma lem2656361 (n : int) (m : int) : (term440 n m) = (term441 n m).
Proof. exact (@lem1988291 (term442 n m) term45). Qed.
Lemma lem2656362 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656385 (m : int) (n : int) : (term442 n m) = (term443 m n).
Proof. exact (@lem1982757 (term158 m) (real_of_int n) term106). Qed.
Lemma lem2656386 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2656387 (m : int) (n : int) : (term444 n m) = (term445 m n).
Proof. exact (MK_COMB (@lem2656386) (@lem2656385 m n)). Qed.
Lemma lem2656388 (m : int) (n : int) : (term446 n m) = (term447 m n).
Proof. exact (MK_COMB (@lem2656387 m n) (@lem2656362)). Qed.
Lemma lem2656389 (m : int) (n : int) : (term447 m n) = (term448 m n).
Proof. exact (@lem1982792 (term443 m n) term45). Qed.
Lemma lem2656391 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656392 : term45 = term142.
Proof. exact (@lem2656391 (NUMERAL 0)). Qed.
Lemma lem2656394 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656395 : term106 = term107.
Proof. exact (@lem2656394 term50). Qed.
Lemma lem2656396 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656397 : term108 = term109.
Proof. exact (MK_COMB (@lem2656396) (@lem2656395)). Qed.
Lemma lem2656398 : term143 = term144.
Proof. exact (MK_COMB (@lem2656397) (@lem2656392)). Qed.
Lemma lem2656399 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2656401 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656402 : term115 = term116.
Proof. exact (@lem2656401 term50 term50). Qed.
Lemma lem2656403 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656404 : term118 = term50.
Proof. exact (EQ_MP (@lem2656403) (@lem940073)). Qed.
Lemma lem2656405 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656406 : term116 = term49.
Proof. exact (MK_COMB (@lem2656405) (@lem2656404)). Qed.
Lemma lem2656407 : term115 = term49.
Proof. exact (TRANS (@lem2656402) (@lem2656406)). Qed.
Lemma lem2656409 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2656410 : term143 = term45.
Proof. exact (@lem2656409 term50). Qed.
Lemma lem2656411 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2656412 : term147 = term148.
Proof. exact (MK_COMB (@lem2656411) (@lem2656410)). Qed.
Lemma lem2656413 : term145 = term142.
Proof. exact (MK_COMB (@lem2656412) (@lem2656407)). Qed.
Lemma lem2656414 : term144 = term142.
Proof. exact (TRANS (@lem2656399) (@lem2656413)). Qed.
Lemma lem2656415 : term143 = term142.
Proof. exact (TRANS (@lem2656398) (@lem2656414)). Qed.
Lemma lem2656417 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2656418 : term142 = term45.
Proof. exact (@lem2656417 term45). Qed.
Lemma lem2656419 : term143 = term45.
Proof. exact (TRANS (@lem2656415) (@lem2656418)). Qed.
Lemma lem2656420 (m : int) (n : int) : (term449 m n) = (term449 m n).
Proof. exact (eq_refl (term449 m n)). Qed.
Lemma lem2656421 (m : int) (n : int) : (term448 m n) = (term450 m n).
Proof. exact (MK_COMB (@lem2656420 m n) (@lem2656419)). Qed.
Lemma lem2656422 (m : int) (n : int) : (term450 m n) = (term443 m n).
Proof. exact (@lem1982723 (term443 m n)). Qed.
Lemma lem2656423 (m : int) (n : int) : (term448 m n) = (term443 m n).
Proof. exact (TRANS (@lem2656421 m n) (@lem2656422 m n)). Qed.
Lemma lem2656424 (m : int) (n : int) : (term447 m n) = (term443 m n).
Proof. exact (TRANS (@lem2656389 m n) (@lem2656423 m n)). Qed.
Lemma lem2656425 (m : int) (n : int) : (term446 n m) = (term443 m n).
Proof. exact (TRANS (@lem2656388 m n) (@lem2656424 m n)). Qed.
Lemma lem2656426 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656427 (m : int) (n : int) : (term451 n m) = (term452 m n).
Proof. exact (MK_COMB (@lem2656426) (@lem2656425 m n)). Qed.
Lemma lem2656428 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656429 (m : int) (n : int) : (term441 n m) = (term453 m n).
Proof. exact (MK_COMB (@lem2656427 m n) (@lem2656428)). Qed.
Lemma lem2656430 (m : int) (n : int) : (term440 n m) = (term453 m n).
Proof. exact (TRANS (@lem2656361 n m) (@lem2656429 m n)). Qed.
Lemma lem2656431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656432 (m : int) : (term167 m) = (term167 m).
Proof. exact (MK_COMB (@lem2656431) (@lem2656360 m)). Qed.
Lemma lem2656433 (m : int) (n : int) : (term454 n m) = (term455 m n).
Proof. exact (MK_COMB (@lem2656432 m) (@lem2656430 m n)). Qed.
Lemma lem2656434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656435 (m : int) (n : int) : (term344 m n) = (term344 m n).
Proof. exact (MK_COMB (@lem2656434) (@lem2656312 m n)). Qed.
Lemma lem2656436 (m : int) (n : int) : (term456 n m) = (term457 m n).
Proof. exact (MK_COMB (@lem2656435 m n) (@lem2656433 m n)). Qed.
Lemma lem2656437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656438 (n : int) : (term153 n) = (term153 n).
Proof. exact (MK_COMB (@lem2656437) (@lem2656252 n)). Qed.
Lemma lem2656439 (m : int) (n : int) : (term421 n m) = (term458 m n).
Proof. exact (MK_COMB (@lem2656438 n) (@lem2656436 m n)). Qed.
Lemma lem2656440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656441 (n : int) : (term167 n) = (term167 n).
Proof. exact (MK_COMB (@lem2656440) (@lem2656198 n)). Qed.
Lemma lem2656442 (m : int) (n : int) : (term423 n m) = (term459 m n).
Proof. exact (MK_COMB (@lem2656441 n) (@lem2656439 m n)). Qed.
Lemma lem2656443 (n : int) : (term460 n) = (term461 n).
Proof. exact (@lem1988289 term45 (real_of_int n)). Qed.
Lemma lem2656449 (n : int) : (term156 n) = (term157 n).
Proof. exact (@lem1982792 term45 (real_of_int n)). Qed.
Lemma lem2656454 (n : int) : (term157 n) = (term158 n).
Proof. exact (@lem1982721 (term158 n)). Qed.
Lemma lem2656456 (n : int) : (term156 n) = (term158 n).
Proof. exact (TRANS (@lem2656449 n) (@lem2656454 n)). Qed.
Lemma lem2656457 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2656458 (n : int) : (term462 n) = (term463 n).
Proof. exact (MK_COMB (@lem2656457) (@lem2656456 n)). Qed.
Lemma lem2656459 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656460 (n : int) : (term461 n) = (term464 n).
Proof. exact (MK_COMB (@lem2656458 n) (@lem2656459)). Qed.
Lemma lem2656461 (n : int) : (term460 n) = (term464 n).
Proof. exact (TRANS (@lem2656443 n) (@lem2656460 n)). Qed.
Lemma lem2656462 (n : int) (m : int) : (term465 n m) = (term466 n m).
Proof. exact (@lem1988291 (term467 n m) term45). Qed.
Lemma lem2656463 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656476 (m : int) : (term135 m) = (term135 m).
Proof. exact (eq_refl (term135 m)). Qed.
Lemma lem2656483 (n : int) : (term468 n) = (term158 n).
Proof. exact (@lem1982785 (real_of_int n)). Qed.
Lemma lem2656484 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2656485 (n : int) : (term469 n) = (term134 n).
Proof. exact (MK_COMB (@lem2656484) (@lem2656483 n)). Qed.
Lemma lem2656486 (n : int) (m : int) : (term467 n m) = (term470 n m).
Proof. exact (MK_COMB (@lem2656485 n) (@lem2656476 m)). Qed.
Lemma lem2656491 (m : int) (n : int) : (term470 n m) = (term470 m n).
Proof. exact (@lem1982757 (term158 m) (term158 n) term106). Qed.
Lemma lem2656492 (m : int) (n : int) : (term467 n m) = (term470 m n).
Proof. exact (TRANS (@lem2656486 n m) (@lem2656491 m n)). Qed.
Lemma lem2656493 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2656494 (m : int) (n : int) : (term471 n m) = (term472 m n).
Proof. exact (MK_COMB (@lem2656493) (@lem2656492 m n)). Qed.
Lemma lem2656495 (m : int) (n : int) : (term473 n m) = (term474 m n).
Proof. exact (MK_COMB (@lem2656494 m n) (@lem2656463)). Qed.
Lemma lem2656496 (m : int) (n : int) : (term474 m n) = (term475 m n).
Proof. exact (@lem1982792 (term470 m n) term45). Qed.
Lemma lem2656498 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656499 : term45 = term142.
Proof. exact (@lem2656498 (NUMERAL 0)). Qed.
Lemma lem2656501 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656502 : term106 = term107.
Proof. exact (@lem2656501 term50). Qed.
Lemma lem2656503 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656504 : term108 = term109.
Proof. exact (MK_COMB (@lem2656503) (@lem2656502)). Qed.
Lemma lem2656505 : term143 = term144.
Proof. exact (MK_COMB (@lem2656504) (@lem2656499)). Qed.
Lemma lem2656506 : term144 = term145.
Proof. exact (@lem1981613 term106 term45 term49 term49). Qed.
Lemma lem2656508 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656509 : term115 = term116.
Proof. exact (@lem2656508 term50 term50). Qed.
Lemma lem2656510 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656511 : term118 = term50.
Proof. exact (EQ_MP (@lem2656510) (@lem940073)). Qed.
Lemma lem2656512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656513 : term116 = term49.
Proof. exact (MK_COMB (@lem2656512) (@lem2656511)). Qed.
Lemma lem2656514 : term115 = term49.
Proof. exact (TRANS (@lem2656509) (@lem2656513)). Qed.
Lemma lem2656516 (x : nat) : (term146 x) = term45.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2656517 : term143 = term45.
Proof. exact (@lem2656516 term50). Qed.
Lemma lem2656518 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2656519 : term147 = term148.
Proof. exact (MK_COMB (@lem2656518) (@lem2656517)). Qed.
Lemma lem2656520 : term145 = term142.
Proof. exact (MK_COMB (@lem2656519) (@lem2656514)). Qed.
Lemma lem2656521 : term144 = term142.
Proof. exact (TRANS (@lem2656506) (@lem2656520)). Qed.
Lemma lem2656522 : term143 = term142.
Proof. exact (TRANS (@lem2656505) (@lem2656521)). Qed.
Lemma lem2656524 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2656525 : term142 = term45.
Proof. exact (@lem2656524 term45). Qed.
Lemma lem2656526 : term143 = term45.
Proof. exact (TRANS (@lem2656522) (@lem2656525)). Qed.
Lemma lem2656527 (m : int) (n : int) : (term476 m n) = (term476 m n).
Proof. exact (eq_refl (term476 m n)). Qed.
Lemma lem2656528 (m : int) (n : int) : (term475 m n) = (term477 m n).
Proof. exact (MK_COMB (@lem2656527 m n) (@lem2656526)). Qed.
Lemma lem2656529 (m : int) (n : int) : (term477 m n) = (term470 m n).
Proof. exact (@lem1982723 (term470 m n)). Qed.
Lemma lem2656530 (m : int) (n : int) : (term475 m n) = (term470 m n).
Proof. exact (TRANS (@lem2656528 m n) (@lem2656529 m n)). Qed.
Lemma lem2656531 (m : int) (n : int) : (term474 m n) = (term470 m n).
Proof. exact (TRANS (@lem2656496 m n) (@lem2656530 m n)). Qed.
Lemma lem2656532 (m : int) (n : int) : (term473 n m) = (term470 m n).
Proof. exact (TRANS (@lem2656495 m n) (@lem2656531 m n)). Qed.
Lemma lem2656533 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656534 (m : int) (n : int) : (term478 n m) = (term479 m n).
Proof. exact (MK_COMB (@lem2656533) (@lem2656532 m n)). Qed.
Lemma lem2656535 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656536 (m : int) (n : int) : (term466 n m) = (term480 m n).
Proof. exact (MK_COMB (@lem2656534 m n) (@lem2656535)). Qed.
Lemma lem2656537 (m : int) (n : int) : (term465 n m) = (term480 m n).
Proof. exact (TRANS (@lem2656462 n m) (@lem2656536 m n)). Qed.
Lemma lem2656538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656539 (m : int) : (term167 m) = (term167 m).
Proof. exact (MK_COMB (@lem2656538) (@lem2656360 m)). Qed.
Lemma lem2656540 (m : int) (n : int) : (term481 n m) = (term482 m n).
Proof. exact (MK_COMB (@lem2656539 m) (@lem2656537 m n)). Qed.
Lemma lem2656541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656542 (m : int) (n : int) : (term344 m n) = (term344 m n).
Proof. exact (MK_COMB (@lem2656541) (@lem2656312 m n)). Qed.
Lemma lem2656543 (m : int) (n : int) : (term483 n m) = (term484 m n).
Proof. exact (MK_COMB (@lem2656542 m n) (@lem2656540 m n)). Qed.
Lemma lem2656544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656545 (n : int) : (term153 n) = (term153 n).
Proof. exact (MK_COMB (@lem2656544) (@lem2656252 n)). Qed.
Lemma lem2656546 (m : int) (n : int) : (term416 n m) = (term485 m n).
Proof. exact (MK_COMB (@lem2656545 n) (@lem2656543 m n)). Qed.
Lemma lem2656547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656548 (n : int) : (term417 n) = (term486 n).
Proof. exact (MK_COMB (@lem2656547) (@lem2656461 n)). Qed.
Lemma lem2656549 (m : int) (n : int) : (term419 n m) = (term487 m n).
Proof. exact (MK_COMB (@lem2656548 n) (@lem2656546 m n)). Qed.
Lemma lem2656550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2656551 (m : int) (n : int) : (term425 n m) = (term488 m n).
Proof. exact (MK_COMB (@lem2656550) (@lem2656442 m n)). Qed.
Lemma lem2656552 (m : int) (n : int) : (term426 n m) = (term489 m n).
Proof. exact (MK_COMB (@lem2656551 m n) (@lem2656549 m n)). Qed.
Lemma lem2656564 (m : int) (n : int) : (term412 n m) = (term489 m n).
Proof. exact (TRANS (@lem2656150 n m) (@lem2656552 m n)). Qed.
Lemma lem2656566 (m : int) (n : int) : (term490 m n) = (term490 m n).
Proof. exact (eq_refl (term490 m n)). Qed.
Lemma lem2656567 (m : int) (n : int) : (term408 n m) = (term491 m n).
Proof. exact (MK_COMB (@lem2656566 m n) (@lem2656564 m n)). Qed.
Lemma lem2656568 (m : int) (n : int) (h1 : term491 m n) : term491 m n.
Proof. exact (h1). Qed.
Lemma lem2656569 (m : int) (n : int) (h1 : term492 m n) : term492 m n.
Proof. exact (h1). Qed.
Lemma lem2656570 (m : int) (n : int) (h1 : term492 m n) : term409 m n.
Proof. exact (proj2 (@lem2656569 m n h1)). Qed.
Lemma lem2656571 (m : int) (n : int) (h1 : term492 m n) : term128 n.
Proof. exact (proj1 (@lem2656569 m n h1)). Qed.
Lemma lem2656572 (m : int) (n : int) (h1 : term492 m n) : (real_of_int n) = term45.
Proof. exact (proj2 (@lem2656570 m n h1)). Qed.
Lemma lem2656575 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2656576 : term182 = term183.
Proof. exact (@lem2656575 term45 term49). Qed.
Lemma lem2656578 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656579 : term49 = term103.
Proof. exact (@lem2656578 term50). Qed.
Lemma lem2656581 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656582 : term45 = term142.
Proof. exact (@lem2656581 (NUMERAL 0)). Qed.
Lemma lem2656583 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2656584 : term184 = term185.
Proof. exact (MK_COMB (@lem2656583) (@lem2656582)). Qed.
Lemma lem2656585 : term183 = term186.
Proof. exact (MK_COMB (@lem2656584) (@lem2656579)). Qed.
Lemma lem2656586 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2656588 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656589 : term183 = term189.
Proof. exact (@lem2656588 (NUMERAL 0) term50). Qed.
Lemma lem2656590 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656591 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656592 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656591 h1) (fun h1 : term189 = True => @lem2656590)). Qed.
Lemma lem2656593 : term189 = True.
Proof. exact (EQ_MP (@lem2656592) (@lem2656590)). Qed.
Lemma lem2656594 : term183 = True.
Proof. exact (TRANS (@lem2656589) (@lem2656593)). Qed.
Lemma lem2656595 : True = term183.
Proof. exact (SYM (@lem2656594)). Qed.
Lemma lem2656596 : term183.
Proof. exact (EQ_MP (@lem2656595) (@lem0)). Qed.
Lemma lem2656597 : term191.
Proof. exact (@lem2656586 (@lem2656596)). Qed.
Lemma lem2656599 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656600 : term183 = term189.
Proof. exact (@lem2656599 (NUMERAL 0) term50). Qed.
Lemma lem2656601 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656602 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656603 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656602 h1) (fun h1 : term189 = True => @lem2656601)). Qed.
Lemma lem2656604 : term189 = True.
Proof. exact (EQ_MP (@lem2656603) (@lem2656601)). Qed.
Lemma lem2656605 : term183 = True.
Proof. exact (TRANS (@lem2656600) (@lem2656604)). Qed.
Lemma lem2656606 : True = term183.
Proof. exact (SYM (@lem2656605)). Qed.
Lemma lem2656607 : term183.
Proof. exact (EQ_MP (@lem2656606) (@lem0)). Qed.
Lemma lem2656608 : term186 = term192.
Proof. exact (@lem2656597 (@lem2656607)). Qed.
Lemma lem2656610 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656611 : term115 = term116.
Proof. exact (@lem2656610 term50 term50). Qed.
Lemma lem2656612 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656613 : term118 = term50.
Proof. exact (EQ_MP (@lem2656612) (@lem940073)). Qed.
Lemma lem2656614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656615 : term116 = term49.
Proof. exact (MK_COMB (@lem2656614) (@lem2656613)). Qed.
Lemma lem2656616 : term115 = term49.
Proof. exact (TRANS (@lem2656611) (@lem2656615)). Qed.
Lemma lem2656618 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2656619 : term194 = term45.
Proof. exact (@lem2656618 term50). Qed.
Lemma lem2656620 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2656621 : term195 = term184.
Proof. exact (MK_COMB (@lem2656620) (@lem2656619)). Qed.
Lemma lem2656622 : term192 = term183.
Proof. exact (MK_COMB (@lem2656621) (@lem2656616)). Qed.
Lemma lem2656624 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656625 : term183 = term189.
Proof. exact (@lem2656624 (NUMERAL 0) term50). Qed.
Lemma lem2656626 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656627 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656628 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656627 h1) (fun h1 : term189 = True => @lem2656626)). Qed.
Lemma lem2656629 : term189 = True.
Proof. exact (EQ_MP (@lem2656628) (@lem2656626)). Qed.
Lemma lem2656630 : term183 = True.
Proof. exact (TRANS (@lem2656625) (@lem2656629)). Qed.
Lemma lem2656631 : term192 = True.
Proof. exact (TRANS (@lem2656622) (@lem2656630)). Qed.
Lemma lem2656632 : term186 = True.
Proof. exact (TRANS (@lem2656608) (@lem2656631)). Qed.
Lemma lem2656633 : term183 = True.
Proof. exact (TRANS (@lem2656585) (@lem2656632)). Qed.
Lemma lem2656634 : term182 = True.
Proof. exact (TRANS (@lem2656576) (@lem2656633)). Qed.
Lemma lem2656635 : True = term182.
Proof. exact (SYM (@lem2656634)). Qed.
Lemma lem2656636 : term182.
Proof. exact (EQ_MP (@lem2656635) (@lem0)). Qed.
Lemma lem2656637 (m : int) (n : int) (h1 : term492 m n) : term196 n.
Proof. exact (conj (@lem2656636) (@lem2656571 m n h1)). Qed.
Lemma lem2656639 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2656640 (n : int) : term198 n.
Proof. exact (@lem2656639 term49 (term125 n)). Qed.
Lemma lem2656641 (m : int) (n : int) (h1 : term492 m n) : term199 n.
Proof. exact (@lem2656640 n (@lem2656637 m n h1)). Qed.
Lemma lem2656642 (n : int) : (term200 n) = (term125 n).
Proof. exact (@lem1982733 (term125 n)). Qed.
Lemma lem2656643 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656644 (n : int) : (term201 n) = (term127 n).
Proof. exact (MK_COMB (@lem2656643) (@lem2656642 n)). Qed.
Lemma lem2656645 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656646 (n : int) : (term199 n) = (term128 n).
Proof. exact (MK_COMB (@lem2656644 n) (@lem2656645)). Qed.
Lemma lem2656647 (m : int) (n : int) (h1 : term492 m n) : term128 n.
Proof. exact (EQ_MP (@lem2656646 n) (@lem2656641 m n h1)). Qed.
Lemma lem2656649 (y : real) : term275 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2656650 (n : int) : term276 n.
Proof. exact (@lem2656649 (real_of_int n)). Qed.
Lemma lem2656651 (m : int) (n : int) (h1 : term492 m n) : term277 n.
Proof. exact (@lem2656650 n (@lem2656572 m n h1)). Qed.
Lemma lem2656652 (m : int) (n : int) (h1 : term492 m n) : term278 n.
Proof. exact (@lem2656651 m n h1 term106). Qed.
Lemma lem2656653 (n : int) : (term278 n) = ((term158 n) = term45).
Proof. exact (eq_refl (term278 n)). Qed.
Lemma lem2656660 (m : int) (n : int) (h1 : term492 m n) : (term158 n) = term45.
Proof. exact (EQ_MP (@lem2656653 n) (@lem2656652 m n h1)). Qed.
Lemma lem2656661 (m : int) (n : int) (h1 : term492 m n) : term279 n.
Proof. exact (conj (@lem2656660 m n h1) (@lem2656647 m n h1)). Qed.
Lemma lem2656663 (x : real) (y : real) : term280 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2656664 (n : int) : term281 n.
Proof. exact (@lem2656663 (term158 n) (term125 n)). Qed.
Lemma lem2656665 (m : int) (n : int) (h1 : term492 m n) : term282 n.
Proof. exact (@lem2656664 n (@lem2656661 m n h1)). Qed.
Lemma lem2656666 (n : int) : (term283 n) = (term284 n).
Proof. exact (@lem1982763 (term158 n) (real_of_int n) term106). Qed.
Lemma lem2656667 (n : int) : (term213 n) = (term214 n).
Proof. exact (@lem1982713 term106 (real_of_int n)). Qed.
Lemma lem2656669 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656670 : term49 = term103.
Proof. exact (@lem2656669 term50). Qed.
Lemma lem2656672 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656673 : term106 = term107.
Proof. exact (@lem2656672 term50). Qed.
Lemma lem2656674 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2656675 : term215 = term216.
Proof. exact (MK_COMB (@lem2656674) (@lem2656673)). Qed.
Lemma lem2656676 : term217 = term218.
Proof. exact (MK_COMB (@lem2656675) (@lem2656670)). Qed.
Lemma lem2656677 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2656679 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656680 : term183 = term189.
Proof. exact (@lem2656679 (NUMERAL 0) term50). Qed.
Lemma lem2656681 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656682 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656683 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656682 h1) (fun h1 : term189 = True => @lem2656681)). Qed.
Lemma lem2656684 : term189 = True.
Proof. exact (EQ_MP (@lem2656683) (@lem2656681)). Qed.
Lemma lem2656685 : term183 = True.
Proof. exact (TRANS (@lem2656680) (@lem2656684)). Qed.
Lemma lem2656686 : True = term183.
Proof. exact (SYM (@lem2656685)). Qed.
Lemma lem2656687 : term183.
Proof. exact (EQ_MP (@lem2656686) (@lem0)). Qed.
Lemma lem2656688 : term220.
Proof. exact (@lem2656677 (@lem2656687)). Qed.
Lemma lem2656690 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656691 : term183 = term189.
Proof. exact (@lem2656690 (NUMERAL 0) term50). Qed.
Lemma lem2656692 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656693 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656694 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656693 h1) (fun h1 : term189 = True => @lem2656692)). Qed.
Lemma lem2656695 : term189 = True.
Proof. exact (EQ_MP (@lem2656694) (@lem2656692)). Qed.
Lemma lem2656696 : term183 = True.
Proof. exact (TRANS (@lem2656691) (@lem2656695)). Qed.
Lemma lem2656697 : True = term183.
Proof. exact (SYM (@lem2656696)). Qed.
Lemma lem2656698 : term183.
Proof. exact (EQ_MP (@lem2656697) (@lem0)). Qed.
Lemma lem2656699 : term221.
Proof. exact (@lem2656688 (@lem2656698)). Qed.
Lemma lem2656701 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656702 : term183 = term189.
Proof. exact (@lem2656701 (NUMERAL 0) term50). Qed.
Lemma lem2656703 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656704 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656705 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656704 h1) (fun h1 : term189 = True => @lem2656703)). Qed.
Lemma lem2656706 : term189 = True.
Proof. exact (EQ_MP (@lem2656705) (@lem2656703)). Qed.
Lemma lem2656707 : term183 = True.
Proof. exact (TRANS (@lem2656702) (@lem2656706)). Qed.
Lemma lem2656708 : True = term183.
Proof. exact (SYM (@lem2656707)). Qed.
Lemma lem2656709 : term183.
Proof. exact (EQ_MP (@lem2656708) (@lem0)). Qed.
Lemma lem2656710 : term222.
Proof. exact (@lem2656699 (@lem2656709)). Qed.
Lemma lem2656712 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656713 : term115 = term116.
Proof. exact (@lem2656712 term50 term50). Qed.
Lemma lem2656714 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656715 : term118 = term50.
Proof. exact (EQ_MP (@lem2656714) (@lem940073)). Qed.
Lemma lem2656716 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656717 : term116 = term49.
Proof. exact (MK_COMB (@lem2656716) (@lem2656715)). Qed.
Lemma lem2656718 : term115 = term49.
Proof. exact (TRANS (@lem2656713) (@lem2656717)). Qed.
Lemma lem2656720 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2656721 : term110 = term121.
Proof. exact (@lem2656720 term50 term50). Qed.
Lemma lem2656722 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656723 : term118 = term50.
Proof. exact (EQ_MP (@lem2656722) (@lem940073)). Qed.
Lemma lem2656724 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656725 : term116 = term49.
Proof. exact (MK_COMB (@lem2656724) (@lem2656723)). Qed.
Lemma lem2656726 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2656727 : term121 = term106.
Proof. exact (MK_COMB (@lem2656726) (@lem2656725)). Qed.
Lemma lem2656728 : term110 = term106.
Proof. exact (TRANS (@lem2656721) (@lem2656727)). Qed.
Lemma lem2656729 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2656730 : term223 = term215.
Proof. exact (MK_COMB (@lem2656729) (@lem2656728)). Qed.
Lemma lem2656731 : term224 = term217.
Proof. exact (MK_COMB (@lem2656730) (@lem2656718)). Qed.
Lemma lem2656733 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2656734 : term217 = term45.
Proof. exact (@lem2656733 term50). Qed.
Lemma lem2656735 : term224 = term45.
Proof. exact (TRANS (@lem2656731) (@lem2656734)). Qed.
Lemma lem2656736 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656737 : term226 = term227.
Proof. exact (MK_COMB (@lem2656736) (@lem2656735)). Qed.
Lemma lem2656738 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2656739 : term228 = term194.
Proof. exact (MK_COMB (@lem2656737) (@lem2656738)). Qed.
Lemma lem2656741 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2656742 : term194 = term45.
Proof. exact (@lem2656741 term50). Qed.
Lemma lem2656743 : term228 = term45.
Proof. exact (TRANS (@lem2656739) (@lem2656742)). Qed.
Lemma lem2656745 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656746 : term115 = term116.
Proof. exact (@lem2656745 term50 term50). Qed.
Lemma lem2656747 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656748 : term118 = term50.
Proof. exact (EQ_MP (@lem2656747) (@lem940073)). Qed.
Lemma lem2656749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656750 : term116 = term49.
Proof. exact (MK_COMB (@lem2656749) (@lem2656748)). Qed.
Lemma lem2656751 : term115 = term49.
Proof. exact (TRANS (@lem2656746) (@lem2656750)). Qed.
Lemma lem2656752 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2656753 : term229 = term194.
Proof. exact (MK_COMB (@lem2656752) (@lem2656751)). Qed.
Lemma lem2656755 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2656756 : term194 = term45.
Proof. exact (@lem2656755 term50). Qed.
Lemma lem2656757 : term229 = term45.
Proof. exact (TRANS (@lem2656753) (@lem2656756)). Qed.
Lemma lem2656758 : term45 = term229.
Proof. exact (SYM (@lem2656757)). Qed.
Lemma lem2656759 : term228 = term229.
Proof. exact (TRANS (@lem2656743) (@lem2656758)). Qed.
Lemma lem2656760 : term218 = term142.
Proof. exact (@lem2656710 (@lem2656759)). Qed.
Lemma lem2656761 : term217 = term142.
Proof. exact (TRANS (@lem2656676) (@lem2656760)). Qed.
Lemma lem2656763 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2656764 : term142 = term45.
Proof. exact (@lem2656763 term45). Qed.
Lemma lem2656765 : term217 = term45.
Proof. exact (TRANS (@lem2656761) (@lem2656764)). Qed.
Lemma lem2656766 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2656767 : term230 = term227.
Proof. exact (MK_COMB (@lem2656766) (@lem2656765)). Qed.
Lemma lem2656768 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2656769 (n : int) : (term214 n) = (term231 n).
Proof. exact (MK_COMB (@lem2656767) (@lem2656768 n)). Qed.
Lemma lem2656770 (n : int) : (term213 n) = (term231 n).
Proof. exact (TRANS (@lem2656667 n) (@lem2656769 n)). Qed.
Lemma lem2656771 (n : int) : (term231 n) = term45.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2656772 (n : int) : (term213 n) = term45.
Proof. exact (TRANS (@lem2656770 n) (@lem2656771 n)). Qed.
Lemma lem2656773 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2656774 (n : int) : (term232 n) = term47.
Proof. exact (MK_COMB (@lem2656773) (@lem2656772 n)). Qed.
Lemma lem2656775 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2656776 (n : int) : (term284 n) = term285.
Proof. exact (MK_COMB (@lem2656774 n) (@lem2656775)). Qed.
Lemma lem2656777 (n : int) : (term283 n) = term285.
Proof. exact (TRANS (@lem2656666 n) (@lem2656776 n)). Qed.
Lemma lem2656778 : term285 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2656779 (n : int) : (term283 n) = term106.
Proof. exact (TRANS (@lem2656777 n) (@lem2656778)). Qed.
Lemma lem2656780 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656781 (n : int) : (term286 n) = term287.
Proof. exact (MK_COMB (@lem2656780) (@lem2656779 n)). Qed.
Lemma lem2656782 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656783 (n : int) : (term282 n) = term288.
Proof. exact (MK_COMB (@lem2656781 n) (@lem2656782)). Qed.
Lemma lem2656784 (m : int) (n : int) (h1 : term492 m n) : term288.
Proof. exact (EQ_MP (@lem2656783 n) (@lem2656665 m n h1)). Qed.
Lemma lem2656786 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2656787 : term288 = term289.
Proof. exact (@lem2656786 term45 term106). Qed.
Lemma lem2656789 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2656790 : term106 = term107.
Proof. exact (@lem2656789 term50). Qed.
Lemma lem2656792 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656793 : term45 = term142.
Proof. exact (@lem2656792 (NUMERAL 0)). Qed.
Lemma lem2656794 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2656795 : term80 = term263.
Proof. exact (MK_COMB (@lem2656794) (@lem2656793)). Qed.
Lemma lem2656796 : term289 = term290.
Proof. exact (MK_COMB (@lem2656795) (@lem2656790)). Qed.
Lemma lem2656797 : term291.
Proof. exact (@lem1980026 term45 term49 term106 term49). Qed.
Lemma lem2656799 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656800 : term183 = term189.
Proof. exact (@lem2656799 (NUMERAL 0) term50). Qed.
Lemma lem2656801 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656802 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656803 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656802 h1) (fun h1 : term189 = True => @lem2656801)). Qed.
Lemma lem2656804 : term189 = True.
Proof. exact (EQ_MP (@lem2656803) (@lem2656801)). Qed.
Lemma lem2656805 : term183 = True.
Proof. exact (TRANS (@lem2656800) (@lem2656804)). Qed.
Lemma lem2656806 : True = term183.
Proof. exact (SYM (@lem2656805)). Qed.
Lemma lem2656807 : term183.
Proof. exact (EQ_MP (@lem2656806) (@lem0)). Qed.
Lemma lem2656808 : term292.
Proof. exact (@lem2656797 (@lem2656807)). Qed.
Lemma lem2656810 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656811 : term183 = term189.
Proof. exact (@lem2656810 (NUMERAL 0) term50). Qed.
Lemma lem2656812 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656813 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656814 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656813 h1) (fun h1 : term189 = True => @lem2656812)). Qed.
Lemma lem2656815 : term189 = True.
Proof. exact (EQ_MP (@lem2656814) (@lem2656812)). Qed.
Lemma lem2656816 : term183 = True.
Proof. exact (TRANS (@lem2656811) (@lem2656815)). Qed.
Lemma lem2656817 : True = term183.
Proof. exact (SYM (@lem2656816)). Qed.
Lemma lem2656818 : term183.
Proof. exact (EQ_MP (@lem2656817) (@lem0)). Qed.
Lemma lem2656819 : term290 = term293.
Proof. exact (@lem2656808 (@lem2656818)). Qed.
Lemma lem2656821 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2656822 : term110 = term121.
Proof. exact (@lem2656821 term50 term50). Qed.
Lemma lem2656823 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656824 : term118 = term50.
Proof. exact (EQ_MP (@lem2656823) (@lem940073)). Qed.
Lemma lem2656825 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656826 : term116 = term49.
Proof. exact (MK_COMB (@lem2656825) (@lem2656824)). Qed.
Lemma lem2656827 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2656828 : term121 = term106.
Proof. exact (MK_COMB (@lem2656827) (@lem2656826)). Qed.
Lemma lem2656829 : term110 = term106.
Proof. exact (TRANS (@lem2656822) (@lem2656828)). Qed.
Lemma lem2656831 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2656832 : term194 = term45.
Proof. exact (@lem2656831 term50). Qed.
Lemma lem2656833 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2656834 : term268 = term80.
Proof. exact (MK_COMB (@lem2656833) (@lem2656832)). Qed.
Lemma lem2656835 : term293 = term289.
Proof. exact (MK_COMB (@lem2656834) (@lem2656829)). Qed.
Lemma lem2656837 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2656838 : term289 = term294.
Proof. exact (@lem2656837 (NUMERAL 0) term50). Qed.
Lemma lem2656839 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656840 (h1 : term190 = (BIT1 0)) : (term50 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2656841 : (term190 = (BIT1 0)) = ((term50 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656840 h1) (fun h1 : (term50 = (NUMERAL 0)) = False => @lem2656839)). Qed.
Lemma lem2656842 : (term50 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2656841) (@lem2656839)). Qed.
Lemma lem2656843 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2656844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2656845 : term273 = (and True).
Proof. exact (MK_COMB (@lem2656844) (@lem2656843)). Qed.
Lemma lem2656846 : term294 = (True /\ False).
Proof. exact (MK_COMB (@lem2656845) (@lem2656842)). Qed.
Lemma lem2656848 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2656849 : term294 = False.
Proof. exact (TRANS (@lem2656846) (@lem2656848)). Qed.
Lemma lem2656850 : term289 = False.
Proof. exact (TRANS (@lem2656838) (@lem2656849)). Qed.
Lemma lem2656851 : term293 = False.
Proof. exact (TRANS (@lem2656835) (@lem2656850)). Qed.
Lemma lem2656852 : term290 = False.
Proof. exact (TRANS (@lem2656819) (@lem2656851)). Qed.
Lemma lem2656853 : term289 = False.
Proof. exact (TRANS (@lem2656796) (@lem2656852)). Qed.
Lemma lem2656854 : term288 = False.
Proof. exact (TRANS (@lem2656787) (@lem2656853)). Qed.
Lemma lem2656855 (m : int) (n : int) (h1 : term492 m n) : False.
Proof. exact (EQ_MP (@lem2656854) (@lem2656784 m n h1)). Qed.
Lemma lem2656856 (m : int) (n : int) (h1 : term489 m n) : term489 m n.
Proof. exact (h1). Qed.
Lemma lem2656857 (m : int) (n : int) (h1 : term459 m n) : term459 m n.
Proof. exact (h1). Qed.
Lemma lem2656858 (m : int) (n : int) (h1 : term459 m n) : term458 m n.
Proof. exact (proj2 (@lem2656857 m n h1)). Qed.
Lemma lem2656860 (m : int) (n : int) (h1 : term459 m n) : term457 m n.
Proof. exact (proj2 (@lem2656858 m n h1)). Qed.
Lemma lem2656862 (m : int) (n : int) (h1 : term459 m n) : term455 m n.
Proof. exact (proj2 (@lem2656860 m n h1)). Qed.
Lemma lem2656863 (m : int) (n : int) (h1 : term459 m n) : term342 m n.
Proof. exact (proj1 (@lem2656860 m n h1)). Qed.
Lemma lem2656864 (m : int) (n : int) (h1 : term459 m n) : term453 m n.
Proof. exact (proj2 (@lem2656862 m n h1)). Qed.
Lemma lem2656867 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2656868 : term182 = term183.
Proof. exact (@lem2656867 term45 term49). Qed.
Lemma lem2656870 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656871 : term49 = term103.
Proof. exact (@lem2656870 term50). Qed.
Lemma lem2656873 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656874 : term45 = term142.
Proof. exact (@lem2656873 (NUMERAL 0)). Qed.
Lemma lem2656875 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2656876 : term184 = term185.
Proof. exact (MK_COMB (@lem2656875) (@lem2656874)). Qed.
Lemma lem2656877 : term183 = term186.
Proof. exact (MK_COMB (@lem2656876) (@lem2656871)). Qed.
Lemma lem2656878 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2656880 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656881 : term183 = term189.
Proof. exact (@lem2656880 (NUMERAL 0) term50). Qed.
Lemma lem2656882 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656883 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656884 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656883 h1) (fun h1 : term189 = True => @lem2656882)). Qed.
Lemma lem2656885 : term189 = True.
Proof. exact (EQ_MP (@lem2656884) (@lem2656882)). Qed.
Lemma lem2656886 : term183 = True.
Proof. exact (TRANS (@lem2656881) (@lem2656885)). Qed.
Lemma lem2656887 : True = term183.
Proof. exact (SYM (@lem2656886)). Qed.
Lemma lem2656888 : term183.
Proof. exact (EQ_MP (@lem2656887) (@lem0)). Qed.
Lemma lem2656889 : term191.
Proof. exact (@lem2656878 (@lem2656888)). Qed.
Lemma lem2656891 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656892 : term183 = term189.
Proof. exact (@lem2656891 (NUMERAL 0) term50). Qed.
Lemma lem2656893 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656894 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656895 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656894 h1) (fun h1 : term189 = True => @lem2656893)). Qed.
Lemma lem2656896 : term189 = True.
Proof. exact (EQ_MP (@lem2656895) (@lem2656893)). Qed.
Lemma lem2656897 : term183 = True.
Proof. exact (TRANS (@lem2656892) (@lem2656896)). Qed.
Lemma lem2656898 : True = term183.
Proof. exact (SYM (@lem2656897)). Qed.
Lemma lem2656899 : term183.
Proof. exact (EQ_MP (@lem2656898) (@lem0)). Qed.
Lemma lem2656900 : term186 = term192.
Proof. exact (@lem2656889 (@lem2656899)). Qed.
Lemma lem2656902 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656903 : term115 = term116.
Proof. exact (@lem2656902 term50 term50). Qed.
Lemma lem2656904 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656905 : term118 = term50.
Proof. exact (EQ_MP (@lem2656904) (@lem940073)). Qed.
Lemma lem2656906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656907 : term116 = term49.
Proof. exact (MK_COMB (@lem2656906) (@lem2656905)). Qed.
Lemma lem2656908 : term115 = term49.
Proof. exact (TRANS (@lem2656903) (@lem2656907)). Qed.
Lemma lem2656910 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2656911 : term194 = term45.
Proof. exact (@lem2656910 term50). Qed.
Lemma lem2656912 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2656913 : term195 = term184.
Proof. exact (MK_COMB (@lem2656912) (@lem2656911)). Qed.
Lemma lem2656914 : term192 = term183.
Proof. exact (MK_COMB (@lem2656913) (@lem2656908)). Qed.
Lemma lem2656916 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656917 : term183 = term189.
Proof. exact (@lem2656916 (NUMERAL 0) term50). Qed.
Lemma lem2656918 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656919 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656920 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656919 h1) (fun h1 : term189 = True => @lem2656918)). Qed.
Lemma lem2656921 : term189 = True.
Proof. exact (EQ_MP (@lem2656920) (@lem2656918)). Qed.
Lemma lem2656922 : term183 = True.
Proof. exact (TRANS (@lem2656917) (@lem2656921)). Qed.
Lemma lem2656923 : term192 = True.
Proof. exact (TRANS (@lem2656914) (@lem2656922)). Qed.
Lemma lem2656924 : term186 = True.
Proof. exact (TRANS (@lem2656900) (@lem2656923)). Qed.
Lemma lem2656925 : term183 = True.
Proof. exact (TRANS (@lem2656877) (@lem2656924)). Qed.
Lemma lem2656926 : term182 = True.
Proof. exact (TRANS (@lem2656868) (@lem2656925)). Qed.
Lemma lem2656927 : True = term182.
Proof. exact (SYM (@lem2656926)). Qed.
Lemma lem2656928 : term182.
Proof. exact (EQ_MP (@lem2656927) (@lem0)). Qed.
Lemma lem2656929 (m : int) (n : int) (h1 : term459 m n) : term353 m n.
Proof. exact (conj (@lem2656928) (@lem2656863 m n h1)). Qed.
Lemma lem2656931 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2656932 (m : int) (n : int) : term354 m n.
Proof. exact (@lem2656931 term49 (term339 m n)). Qed.
Lemma lem2656933 (m : int) (n : int) (h1 : term459 m n) : term355 m n.
Proof. exact (@lem2656932 m n (@lem2656929 m n h1)). Qed.
Lemma lem2656934 (m : int) (n : int) : (term356 m n) = (term339 m n).
Proof. exact (@lem1982733 (term339 m n)). Qed.
Lemma lem2656935 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2656936 (m : int) (n : int) : (term357 m n) = (term341 m n).
Proof. exact (MK_COMB (@lem2656935) (@lem2656934 m n)). Qed.
Lemma lem2656937 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2656938 (m : int) (n : int) : (term355 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem2656936 m n) (@lem2656937)). Qed.
Lemma lem2656939 (m : int) (n : int) (h1 : term459 m n) : term342 m n.
Proof. exact (EQ_MP (@lem2656938 m n) (@lem2656933 m n h1)). Qed.
Lemma lem2656941 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2656942 : term182 = term183.
Proof. exact (@lem2656941 term45 term49). Qed.
Lemma lem2656944 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656945 : term49 = term103.
Proof. exact (@lem2656944 term50). Qed.
Lemma lem2656947 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2656948 : term45 = term142.
Proof. exact (@lem2656947 (NUMERAL 0)). Qed.
Lemma lem2656949 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2656950 : term184 = term185.
Proof. exact (MK_COMB (@lem2656949) (@lem2656948)). Qed.
Lemma lem2656951 : term183 = term186.
Proof. exact (MK_COMB (@lem2656950) (@lem2656945)). Qed.
Lemma lem2656952 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2656954 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656955 : term183 = term189.
Proof. exact (@lem2656954 (NUMERAL 0) term50). Qed.
Lemma lem2656956 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656957 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656958 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656957 h1) (fun h1 : term189 = True => @lem2656956)). Qed.
Lemma lem2656959 : term189 = True.
Proof. exact (EQ_MP (@lem2656958) (@lem2656956)). Qed.
Lemma lem2656960 : term183 = True.
Proof. exact (TRANS (@lem2656955) (@lem2656959)). Qed.
Lemma lem2656961 : True = term183.
Proof. exact (SYM (@lem2656960)). Qed.
Lemma lem2656962 : term183.
Proof. exact (EQ_MP (@lem2656961) (@lem0)). Qed.
Lemma lem2656963 : term191.
Proof. exact (@lem2656952 (@lem2656962)). Qed.
Lemma lem2656965 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656966 : term183 = term189.
Proof. exact (@lem2656965 (NUMERAL 0) term50). Qed.
Lemma lem2656967 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656968 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656969 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656968 h1) (fun h1 : term189 = True => @lem2656967)). Qed.
Lemma lem2656970 : term189 = True.
Proof. exact (EQ_MP (@lem2656969) (@lem2656967)). Qed.
Lemma lem2656971 : term183 = True.
Proof. exact (TRANS (@lem2656966) (@lem2656970)). Qed.
Lemma lem2656972 : True = term183.
Proof. exact (SYM (@lem2656971)). Qed.
Lemma lem2656973 : term183.
Proof. exact (EQ_MP (@lem2656972) (@lem0)). Qed.
Lemma lem2656974 : term186 = term192.
Proof. exact (@lem2656963 (@lem2656973)). Qed.
Lemma lem2656976 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2656977 : term115 = term116.
Proof. exact (@lem2656976 term50 term50). Qed.
Lemma lem2656978 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2656979 : term118 = term50.
Proof. exact (EQ_MP (@lem2656978) (@lem940073)). Qed.
Lemma lem2656980 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2656981 : term116 = term49.
Proof. exact (MK_COMB (@lem2656980) (@lem2656979)). Qed.
Lemma lem2656982 : term115 = term49.
Proof. exact (TRANS (@lem2656977) (@lem2656981)). Qed.
Lemma lem2656984 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2656985 : term194 = term45.
Proof. exact (@lem2656984 term50). Qed.
Lemma lem2656986 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2656987 : term195 = term184.
Proof. exact (MK_COMB (@lem2656986) (@lem2656985)). Qed.
Lemma lem2656988 : term192 = term183.
Proof. exact (MK_COMB (@lem2656987) (@lem2656982)). Qed.
Lemma lem2656990 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2656991 : term183 = term189.
Proof. exact (@lem2656990 (NUMERAL 0) term50). Qed.
Lemma lem2656992 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2656993 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2656994 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2656993 h1) (fun h1 : term189 = True => @lem2656992)). Qed.
Lemma lem2656995 : term189 = True.
Proof. exact (EQ_MP (@lem2656994) (@lem2656992)). Qed.
Lemma lem2656996 : term183 = True.
Proof. exact (TRANS (@lem2656991) (@lem2656995)). Qed.
Lemma lem2656997 : term192 = True.
Proof. exact (TRANS (@lem2656988) (@lem2656996)). Qed.
Lemma lem2656998 : term186 = True.
Proof. exact (TRANS (@lem2656974) (@lem2656997)). Qed.
Lemma lem2656999 : term183 = True.
Proof. exact (TRANS (@lem2656951) (@lem2656998)). Qed.
Lemma lem2657000 : term182 = True.
Proof. exact (TRANS (@lem2656942) (@lem2656999)). Qed.
Lemma lem2657001 : True = term182.
Proof. exact (SYM (@lem2657000)). Qed.
Lemma lem2657002 : term182.
Proof. exact (EQ_MP (@lem2657001) (@lem0)). Qed.
Lemma lem2657003 (m : int) (n : int) (h1 : term459 m n) : term493 m n.
Proof. exact (conj (@lem2657002) (@lem2656864 m n h1)). Qed.
Lemma lem2657005 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2657006 (m : int) (n : int) : term494 m n.
Proof. exact (@lem2657005 term49 (term443 m n)). Qed.
Lemma lem2657007 (m : int) (n : int) (h1 : term459 m n) : term495 m n.
Proof. exact (@lem2657006 m n (@lem2657003 m n h1)). Qed.
Lemma lem2657008 (m : int) (n : int) : (term496 m n) = (term443 m n).
Proof. exact (@lem1982733 (term443 m n)). Qed.
Lemma lem2657009 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2657010 (m : int) (n : int) : (term497 m n) = (term452 m n).
Proof. exact (MK_COMB (@lem2657009) (@lem2657008 m n)). Qed.
Lemma lem2657011 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2657012 (m : int) (n : int) : (term495 m n) = (term453 m n).
Proof. exact (MK_COMB (@lem2657010 m n) (@lem2657011)). Qed.
Lemma lem2657013 (m : int) (n : int) (h1 : term459 m n) : term453 m n.
Proof. exact (EQ_MP (@lem2657012 m n) (@lem2657007 m n h1)). Qed.
Lemma lem2657014 (m : int) (n : int) (h1 : term459 m n) : term498 m n.
Proof. exact (conj (@lem2657013 m n h1) (@lem2656939 m n h1)). Qed.
Lemma lem2657016 (x : real) (y : real) : term208 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2657017 (m : int) (n : int) : term499 m n.
Proof. exact (@lem2657016 (term443 m n) (term339 m n)). Qed.
Lemma lem2657018 (m : int) (n : int) (h1 : term459 m n) : term500 m n.
Proof. exact (@lem2657017 m n (@lem2657014 m n h1)). Qed.
Lemma lem2657019 (m : int) (n : int) : (term501 m n) = (term502 m n).
Proof. exact (@lem1982753 (term158 m) (real_of_int m) (term125 n) (term158 n)). Qed.
Lemma lem2657020 (m : int) : (term213 m) = (term214 m).
Proof. exact (@lem1982713 term106 (real_of_int m)). Qed.
Lemma lem2657022 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657023 : term49 = term103.
Proof. exact (@lem2657022 term50). Qed.
Lemma lem2657025 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2657026 : term106 = term107.
Proof. exact (@lem2657025 term50). Qed.
Lemma lem2657027 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657028 : term215 = term216.
Proof. exact (MK_COMB (@lem2657027) (@lem2657026)). Qed.
Lemma lem2657029 : term217 = term218.
Proof. exact (MK_COMB (@lem2657028) (@lem2657023)). Qed.
Lemma lem2657030 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2657032 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657033 : term183 = term189.
Proof. exact (@lem2657032 (NUMERAL 0) term50). Qed.
Lemma lem2657034 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657035 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657036 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657035 h1) (fun h1 : term189 = True => @lem2657034)). Qed.
Lemma lem2657037 : term189 = True.
Proof. exact (EQ_MP (@lem2657036) (@lem2657034)). Qed.
Lemma lem2657038 : term183 = True.
Proof. exact (TRANS (@lem2657033) (@lem2657037)). Qed.
Lemma lem2657039 : True = term183.
Proof. exact (SYM (@lem2657038)). Qed.
Lemma lem2657040 : term183.
Proof. exact (EQ_MP (@lem2657039) (@lem0)). Qed.
Lemma lem2657041 : term220.
Proof. exact (@lem2657030 (@lem2657040)). Qed.
Lemma lem2657043 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657044 : term183 = term189.
Proof. exact (@lem2657043 (NUMERAL 0) term50). Qed.
Lemma lem2657045 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657046 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657047 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657046 h1) (fun h1 : term189 = True => @lem2657045)). Qed.
Lemma lem2657048 : term189 = True.
Proof. exact (EQ_MP (@lem2657047) (@lem2657045)). Qed.
Lemma lem2657049 : term183 = True.
Proof. exact (TRANS (@lem2657044) (@lem2657048)). Qed.
Lemma lem2657050 : True = term183.
Proof. exact (SYM (@lem2657049)). Qed.
Lemma lem2657051 : term183.
Proof. exact (EQ_MP (@lem2657050) (@lem0)). Qed.
Lemma lem2657052 : term221.
Proof. exact (@lem2657041 (@lem2657051)). Qed.
Lemma lem2657054 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657055 : term183 = term189.
Proof. exact (@lem2657054 (NUMERAL 0) term50). Qed.
Lemma lem2657056 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657057 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657058 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657057 h1) (fun h1 : term189 = True => @lem2657056)). Qed.
Lemma lem2657059 : term189 = True.
Proof. exact (EQ_MP (@lem2657058) (@lem2657056)). Qed.
Lemma lem2657060 : term183 = True.
Proof. exact (TRANS (@lem2657055) (@lem2657059)). Qed.
Lemma lem2657061 : True = term183.
Proof. exact (SYM (@lem2657060)). Qed.
Lemma lem2657062 : term183.
Proof. exact (EQ_MP (@lem2657061) (@lem0)). Qed.
Lemma lem2657063 : term222.
Proof. exact (@lem2657052 (@lem2657062)). Qed.
Lemma lem2657065 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2657066 : term115 = term116.
Proof. exact (@lem2657065 term50 term50). Qed.
Lemma lem2657067 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657068 : term118 = term50.
Proof. exact (EQ_MP (@lem2657067) (@lem940073)). Qed.
Lemma lem2657069 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657070 : term116 = term49.
Proof. exact (MK_COMB (@lem2657069) (@lem2657068)). Qed.
Lemma lem2657071 : term115 = term49.
Proof. exact (TRANS (@lem2657066) (@lem2657070)). Qed.
Lemma lem2657073 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2657074 : term110 = term121.
Proof. exact (@lem2657073 term50 term50). Qed.
Lemma lem2657075 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657076 : term118 = term50.
Proof. exact (EQ_MP (@lem2657075) (@lem940073)). Qed.
Lemma lem2657077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657078 : term116 = term49.
Proof. exact (MK_COMB (@lem2657077) (@lem2657076)). Qed.
Lemma lem2657079 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2657080 : term121 = term106.
Proof. exact (MK_COMB (@lem2657079) (@lem2657078)). Qed.
Lemma lem2657081 : term110 = term106.
Proof. exact (TRANS (@lem2657074) (@lem2657080)). Qed.
Lemma lem2657082 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657083 : term223 = term215.
Proof. exact (MK_COMB (@lem2657082) (@lem2657081)). Qed.
Lemma lem2657084 : term224 = term217.
Proof. exact (MK_COMB (@lem2657083) (@lem2657071)). Qed.
Lemma lem2657086 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2657087 : term217 = term45.
Proof. exact (@lem2657086 term50). Qed.
Lemma lem2657088 : term224 = term45.
Proof. exact (TRANS (@lem2657084) (@lem2657087)). Qed.
Lemma lem2657089 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2657090 : term226 = term227.
Proof. exact (MK_COMB (@lem2657089) (@lem2657088)). Qed.
Lemma lem2657091 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2657092 : term228 = term194.
Proof. exact (MK_COMB (@lem2657090) (@lem2657091)). Qed.
Lemma lem2657094 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657095 : term194 = term45.
Proof. exact (@lem2657094 term50). Qed.
Lemma lem2657096 : term228 = term45.
Proof. exact (TRANS (@lem2657092) (@lem2657095)). Qed.
Lemma lem2657098 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2657099 : term115 = term116.
Proof. exact (@lem2657098 term50 term50). Qed.
Lemma lem2657100 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657101 : term118 = term50.
Proof. exact (EQ_MP (@lem2657100) (@lem940073)). Qed.
Lemma lem2657102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657103 : term116 = term49.
Proof. exact (MK_COMB (@lem2657102) (@lem2657101)). Qed.
Lemma lem2657104 : term115 = term49.
Proof. exact (TRANS (@lem2657099) (@lem2657103)). Qed.
Lemma lem2657105 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2657106 : term229 = term194.
Proof. exact (MK_COMB (@lem2657105) (@lem2657104)). Qed.
Lemma lem2657108 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657109 : term194 = term45.
Proof. exact (@lem2657108 term50). Qed.
Lemma lem2657110 : term229 = term45.
Proof. exact (TRANS (@lem2657106) (@lem2657109)). Qed.
Lemma lem2657111 : term45 = term229.
Proof. exact (SYM (@lem2657110)). Qed.
Lemma lem2657112 : term228 = term229.
Proof. exact (TRANS (@lem2657096) (@lem2657111)). Qed.
Lemma lem2657113 : term218 = term142.
Proof. exact (@lem2657063 (@lem2657112)). Qed.
Lemma lem2657114 : term217 = term142.
Proof. exact (TRANS (@lem2657029) (@lem2657113)). Qed.
Lemma lem2657116 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2657117 : term142 = term45.
Proof. exact (@lem2657116 term45). Qed.
Lemma lem2657118 : term217 = term45.
Proof. exact (TRANS (@lem2657114) (@lem2657117)). Qed.
Lemma lem2657119 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2657120 : term230 = term227.
Proof. exact (MK_COMB (@lem2657119) (@lem2657118)). Qed.
Lemma lem2657121 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2657122 (m : int) : (term214 m) = (term231 m).
Proof. exact (MK_COMB (@lem2657120) (@lem2657121 m)). Qed.
Lemma lem2657123 (m : int) : (term213 m) = (term231 m).
Proof. exact (TRANS (@lem2657020 m) (@lem2657122 m)). Qed.
Lemma lem2657124 (m : int) : (term231 m) = term45.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2657125 (m : int) : (term213 m) = term45.
Proof. exact (TRANS (@lem2657123 m) (@lem2657124 m)). Qed.
Lemma lem2657126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657127 (m : int) : (term232 m) = term47.
Proof. exact (MK_COMB (@lem2657126) (@lem2657125 m)). Qed.
Lemma lem2657128 (n : int) : (term503 n) = (term504 n).
Proof. exact (@lem1982759 (real_of_int n) (term158 n) term106). Qed.
Lemma lem2657129 (n : int) : (term505 n) = (term214 n).
Proof. exact (@lem1982715 term106 (real_of_int n)). Qed.
Lemma lem2657131 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657132 : term49 = term103.
Proof. exact (@lem2657131 term50). Qed.
Lemma lem2657134 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2657135 : term106 = term107.
Proof. exact (@lem2657134 term50). Qed.
Lemma lem2657136 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657137 : term215 = term216.
Proof. exact (MK_COMB (@lem2657136) (@lem2657135)). Qed.
Lemma lem2657138 : term217 = term218.
Proof. exact (MK_COMB (@lem2657137) (@lem2657132)). Qed.
Lemma lem2657139 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2657141 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657142 : term183 = term189.
Proof. exact (@lem2657141 (NUMERAL 0) term50). Qed.
Lemma lem2657143 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657144 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657145 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657144 h1) (fun h1 : term189 = True => @lem2657143)). Qed.
Lemma lem2657146 : term189 = True.
Proof. exact (EQ_MP (@lem2657145) (@lem2657143)). Qed.
Lemma lem2657147 : term183 = True.
Proof. exact (TRANS (@lem2657142) (@lem2657146)). Qed.
Lemma lem2657148 : True = term183.
Proof. exact (SYM (@lem2657147)). Qed.
Lemma lem2657149 : term183.
Proof. exact (EQ_MP (@lem2657148) (@lem0)). Qed.
Lemma lem2657150 : term220.
Proof. exact (@lem2657139 (@lem2657149)). Qed.
Lemma lem2657152 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657153 : term183 = term189.
Proof. exact (@lem2657152 (NUMERAL 0) term50). Qed.
Lemma lem2657154 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657155 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657156 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657155 h1) (fun h1 : term189 = True => @lem2657154)). Qed.
Lemma lem2657157 : term189 = True.
Proof. exact (EQ_MP (@lem2657156) (@lem2657154)). Qed.
Lemma lem2657158 : term183 = True.
Proof. exact (TRANS (@lem2657153) (@lem2657157)). Qed.
Lemma lem2657159 : True = term183.
Proof. exact (SYM (@lem2657158)). Qed.
Lemma lem2657160 : term183.
Proof. exact (EQ_MP (@lem2657159) (@lem0)). Qed.
Lemma lem2657161 : term221.
Proof. exact (@lem2657150 (@lem2657160)). Qed.
Lemma lem2657163 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657164 : term183 = term189.
Proof. exact (@lem2657163 (NUMERAL 0) term50). Qed.
Lemma lem2657165 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657166 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657167 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657166 h1) (fun h1 : term189 = True => @lem2657165)). Qed.
Lemma lem2657168 : term189 = True.
Proof. exact (EQ_MP (@lem2657167) (@lem2657165)). Qed.
Lemma lem2657169 : term183 = True.
Proof. exact (TRANS (@lem2657164) (@lem2657168)). Qed.
Lemma lem2657170 : True = term183.
Proof. exact (SYM (@lem2657169)). Qed.
Lemma lem2657171 : term183.
Proof. exact (EQ_MP (@lem2657170) (@lem0)). Qed.
Lemma lem2657172 : term222.
Proof. exact (@lem2657161 (@lem2657171)). Qed.
Lemma lem2657174 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2657175 : term115 = term116.
Proof. exact (@lem2657174 term50 term50). Qed.
Lemma lem2657176 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657177 : term118 = term50.
Proof. exact (EQ_MP (@lem2657176) (@lem940073)). Qed.
Lemma lem2657178 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657179 : term116 = term49.
Proof. exact (MK_COMB (@lem2657178) (@lem2657177)). Qed.
Lemma lem2657180 : term115 = term49.
Proof. exact (TRANS (@lem2657175) (@lem2657179)). Qed.
Lemma lem2657182 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2657183 : term110 = term121.
Proof. exact (@lem2657182 term50 term50). Qed.
Lemma lem2657184 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657185 : term118 = term50.
Proof. exact (EQ_MP (@lem2657184) (@lem940073)). Qed.
Lemma lem2657186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657187 : term116 = term49.
Proof. exact (MK_COMB (@lem2657186) (@lem2657185)). Qed.
Lemma lem2657188 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2657189 : term121 = term106.
Proof. exact (MK_COMB (@lem2657188) (@lem2657187)). Qed.
Lemma lem2657190 : term110 = term106.
Proof. exact (TRANS (@lem2657183) (@lem2657189)). Qed.
Lemma lem2657191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657192 : term223 = term215.
Proof. exact (MK_COMB (@lem2657191) (@lem2657190)). Qed.
Lemma lem2657193 : term224 = term217.
Proof. exact (MK_COMB (@lem2657192) (@lem2657180)). Qed.
Lemma lem2657195 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2657196 : term217 = term45.
Proof. exact (@lem2657195 term50). Qed.
Lemma lem2657197 : term224 = term45.
Proof. exact (TRANS (@lem2657193) (@lem2657196)). Qed.
Lemma lem2657198 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2657199 : term226 = term227.
Proof. exact (MK_COMB (@lem2657198) (@lem2657197)). Qed.
Lemma lem2657200 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2657201 : term228 = term194.
Proof. exact (MK_COMB (@lem2657199) (@lem2657200)). Qed.
Lemma lem2657203 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657204 : term194 = term45.
Proof. exact (@lem2657203 term50). Qed.
Lemma lem2657205 : term228 = term45.
Proof. exact (TRANS (@lem2657201) (@lem2657204)). Qed.
Lemma lem2657207 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2657208 : term115 = term116.
Proof. exact (@lem2657207 term50 term50). Qed.
Lemma lem2657209 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657210 : term118 = term50.
Proof. exact (EQ_MP (@lem2657209) (@lem940073)). Qed.
Lemma lem2657211 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657212 : term116 = term49.
Proof. exact (MK_COMB (@lem2657211) (@lem2657210)). Qed.
Lemma lem2657213 : term115 = term49.
Proof. exact (TRANS (@lem2657208) (@lem2657212)). Qed.
Lemma lem2657214 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2657215 : term229 = term194.
Proof. exact (MK_COMB (@lem2657214) (@lem2657213)). Qed.
Lemma lem2657217 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657218 : term194 = term45.
Proof. exact (@lem2657217 term50). Qed.
Lemma lem2657219 : term229 = term45.
Proof. exact (TRANS (@lem2657215) (@lem2657218)). Qed.
Lemma lem2657220 : term45 = term229.
Proof. exact (SYM (@lem2657219)). Qed.
Lemma lem2657221 : term228 = term229.
Proof. exact (TRANS (@lem2657205) (@lem2657220)). Qed.
Lemma lem2657222 : term218 = term142.
Proof. exact (@lem2657172 (@lem2657221)). Qed.
Lemma lem2657223 : term217 = term142.
Proof. exact (TRANS (@lem2657138) (@lem2657222)). Qed.
Lemma lem2657225 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2657226 : term142 = term45.
Proof. exact (@lem2657225 term45). Qed.
Lemma lem2657227 : term217 = term45.
Proof. exact (TRANS (@lem2657223) (@lem2657226)). Qed.
Lemma lem2657228 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2657229 : term230 = term227.
Proof. exact (MK_COMB (@lem2657228) (@lem2657227)). Qed.
Lemma lem2657230 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2657231 (n : int) : (term214 n) = (term231 n).
Proof. exact (MK_COMB (@lem2657229) (@lem2657230 n)). Qed.
Lemma lem2657232 (n : int) : (term505 n) = (term231 n).
Proof. exact (TRANS (@lem2657129 n) (@lem2657231 n)). Qed.
Lemma lem2657233 (n : int) : (term231 n) = term45.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2657234 (n : int) : (term505 n) = term45.
Proof. exact (TRANS (@lem2657232 n) (@lem2657233 n)). Qed.
Lemma lem2657235 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657236 (n : int) : (term506 n) = term47.
Proof. exact (MK_COMB (@lem2657235) (@lem2657234 n)). Qed.
Lemma lem2657237 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2657238 (n : int) : (term504 n) = term285.
Proof. exact (MK_COMB (@lem2657236 n) (@lem2657237)). Qed.
Lemma lem2657239 (n : int) : (term503 n) = term285.
Proof. exact (TRANS (@lem2657128 n) (@lem2657238 n)). Qed.
Lemma lem2657240 : term285 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2657241 (n : int) : (term503 n) = term106.
Proof. exact (TRANS (@lem2657239 n) (@lem2657240)). Qed.
Lemma lem2657242 (m : int) (n : int) : (term502 m n) = term285.
Proof. exact (MK_COMB (@lem2657127 m) (@lem2657241 n)). Qed.
Lemma lem2657243 (m : int) (n : int) : (term501 m n) = term285.
Proof. exact (TRANS (@lem2657019 m n) (@lem2657242 m n)). Qed.
Lemma lem2657244 : term285 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2657245 (m : int) (n : int) : (term501 m n) = term106.
Proof. exact (TRANS (@lem2657243 m n) (@lem2657244)). Qed.
Lemma lem2657246 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2657247 (m : int) (n : int) : (term507 m n) = term287.
Proof. exact (MK_COMB (@lem2657246) (@lem2657245 m n)). Qed.
Lemma lem2657248 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2657249 (m : int) (n : int) : (term500 m n) = term288.
Proof. exact (MK_COMB (@lem2657247 m n) (@lem2657248)). Qed.
Lemma lem2657250 (m : int) (n : int) (h1 : term459 m n) : term288.
Proof. exact (EQ_MP (@lem2657249 m n) (@lem2657018 m n h1)). Qed.
Lemma lem2657252 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2657253 : term288 = term289.
Proof. exact (@lem2657252 term45 term106). Qed.
Lemma lem2657255 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2657256 : term106 = term107.
Proof. exact (@lem2657255 term50). Qed.
Lemma lem2657258 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657259 : term45 = term142.
Proof. exact (@lem2657258 (NUMERAL 0)). Qed.
Lemma lem2657260 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2657261 : term80 = term263.
Proof. exact (MK_COMB (@lem2657260) (@lem2657259)). Qed.
Lemma lem2657262 : term289 = term290.
Proof. exact (MK_COMB (@lem2657261) (@lem2657256)). Qed.
Lemma lem2657263 : term291.
Proof. exact (@lem1980026 term45 term49 term106 term49). Qed.
Lemma lem2657265 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657266 : term183 = term189.
Proof. exact (@lem2657265 (NUMERAL 0) term50). Qed.
Lemma lem2657267 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657268 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657269 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657268 h1) (fun h1 : term189 = True => @lem2657267)). Qed.
Lemma lem2657270 : term189 = True.
Proof. exact (EQ_MP (@lem2657269) (@lem2657267)). Qed.
Lemma lem2657271 : term183 = True.
Proof. exact (TRANS (@lem2657266) (@lem2657270)). Qed.
Lemma lem2657272 : True = term183.
Proof. exact (SYM (@lem2657271)). Qed.
Lemma lem2657273 : term183.
Proof. exact (EQ_MP (@lem2657272) (@lem0)). Qed.
Lemma lem2657274 : term292.
Proof. exact (@lem2657263 (@lem2657273)). Qed.
Lemma lem2657276 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657277 : term183 = term189.
Proof. exact (@lem2657276 (NUMERAL 0) term50). Qed.
Lemma lem2657278 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657279 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657280 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657279 h1) (fun h1 : term189 = True => @lem2657278)). Qed.
Lemma lem2657281 : term189 = True.
Proof. exact (EQ_MP (@lem2657280) (@lem2657278)). Qed.
Lemma lem2657282 : term183 = True.
Proof. exact (TRANS (@lem2657277) (@lem2657281)). Qed.
Lemma lem2657283 : True = term183.
Proof. exact (SYM (@lem2657282)). Qed.
Lemma lem2657284 : term183.
Proof. exact (EQ_MP (@lem2657283) (@lem0)). Qed.
Lemma lem2657285 : term290 = term293.
Proof. exact (@lem2657274 (@lem2657284)). Qed.
Lemma lem2657287 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2657288 : term110 = term121.
Proof. exact (@lem2657287 term50 term50). Qed.
Lemma lem2657289 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657290 : term118 = term50.
Proof. exact (EQ_MP (@lem2657289) (@lem940073)). Qed.
Lemma lem2657291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657292 : term116 = term49.
Proof. exact (MK_COMB (@lem2657291) (@lem2657290)). Qed.
Lemma lem2657293 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2657294 : term121 = term106.
Proof. exact (MK_COMB (@lem2657293) (@lem2657292)). Qed.
Lemma lem2657295 : term110 = term106.
Proof. exact (TRANS (@lem2657288) (@lem2657294)). Qed.
Lemma lem2657297 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657298 : term194 = term45.
Proof. exact (@lem2657297 term50). Qed.
Lemma lem2657299 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2657300 : term268 = term80.
Proof. exact (MK_COMB (@lem2657299) (@lem2657298)). Qed.
Lemma lem2657301 : term293 = term289.
Proof. exact (MK_COMB (@lem2657300) (@lem2657295)). Qed.
Lemma lem2657303 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2657304 : term289 = term294.
Proof. exact (@lem2657303 (NUMERAL 0) term50). Qed.
Lemma lem2657305 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657306 (h1 : term190 = (BIT1 0)) : (term50 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2657307 : (term190 = (BIT1 0)) = ((term50 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657306 h1) (fun h1 : (term50 = (NUMERAL 0)) = False => @lem2657305)). Qed.
Lemma lem2657308 : (term50 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2657307) (@lem2657305)). Qed.
Lemma lem2657309 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2657310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2657311 : term273 = (and True).
Proof. exact (MK_COMB (@lem2657310) (@lem2657309)). Qed.
Lemma lem2657312 : term294 = (True /\ False).
Proof. exact (MK_COMB (@lem2657311) (@lem2657308)). Qed.
Lemma lem2657314 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2657315 : term294 = False.
Proof. exact (TRANS (@lem2657312) (@lem2657314)). Qed.
Lemma lem2657316 : term289 = False.
Proof. exact (TRANS (@lem2657304) (@lem2657315)). Qed.
Lemma lem2657317 : term293 = False.
Proof. exact (TRANS (@lem2657301) (@lem2657316)). Qed.
Lemma lem2657318 : term290 = False.
Proof. exact (TRANS (@lem2657285) (@lem2657317)). Qed.
Lemma lem2657319 : term289 = False.
Proof. exact (TRANS (@lem2657262) (@lem2657318)). Qed.
Lemma lem2657320 : term288 = False.
Proof. exact (TRANS (@lem2657253) (@lem2657319)). Qed.
Lemma lem2657321 (m : int) (n : int) (h1 : term459 m n) : False.
Proof. exact (EQ_MP (@lem2657320) (@lem2657250 m n h1)). Qed.
Lemma lem2657322 (m : int) (n : int) (h1 : term487 m n) : term487 m n.
Proof. exact (h1). Qed.
Lemma lem2657323 (m : int) (n : int) (h1 : term487 m n) : term485 m n.
Proof. exact (proj2 (@lem2657322 m n h1)). Qed.
Lemma lem2657324 (m : int) (n : int) (h1 : term487 m n) : term464 n.
Proof. exact (proj1 (@lem2657322 m n h1)). Qed.
Lemma lem2657326 (m : int) (n : int) (h1 : term487 m n) : term128 n.
Proof. exact (proj1 (@lem2657323 m n h1)). Qed.
Lemma lem2657332 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2657333 : term182 = term183.
Proof. exact (@lem2657332 term45 term49). Qed.
Lemma lem2657335 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657336 : term49 = term103.
Proof. exact (@lem2657335 term50). Qed.
Lemma lem2657338 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657339 : term45 = term142.
Proof. exact (@lem2657338 (NUMERAL 0)). Qed.
Lemma lem2657340 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2657341 : term184 = term185.
Proof. exact (MK_COMB (@lem2657340) (@lem2657339)). Qed.
Lemma lem2657342 : term183 = term186.
Proof. exact (MK_COMB (@lem2657341) (@lem2657336)). Qed.
Lemma lem2657343 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2657345 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657346 : term183 = term189.
Proof. exact (@lem2657345 (NUMERAL 0) term50). Qed.
Lemma lem2657347 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657348 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657349 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657348 h1) (fun h1 : term189 = True => @lem2657347)). Qed.
Lemma lem2657350 : term189 = True.
Proof. exact (EQ_MP (@lem2657349) (@lem2657347)). Qed.
Lemma lem2657351 : term183 = True.
Proof. exact (TRANS (@lem2657346) (@lem2657350)). Qed.
Lemma lem2657352 : True = term183.
Proof. exact (SYM (@lem2657351)). Qed.
Lemma lem2657353 : term183.
Proof. exact (EQ_MP (@lem2657352) (@lem0)). Qed.
Lemma lem2657354 : term191.
Proof. exact (@lem2657343 (@lem2657353)). Qed.
Lemma lem2657356 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657357 : term183 = term189.
Proof. exact (@lem2657356 (NUMERAL 0) term50). Qed.
Lemma lem2657358 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657359 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657360 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657359 h1) (fun h1 : term189 = True => @lem2657358)). Qed.
Lemma lem2657361 : term189 = True.
Proof. exact (EQ_MP (@lem2657360) (@lem2657358)). Qed.
Lemma lem2657362 : term183 = True.
Proof. exact (TRANS (@lem2657357) (@lem2657361)). Qed.
Lemma lem2657363 : True = term183.
Proof. exact (SYM (@lem2657362)). Qed.
Lemma lem2657364 : term183.
Proof. exact (EQ_MP (@lem2657363) (@lem0)). Qed.
Lemma lem2657365 : term186 = term192.
Proof. exact (@lem2657354 (@lem2657364)). Qed.
Lemma lem2657367 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2657368 : term115 = term116.
Proof. exact (@lem2657367 term50 term50). Qed.
Lemma lem2657369 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657370 : term118 = term50.
Proof. exact (EQ_MP (@lem2657369) (@lem940073)). Qed.
Lemma lem2657371 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657372 : term116 = term49.
Proof. exact (MK_COMB (@lem2657371) (@lem2657370)). Qed.
Lemma lem2657373 : term115 = term49.
Proof. exact (TRANS (@lem2657368) (@lem2657372)). Qed.
Lemma lem2657375 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657376 : term194 = term45.
Proof. exact (@lem2657375 term50). Qed.
Lemma lem2657377 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2657378 : term195 = term184.
Proof. exact (MK_COMB (@lem2657377) (@lem2657376)). Qed.
Lemma lem2657379 : term192 = term183.
Proof. exact (MK_COMB (@lem2657378) (@lem2657373)). Qed.
Lemma lem2657381 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657382 : term183 = term189.
Proof. exact (@lem2657381 (NUMERAL 0) term50). Qed.
Lemma lem2657383 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657384 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657385 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657384 h1) (fun h1 : term189 = True => @lem2657383)). Qed.
Lemma lem2657386 : term189 = True.
Proof. exact (EQ_MP (@lem2657385) (@lem2657383)). Qed.
Lemma lem2657387 : term183 = True.
Proof. exact (TRANS (@lem2657382) (@lem2657386)). Qed.
Lemma lem2657388 : term192 = True.
Proof. exact (TRANS (@lem2657379) (@lem2657387)). Qed.
Lemma lem2657389 : term186 = True.
Proof. exact (TRANS (@lem2657365) (@lem2657388)). Qed.
Lemma lem2657390 : term183 = True.
Proof. exact (TRANS (@lem2657342) (@lem2657389)). Qed.
Lemma lem2657391 : term182 = True.
Proof. exact (TRANS (@lem2657333) (@lem2657390)). Qed.
Lemma lem2657392 : True = term182.
Proof. exact (SYM (@lem2657391)). Qed.
Lemma lem2657393 : term182.
Proof. exact (EQ_MP (@lem2657392) (@lem0)). Qed.
Lemma lem2657394 (m : int) (n : int) (h1 : term487 m n) : term196 n.
Proof. exact (conj (@lem2657393) (@lem2657326 m n h1)). Qed.
Lemma lem2657396 (x : real) (y : real) : term197 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2657397 (n : int) : term198 n.
Proof. exact (@lem2657396 term49 (term125 n)). Qed.
Lemma lem2657398 (m : int) (n : int) (h1 : term487 m n) : term199 n.
Proof. exact (@lem2657397 n (@lem2657394 m n h1)). Qed.
Lemma lem2657399 (n : int) : (term200 n) = (term125 n).
Proof. exact (@lem1982733 (term125 n)). Qed.
Lemma lem2657400 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2657401 (n : int) : (term201 n) = (term127 n).
Proof. exact (MK_COMB (@lem2657400) (@lem2657399 n)). Qed.
Lemma lem2657402 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2657403 (n : int) : (term199 n) = (term128 n).
Proof. exact (MK_COMB (@lem2657401 n) (@lem2657402)). Qed.
Lemma lem2657404 (m : int) (n : int) (h1 : term487 m n) : term128 n.
Proof. exact (EQ_MP (@lem2657403 n) (@lem2657398 m n h1)). Qed.
Lemma lem2657406 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2657407 : term182 = term183.
Proof. exact (@lem2657406 term45 term49). Qed.
Lemma lem2657409 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657410 : term49 = term103.
Proof. exact (@lem2657409 term50). Qed.
Lemma lem2657412 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657413 : term45 = term142.
Proof. exact (@lem2657412 (NUMERAL 0)). Qed.
Lemma lem2657414 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2657415 : term184 = term185.
Proof. exact (MK_COMB (@lem2657414) (@lem2657413)). Qed.
Lemma lem2657416 : term183 = term186.
Proof. exact (MK_COMB (@lem2657415) (@lem2657410)). Qed.
Lemma lem2657417 : term187.
Proof. exact (@lem1980255 term45 term49 term49 term49). Qed.
Lemma lem2657419 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657420 : term183 = term189.
Proof. exact (@lem2657419 (NUMERAL 0) term50). Qed.
Lemma lem2657421 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657422 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657423 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657422 h1) (fun h1 : term189 = True => @lem2657421)). Qed.
Lemma lem2657424 : term189 = True.
Proof. exact (EQ_MP (@lem2657423) (@lem2657421)). Qed.
Lemma lem2657425 : term183 = True.
Proof. exact (TRANS (@lem2657420) (@lem2657424)). Qed.
Lemma lem2657426 : True = term183.
Proof. exact (SYM (@lem2657425)). Qed.
Lemma lem2657427 : term183.
Proof. exact (EQ_MP (@lem2657426) (@lem0)). Qed.
Lemma lem2657428 : term191.
Proof. exact (@lem2657417 (@lem2657427)). Qed.
Lemma lem2657430 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657431 : term183 = term189.
Proof. exact (@lem2657430 (NUMERAL 0) term50). Qed.
Lemma lem2657432 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657433 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657434 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657433 h1) (fun h1 : term189 = True => @lem2657432)). Qed.
Lemma lem2657435 : term189 = True.
Proof. exact (EQ_MP (@lem2657434) (@lem2657432)). Qed.
Lemma lem2657436 : term183 = True.
Proof. exact (TRANS (@lem2657431) (@lem2657435)). Qed.
Lemma lem2657437 : True = term183.
Proof. exact (SYM (@lem2657436)). Qed.
Lemma lem2657438 : term183.
Proof. exact (EQ_MP (@lem2657437) (@lem0)). Qed.
Lemma lem2657439 : term186 = term192.
Proof. exact (@lem2657428 (@lem2657438)). Qed.
Lemma lem2657441 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2657442 : term115 = term116.
Proof. exact (@lem2657441 term50 term50). Qed.
Lemma lem2657443 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657444 : term118 = term50.
Proof. exact (EQ_MP (@lem2657443) (@lem940073)). Qed.
Lemma lem2657445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657446 : term116 = term49.
Proof. exact (MK_COMB (@lem2657445) (@lem2657444)). Qed.
Lemma lem2657447 : term115 = term49.
Proof. exact (TRANS (@lem2657442) (@lem2657446)). Qed.
Lemma lem2657449 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657450 : term194 = term45.
Proof. exact (@lem2657449 term50). Qed.
Lemma lem2657451 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2657452 : term195 = term184.
Proof. exact (MK_COMB (@lem2657451) (@lem2657450)). Qed.
Lemma lem2657453 : term192 = term183.
Proof. exact (MK_COMB (@lem2657452) (@lem2657447)). Qed.
Lemma lem2657455 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657456 : term183 = term189.
Proof. exact (@lem2657455 (NUMERAL 0) term50). Qed.
Lemma lem2657457 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657458 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657459 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657458 h1) (fun h1 : term189 = True => @lem2657457)). Qed.
Lemma lem2657460 : term189 = True.
Proof. exact (EQ_MP (@lem2657459) (@lem2657457)). Qed.
Lemma lem2657461 : term183 = True.
Proof. exact (TRANS (@lem2657456) (@lem2657460)). Qed.
Lemma lem2657462 : term192 = True.
Proof. exact (TRANS (@lem2657453) (@lem2657461)). Qed.
Lemma lem2657463 : term186 = True.
Proof. exact (TRANS (@lem2657439) (@lem2657462)). Qed.
Lemma lem2657464 : term183 = True.
Proof. exact (TRANS (@lem2657416) (@lem2657463)). Qed.
Lemma lem2657465 : term182 = True.
Proof. exact (TRANS (@lem2657407) (@lem2657464)). Qed.
Lemma lem2657466 : True = term182.
Proof. exact (SYM (@lem2657465)). Qed.
Lemma lem2657467 : term182.
Proof. exact (EQ_MP (@lem2657466) (@lem0)). Qed.
Lemma lem2657468 (m : int) (n : int) (h1 : term487 m n) : term508 n.
Proof. exact (conj (@lem2657467) (@lem2657324 m n h1)). Qed.
Lemma lem2657470 (x : real) (y : real) : term509 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2657471 (n : int) : term510 n.
Proof. exact (@lem2657470 term49 (term158 n)). Qed.
Lemma lem2657472 (m : int) (n : int) (h1 : term487 m n) : term511 n.
Proof. exact (@lem2657471 n (@lem2657468 m n h1)). Qed.
Lemma lem2657473 (n : int) : (term310 n) = (term158 n).
Proof. exact (@lem1982733 (term158 n)). Qed.
Lemma lem2657474 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2657475 (n : int) : (term512 n) = (term463 n).
Proof. exact (MK_COMB (@lem2657474) (@lem2657473 n)). Qed.
Lemma lem2657476 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2657477 (n : int) : (term511 n) = (term464 n).
Proof. exact (MK_COMB (@lem2657475 n) (@lem2657476)). Qed.
Lemma lem2657478 (m : int) (n : int) (h1 : term487 m n) : term464 n.
Proof. exact (EQ_MP (@lem2657477 n) (@lem2657472 m n h1)). Qed.
Lemma lem2657479 (m : int) (n : int) (h1 : term487 m n) : term513 n.
Proof. exact (conj (@lem2657478 m n h1) (@lem2657404 m n h1)). Qed.
Lemma lem2657481 (x : real) (y : real) : term514 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem2657482 (n : int) : term515 n.
Proof. exact (@lem2657481 (term158 n) (term125 n)). Qed.
Lemma lem2657483 (m : int) (n : int) (h1 : term487 m n) : term516 n.
Proof. exact (@lem2657482 n (@lem2657479 m n h1)). Qed.
Lemma lem2657484 (n : int) : (term283 n) = (term284 n).
Proof. exact (@lem1982763 (term158 n) (real_of_int n) term106). Qed.
Lemma lem2657485 (n : int) : (term213 n) = (term214 n).
Proof. exact (@lem1982713 term106 (real_of_int n)). Qed.
Lemma lem2657487 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657488 : term49 = term103.
Proof. exact (@lem2657487 term50). Qed.
Lemma lem2657490 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2657491 : term106 = term107.
Proof. exact (@lem2657490 term50). Qed.
Lemma lem2657492 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657493 : term215 = term216.
Proof. exact (MK_COMB (@lem2657492) (@lem2657491)). Qed.
Lemma lem2657494 : term217 = term218.
Proof. exact (MK_COMB (@lem2657493) (@lem2657488)). Qed.
Lemma lem2657495 : term219.
Proof. exact (@lem1981473 term106 term49 term49 term49 term45 term49). Qed.
Lemma lem2657497 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657498 : term183 = term189.
Proof. exact (@lem2657497 (NUMERAL 0) term50). Qed.
Lemma lem2657499 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657500 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657501 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657500 h1) (fun h1 : term189 = True => @lem2657499)). Qed.
Lemma lem2657502 : term189 = True.
Proof. exact (EQ_MP (@lem2657501) (@lem2657499)). Qed.
Lemma lem2657503 : term183 = True.
Proof. exact (TRANS (@lem2657498) (@lem2657502)). Qed.
Lemma lem2657504 : True = term183.
Proof. exact (SYM (@lem2657503)). Qed.
Lemma lem2657505 : term183.
Proof. exact (EQ_MP (@lem2657504) (@lem0)). Qed.
Lemma lem2657506 : term220.
Proof. exact (@lem2657495 (@lem2657505)). Qed.
Lemma lem2657508 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657509 : term183 = term189.
Proof. exact (@lem2657508 (NUMERAL 0) term50). Qed.
Lemma lem2657510 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657511 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657512 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657511 h1) (fun h1 : term189 = True => @lem2657510)). Qed.
Lemma lem2657513 : term189 = True.
Proof. exact (EQ_MP (@lem2657512) (@lem2657510)). Qed.
Lemma lem2657514 : term183 = True.
Proof. exact (TRANS (@lem2657509) (@lem2657513)). Qed.
Lemma lem2657515 : True = term183.
Proof. exact (SYM (@lem2657514)). Qed.
Lemma lem2657516 : term183.
Proof. exact (EQ_MP (@lem2657515) (@lem0)). Qed.
Lemma lem2657517 : term221.
Proof. exact (@lem2657506 (@lem2657516)). Qed.
Lemma lem2657519 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657520 : term183 = term189.
Proof. exact (@lem2657519 (NUMERAL 0) term50). Qed.
Lemma lem2657521 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657522 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657523 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657522 h1) (fun h1 : term189 = True => @lem2657521)). Qed.
Lemma lem2657524 : term189 = True.
Proof. exact (EQ_MP (@lem2657523) (@lem2657521)). Qed.
Lemma lem2657525 : term183 = True.
Proof. exact (TRANS (@lem2657520) (@lem2657524)). Qed.
Lemma lem2657526 : True = term183.
Proof. exact (SYM (@lem2657525)). Qed.
Lemma lem2657527 : term183.
Proof. exact (EQ_MP (@lem2657526) (@lem0)). Qed.
Lemma lem2657528 : term222.
Proof. exact (@lem2657517 (@lem2657527)). Qed.
Lemma lem2657530 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2657531 : term115 = term116.
Proof. exact (@lem2657530 term50 term50). Qed.
Lemma lem2657532 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657533 : term118 = term50.
Proof. exact (EQ_MP (@lem2657532) (@lem940073)). Qed.
Lemma lem2657534 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657535 : term116 = term49.
Proof. exact (MK_COMB (@lem2657534) (@lem2657533)). Qed.
Lemma lem2657536 : term115 = term49.
Proof. exact (TRANS (@lem2657531) (@lem2657535)). Qed.
Lemma lem2657538 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2657539 : term110 = term121.
Proof. exact (@lem2657538 term50 term50). Qed.
Lemma lem2657540 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657541 : term118 = term50.
Proof. exact (EQ_MP (@lem2657540) (@lem940073)). Qed.
Lemma lem2657542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657543 : term116 = term49.
Proof. exact (MK_COMB (@lem2657542) (@lem2657541)). Qed.
Lemma lem2657544 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2657545 : term121 = term106.
Proof. exact (MK_COMB (@lem2657544) (@lem2657543)). Qed.
Lemma lem2657546 : term110 = term106.
Proof. exact (TRANS (@lem2657539) (@lem2657545)). Qed.
Lemma lem2657547 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657548 : term223 = term215.
Proof. exact (MK_COMB (@lem2657547) (@lem2657546)). Qed.
Lemma lem2657549 : term224 = term217.
Proof. exact (MK_COMB (@lem2657548) (@lem2657536)). Qed.
Lemma lem2657551 (m : nat) : (term225 m) = term45.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2657552 : term217 = term45.
Proof. exact (@lem2657551 term50). Qed.
Lemma lem2657553 : term224 = term45.
Proof. exact (TRANS (@lem2657549) (@lem2657552)). Qed.
Lemma lem2657554 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2657555 : term226 = term227.
Proof. exact (MK_COMB (@lem2657554) (@lem2657553)). Qed.
Lemma lem2657556 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem2657557 : term228 = term194.
Proof. exact (MK_COMB (@lem2657555) (@lem2657556)). Qed.
Lemma lem2657559 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657560 : term194 = term45.
Proof. exact (@lem2657559 term50). Qed.
Lemma lem2657561 : term228 = term45.
Proof. exact (TRANS (@lem2657557) (@lem2657560)). Qed.
Lemma lem2657563 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2657564 : term115 = term116.
Proof. exact (@lem2657563 term50 term50). Qed.
Lemma lem2657565 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657566 : term118 = term50.
Proof. exact (EQ_MP (@lem2657565) (@lem940073)). Qed.
Lemma lem2657567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657568 : term116 = term49.
Proof. exact (MK_COMB (@lem2657567) (@lem2657566)). Qed.
Lemma lem2657569 : term115 = term49.
Proof. exact (TRANS (@lem2657564) (@lem2657568)). Qed.
Lemma lem2657570 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem2657571 : term229 = term194.
Proof. exact (MK_COMB (@lem2657570) (@lem2657569)). Qed.
Lemma lem2657573 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657574 : term194 = term45.
Proof. exact (@lem2657573 term50). Qed.
Lemma lem2657575 : term229 = term45.
Proof. exact (TRANS (@lem2657571) (@lem2657574)). Qed.
Lemma lem2657576 : term45 = term229.
Proof. exact (SYM (@lem2657575)). Qed.
Lemma lem2657577 : term228 = term229.
Proof. exact (TRANS (@lem2657561) (@lem2657576)). Qed.
Lemma lem2657578 : term218 = term142.
Proof. exact (@lem2657528 (@lem2657577)). Qed.
Lemma lem2657579 : term217 = term142.
Proof. exact (TRANS (@lem2657494) (@lem2657578)). Qed.
Lemma lem2657581 (x : real) : (term124 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2657582 : term142 = term45.
Proof. exact (@lem2657581 term45). Qed.
Lemma lem2657583 : term217 = term45.
Proof. exact (TRANS (@lem2657579) (@lem2657582)). Qed.
Lemma lem2657584 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2657585 : term230 = term227.
Proof. exact (MK_COMB (@lem2657584) (@lem2657583)). Qed.
Lemma lem2657586 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2657587 (n : int) : (term214 n) = (term231 n).
Proof. exact (MK_COMB (@lem2657585) (@lem2657586 n)). Qed.
Lemma lem2657588 (n : int) : (term213 n) = (term231 n).
Proof. exact (TRANS (@lem2657485 n) (@lem2657587 n)). Qed.
Lemma lem2657589 (n : int) : (term231 n) = term45.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2657590 (n : int) : (term213 n) = term45.
Proof. exact (TRANS (@lem2657588 n) (@lem2657589 n)). Qed.
Lemma lem2657591 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2657592 (n : int) : (term232 n) = term47.
Proof. exact (MK_COMB (@lem2657591) (@lem2657590 n)). Qed.
Lemma lem2657593 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2657594 (n : int) : (term284 n) = term285.
Proof. exact (MK_COMB (@lem2657592 n) (@lem2657593)). Qed.
Lemma lem2657595 (n : int) : (term283 n) = term285.
Proof. exact (TRANS (@lem2657484 n) (@lem2657594 n)). Qed.
Lemma lem2657596 : term285 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2657597 (n : int) : (term283 n) = term106.
Proof. exact (TRANS (@lem2657595 n) (@lem2657596)). Qed.
Lemma lem2657598 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2657599 (n : int) : (term517 n) = term518.
Proof. exact (MK_COMB (@lem2657598) (@lem2657597 n)). Qed.
Lemma lem2657600 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2657601 (n : int) : (term516 n) = term519.
Proof. exact (MK_COMB (@lem2657599 n) (@lem2657600)). Qed.
Lemma lem2657602 (m : int) (n : int) (h1 : term487 m n) : term519.
Proof. exact (EQ_MP (@lem2657601 n) (@lem2657483 m n h1)). Qed.
Lemma lem2657604 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2657605 : term519 = term520.
Proof. exact (@lem2657604 term45 term106). Qed.
Lemma lem2657607 (x : nat) : (term104 x) = (term105 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2657608 : term106 = term107.
Proof. exact (@lem2657607 term50). Qed.
Lemma lem2657610 (x : nat) : (real_of_num x) = (term102 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2657611 : term45 = term142.
Proof. exact (@lem2657610 (NUMERAL 0)). Qed.
Lemma lem2657612 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2657613 : term184 = term185.
Proof. exact (MK_COMB (@lem2657612) (@lem2657611)). Qed.
Lemma lem2657614 : term520 = term521.
Proof. exact (MK_COMB (@lem2657613) (@lem2657608)). Qed.
Lemma lem2657615 : term522.
Proof. exact (@lem1980255 term45 term49 term106 term49). Qed.
Lemma lem2657617 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657618 : term183 = term189.
Proof. exact (@lem2657617 (NUMERAL 0) term50). Qed.
Lemma lem2657619 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657620 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657621 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657620 h1) (fun h1 : term189 = True => @lem2657619)). Qed.
Lemma lem2657622 : term189 = True.
Proof. exact (EQ_MP (@lem2657621) (@lem2657619)). Qed.
Lemma lem2657623 : term183 = True.
Proof. exact (TRANS (@lem2657618) (@lem2657622)). Qed.
Lemma lem2657624 : True = term183.
Proof. exact (SYM (@lem2657623)). Qed.
Lemma lem2657625 : term183.
Proof. exact (EQ_MP (@lem2657624) (@lem0)). Qed.
Lemma lem2657626 : term523.
Proof. exact (@lem2657615 (@lem2657625)). Qed.
Lemma lem2657628 (m : nat) (n : nat) : (term188 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2657629 : term183 = term189.
Proof. exact (@lem2657628 (NUMERAL 0) term50). Qed.
Lemma lem2657630 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2657631 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2657632 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem2657631 h1) (fun h1 : term189 = True => @lem2657630)). Qed.
Lemma lem2657633 : term189 = True.
Proof. exact (EQ_MP (@lem2657632) (@lem2657630)). Qed.
Lemma lem2657634 : term183 = True.
Proof. exact (TRANS (@lem2657629) (@lem2657633)). Qed.
Lemma lem2657635 : True = term183.
Proof. exact (SYM (@lem2657634)). Qed.
Lemma lem2657636 : term183.
Proof. exact (EQ_MP (@lem2657635) (@lem0)). Qed.
Lemma lem2657637 : term521 = term524.
Proof. exact (@lem2657626 (@lem2657636)). Qed.
Lemma lem2657639 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2657640 : term110 = term121.
Proof. exact (@lem2657639 term50 term50). Qed.
Lemma lem2657641 : (term117 = (BIT1 0)) = (term118 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2657642 : term118 = term50.
Proof. exact (EQ_MP (@lem2657641) (@lem940073)). Qed.
Lemma lem2657643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2657644 : term116 = term49.
Proof. exact (MK_COMB (@lem2657643) (@lem2657642)). Qed.
Lemma lem2657645 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2657646 : term121 = term106.
Proof. exact (MK_COMB (@lem2657645) (@lem2657644)). Qed.
Lemma lem2657647 : term110 = term106.
Proof. exact (TRANS (@lem2657640) (@lem2657646)). Qed.
Lemma lem2657649 (x : nat) : (term193 x) = term45.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2657650 : term194 = term45.
Proof. exact (@lem2657649 term50). Qed.
Lemma lem2657651 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2657652 : term195 = term184.
Proof. exact (MK_COMB (@lem2657651) (@lem2657650)). Qed.
Lemma lem2657653 : term524 = term520.
Proof. exact (MK_COMB (@lem2657652) (@lem2657647)). Qed.
Lemma lem2657655 (m : nat) (n : nat) : (term525 m n) = False.
Proof. exact (proj1 (@lem1365720 m n)). Qed.
Lemma lem2657656 : term520 = False.
Proof. exact (@lem2657655 (NUMERAL 0) term50). Qed.
Lemma lem2657657 : term524 = False.
Proof. exact (TRANS (@lem2657653) (@lem2657656)). Qed.
Lemma lem2657658 : term521 = False.
Proof. exact (TRANS (@lem2657637) (@lem2657657)). Qed.
Lemma lem2657659 : term520 = False.
Proof. exact (TRANS (@lem2657614) (@lem2657658)). Qed.
Lemma lem2657660 : term519 = False.
Proof. exact (TRANS (@lem2657605) (@lem2657659)). Qed.
Lemma lem2657661 (m : int) (n : int) (h1 : term487 m n) : False.
Proof. exact (EQ_MP (@lem2657660) (@lem2657602 m n h1)). Qed.
Lemma lem2657662 (m : int) (n : int) (h1 : term489 m n) : False.
Proof. exact (or_elim (@lem2656856 m n h1) (fun h0 : term459 m n => @lem2657321 m n h0) (fun h0 : term487 m n => @lem2657661 m n h0)). Qed.
Lemma lem2657663 (m : int) (n : int) (h1 : term491 m n) : False.
Proof. exact (or_elim (@lem2656568 m n h1) (fun h0 : term492 m n => @lem2656855 m n h0) (fun h0 : term489 m n => @lem2657662 m n h0)). Qed.
Lemma lem2657664 (n : int) (m : int) (h1 : term408 n m) : term408 n m.
Proof. exact (h1). Qed.
Lemma lem2657665 (n : int) (m : int) (h1 : term408 n m) : term491 m n.
Proof. exact (EQ_MP (@lem2656567 m n) (@lem2657664 n m h1)). Qed.
Lemma lem2657666 (n : int) (m : int) (h1 : term408 n m) : (term491 m n) = False.
Proof. exact (prop_ext (fun h2 : term491 m n => @lem2657663 m n h2) (fun h2 : False => @lem2657665 n m h1)). Qed.
Lemma lem2657667 (n : int) (m : int) (h1 : term408 n m) : False.
Proof. exact (EQ_MP (@lem2657666 n m h1) (@lem2657665 n m h1)). Qed.
Lemma lem2657668 (m : int) (n : int) (h1 : term393 m n) : term393 m n.
Proof. exact (h1). Qed.
Lemma lem2657669 (m : int) (n : int) (h1 : term393 m n) : term408 n m.
Proof. exact (EQ_MP (@lem2656130 n m) (@lem2657668 m n h1)). Qed.
Lemma lem2657670 (m : int) (n : int) (h1 : term393 m n) : (term408 n m) = False.
Proof. exact (prop_ext (fun h2 : term408 n m => @lem2657667 n m h2) (fun h2 : False => @lem2657669 m n h1)). Qed.
Lemma lem2657671 (m : int) (n : int) (h1 : term393 m n) : False.
Proof. exact (EQ_MP (@lem2657670 m n h1) (@lem2657669 m n h1)). Qed.
Lemma lem2657672 (m : int) (n : int) : term526 m n.
Proof. exact (fun h0 : term393 m n => @lem2657671 m n h0). Qed.
Lemma lem2657673 (m : int) (n : int) : term527 m n.
Proof. exact (@lem1386578 (term528 m n)). Qed.
Lemma lem2657676 (m : int) (n : int) : term528 m n.
Proof. exact (@lem2657673 m n (@lem2657672 m n)). Qed.
Lemma lem2657677 (m : int) (n : int) : (term392 m n) = (term378 m n).
Proof. exact (SYM (@lem2655780 m n)). Qed.
Lemma lem2657678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2657679 (m : int) (n : int) : (term528 m n) = (term370 m n).
Proof. exact (MK_COMB (@lem2657678) (@lem2657677 m n)). Qed.
Lemma lem2657680 (m : int) (n : int) : term370 m n.
Proof. exact (EQ_MP (@lem2657679 m n) (@lem2657676 m n)). Qed.
Lemma lem2657681 (m : int) (n : int) : term371 m n.
Proof. exact (EQ_MP (@lem2655633 m n) (@lem2657680 m n)). Qed.
Lemma lem2657682 (m : int) (n : int) : (term371 m n) = ((term371 m n) = True).
Proof. exact (@lem7 (term371 m n)). Qed.
Lemma lem2657683 (m : int) (n : int) : (term371 m n) = True.
Proof. exact (EQ_MP (@lem2657682 m n) (@lem2657681 m n)). Qed.
Lemma lem2657684 (m : int) (n : int) : True = (term371 m n).
Proof. exact (SYM (@lem2657683 m n)). Qed.
Lemma lem2657685 (m : int) (n : int) : term371 m n.
Proof. exact (EQ_MP (@lem2657684 m n) (@lem0)). Qed.
Lemma lem2657686 (m : int) (n : int) (h1 : term15 n) : term379 m n.
Proof. exact (@lem2657685 m n (@lem2653923 n h1)). Qed.
Lemma lem2657687 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : term369 m n.
Proof. exact (@lem2657686 m n h2 (@lem2653922 n m h1)). Qed.
Lemma lem2657688 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : term368 m n.
Proof. exact (EQ_MP (@lem2655632 m n) (@lem2657687 m n h1 h2)). Qed.
Lemma lem2657689 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : term319 m n.
Proof. exact (conj (@lem2655621 m n h1 h2) (@lem2657688 m n h1 h2)). Qed.
Lemma lem2657690 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : term318 m n.
Proof. exact (EQ_MP (@lem2653931 m n) (@lem2657689 m n h1 h2)). Qed.
Lemma lem2657691 (n : int) (m : int) (h1 : term317 n m) : int_le n m.
Proof. exact (proj2 (@lem2653921 n m h1)). Qed.
Lemma lem2657692 (n : int) (m : int) (h1 : term317 n m) : term15 n.
Proof. exact (proj1 (@lem2653921 n m h1)). Qed.
Lemma lem2657693 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : (int_le n m) = (term318 m n).
Proof. exact (prop_ext (fun h3 : int_le n m => @lem2657690 m n h1 h2) (fun h3 : term318 m n => @lem2653922 n m h1)). Qed.
Lemma lem2657694 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : term318 m n.
Proof. exact (EQ_MP (@lem2657693 m n h1 h2) (@lem2653922 n m h1)). Qed.
Lemma lem2657695 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : (term15 n) = (term318 m n).
Proof. exact (prop_ext (fun h3 : term15 n => @lem2657694 m n h1 h2) (fun h3 : term318 m n => @lem2653923 n h2)). Qed.
Lemma lem2657696 (m : int) (n : int) (h1 : int_le n m) (h2 : term15 n) : term318 m n.
Proof. exact (EQ_MP (@lem2657695 m n h1 h2) (@lem2653923 n h2)). Qed.
Lemma lem2657697 (m : int) (n : int) (h1 : term317 n m) (h2 : term15 n) : (int_le n m) = (term318 m n).
Proof. exact (prop_ext (fun h3 : int_le n m => @lem2657696 m n h3 h2) (fun h3 : term318 m n => @lem2657691 n m h1)). Qed.
Lemma lem2657698 (m : int) (n : int) (h1 : term317 n m) (h2 : term15 n) : term318 m n.
Proof. exact (EQ_MP (@lem2657697 m n h1 h2) (@lem2657691 n m h1)). Qed.
Lemma lem2657699 (n : int) (m : int) (h1 : term317 n m) : (term15 n) = (term318 m n).
Proof. exact (prop_ext (fun h2 : term15 n => @lem2657698 m n h1 h2) (fun h2 : term318 m n => @lem2657692 n m h1)). Qed.
Lemma lem2657700 (n : int) (m : int) (h1 : term317 n m) : term318 m n.
Proof. exact (EQ_MP (@lem2657699 n m h1) (@lem2657692 n m h1)). Qed.
Lemma lem2657701 (m : int) (n : int) : term529 m n.
Proof. exact (fun h0 : term317 n m => @lem2657700 n m h0). Qed.
Lemma lem2657706 (m : int) : term530 m.
Proof. exact (fun n : int => @lem2657701 m n). Qed.
Lemma lem2657711 : term531.
Proof. exact (fun m : int => @lem2657706 m). Qed.
