Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUM_CASES_BINARY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_POS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032084_spec.
Require Import thm1032821_spec.
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
Require Import thm1367769_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1831_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm1982711_spec.
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
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
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
Require Import thm2318497_spec.
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
Require Import thm2841377_spec.
Require Import thm2841378_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm69_spec.
Require Import thm706885_spec.
Require Import thm706887_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm912867_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem2968676 (n : nat) : (term0 n) = (term1 n).
Proof. exact (@lem1032821 n term2 (term3 n)). Qed.
Lemma lem2968677 (n : nat) (q : nat) : (term4 n q) = (term5 n q).
Proof. exact (eq_refl (term4 n q)). Qed.
Lemma lem2968678 (r : nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem2968679 (n : nat) (q : nat) (r : nat) : (term6 n q r) = (term7 n q r).
Proof. exact (MK_COMB (@lem2968677 n q) (@lem2968678 r)). Qed.
Lemma lem2968680 (r : nat) (n : nat) (q : nat) : (term7 n q r) = (term8 n q).
Proof. exact (eq_refl (term7 n q r)). Qed.
Lemma lem2968681 (r : nat) (n : nat) (q : nat) : (term6 n q r) = (term8 n q).
Proof. exact (TRANS (@lem2968679 n q r) (@lem2968680 r n q)). Qed.
Lemma lem2968682 (n : nat) (q : nat) (r : nat) : (term9 n q r) = (term9 n q r).
Proof. exact (eq_refl (term9 n q r)). Qed.
Lemma lem2968683 (r : nat) (n : nat) (q : nat) : (term10 n q r) = (term11 r n q).
Proof. exact (MK_COMB (@lem2968682 n q r) (@lem2968681 r n q)). Qed.
Lemma lem2968684 (n : nat) (q : nat) : (term12 n q) = (term13 n q).
Proof. exact (fun_ext (fun r : nat => @lem2968683 r n q)). Qed.
Lemma lem2968685 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968686 (n : nat) (q : nat) : (term14 n q) = (term15 n q).
Proof. exact (MK_COMB (@lem2968685) (@lem2968684 n q)). Qed.
Lemma lem2968687 (n : nat) : (term16 n) = (term17 n).
Proof. exact (fun_ext (fun q : nat => @lem2968686 n q)). Qed.
Lemma lem2968688 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968689 (n : nat) : (term1 n) = (term18 n).
Proof. exact (MK_COMB (@lem2968688) (@lem2968687 n)). Qed.
Lemma lem2968690 (n : nat) : (term19 n) = (term20 n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem2968691 (n : nat) : (term21 n) = (term21 n).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem2968692 (n : nat) : (term0 n) = (term22 n).
Proof. exact (MK_COMB (@lem2968690 n) (@lem2968691 n)). Qed.
Lemma lem2968693 (n : nat) : (term22 n) = (term23 n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem2968694 (n : nat) : (term0 n) = (term23 n).
Proof. exact (TRANS (@lem2968692 n) (@lem2968693 n)). Qed.
Lemma lem2968695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2968696 (n : nat) : (term24 n) = (term25 n).
Proof. exact (MK_COMB (@lem2968695) (@lem2968694 n)). Qed.
Lemma lem2968697 (n : nat) : ((term0 n) = (term1 n)) = ((term23 n) = (term18 n)).
Proof. exact (MK_COMB (@lem2968696 n) (@lem2968689 n)). Qed.
Lemma lem2968698 (n : nat) : (term23 n) = (term18 n).
Proof. exact (EQ_MP (@lem2968697 n) (@lem2968676 n)). Qed.
Lemma lem2968699 (r : nat) (n : nat) (q : nat) : (term11 r n q) = (term11 r n q).
Proof. exact (eq_refl (term11 r n q)). Qed.
Lemma lem2968700 (n : nat) (q : nat) : (term13 n q) = (term13 n q).
Proof. exact (fun_ext (fun r : nat => @lem2968699 r n q)). Qed.
Lemma lem2968701 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968702 (n : nat) (q : nat) : (term15 n q) = (term15 n q).
Proof. exact (MK_COMB (@lem2968701) (@lem2968700 n q)). Qed.
Lemma lem2968703 (n : nat) : (term17 n) = (term17 n).
Proof. exact (fun_ext (fun q : nat => @lem2968702 n q)). Qed.
Lemma lem2968704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968705 (n : nat) : (term18 n) = (term18 n).
Proof. exact (MK_COMB (@lem2968704) (@lem2968703 n)). Qed.
Lemma lem2968706 (n : nat) : (term25 n) = (term25 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem2968707 (n : nat) : ((term23 n) = (term18 n)) = ((term23 n) = (term18 n)).
Proof. exact (MK_COMB (@lem2968706 n) (@lem2968705 n)). Qed.
Lemma lem2968709 (n : nat) : (term23 n) = (term18 n).
Proof. exact (EQ_MP (@lem2968707 n) (@lem2968698 n)). Qed.
Lemma lem2968710 : term26 = term27.
Proof. exact (@lem912803). Qed.
Lemma lem2968711 (h1 : term26 = term27) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term27 h1). Qed.
Lemma lem2968712 : (term26 = term27) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term26 = term27 => @lem2968711 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem2968710)). Qed.
Lemma lem2968713 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2968712) (@lem2968710)). Qed.
Lemma lem2968714 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2968715 : term28 = (~ False).
Proof. exact (MK_COMB (@lem2968714) (@lem2968713)). Qed.
Lemma lem2968717 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2968718 : term28 = True.
Proof. exact (TRANS (@lem2968715) (@lem2968717)). Qed.
Lemma lem2968719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2968720 : term29 = (or True).
Proof. exact (MK_COMB (@lem2968719) (@lem2968718)). Qed.
Lemma lem2968727 (q : nat) (r : nat) (n : nat) : (term30 q r n) = (term30 q r n).
Proof. exact (eq_refl (term30 q r n)). Qed.
Lemma lem2968728 (q : nat) (r : nat) (n : nat) : (term31 q r n) = (term32 q r n).
Proof. exact (MK_COMB (@lem2968720) (@lem2968727 q r n)). Qed.
Lemma lem2968730 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2968731 (q : nat) (r : nat) (n : nat) : (term32 q r n) = True.
Proof. exact (@lem2968730 (term30 q r n)). Qed.
Lemma lem2968732 (q : nat) (r : nat) (n : nat) : (term31 q r n) = True.
Proof. exact (TRANS (@lem2968728 q r n) (@lem2968731 q r n)). Qed.
Lemma lem2968733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2968734 (q : nat) (r : nat) (n : nat) : (term33 q r n) = (and True).
Proof. exact (MK_COMB (@lem2968733) (@lem2968732 q r n)). Qed.
Lemma lem2968739 (n : nat) (q : nat) (r : nat) : (term34 n q r) = (term34 n q r).
Proof. exact (eq_refl (term34 n q r)). Qed.
Lemma lem2968740 (n : nat) (q : nat) (r : nat) : (term35 n q r) = (term36 n q r).
Proof. exact (MK_COMB (@lem2968734 q r n) (@lem2968739 n q r)). Qed.
Lemma lem2968742 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2968743 (n : nat) (q : nat) (r : nat) : (term36 n q r) = (term34 n q r).
Proof. exact (@lem2968742 (term34 n q r)). Qed.
Lemma lem2968746 (n : nat) (q : nat) (r : nat) : (term35 n q r) = (term34 n q r).
Proof. exact (TRANS (@lem2968740 n q r) (@lem2968743 n q r)). Qed.
Lemma lem2968747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2968748 (n : nat) (q : nat) (r : nat) : (term9 n q r) = (term37 n q r).
Proof. exact (MK_COMB (@lem2968747) (@lem2968746 n q r)). Qed.
Lemma lem2968755 (n : nat) (q : nat) : (term8 n q) = (term8 n q).
Proof. exact (eq_refl (term8 n q)). Qed.
Lemma lem2968756 (r : nat) (n : nat) (q : nat) : (term11 r n q) = (term38 r n q).
Proof. exact (MK_COMB (@lem2968748 n q r) (@lem2968755 n q)). Qed.
Lemma lem2968759 (n : nat) (q : nat) : (term13 n q) = (term39 n q).
Proof. exact (fun_ext (fun r : nat => @lem2968756 r n q)). Qed.
Lemma lem2968760 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968761 (n : nat) (q : nat) : (term15 n q) = (term40 n q).
Proof. exact (MK_COMB (@lem2968760) (@lem2968759 n q)). Qed.
Lemma lem2968766 (n : nat) : (term17 n) = (term41 n).
Proof. exact (fun_ext (fun q : nat => @lem2968761 n q)). Qed.
Lemma lem2968767 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968768 (n : nat) : (term18 n) = (term42 n).
Proof. exact (MK_COMB (@lem2968767) (@lem2968766 n)). Qed.
Lemma lem2968777 (n : nat) : (term23 n) = (term42 n).
Proof. exact (TRANS (@lem2968709 n) (@lem2968768 n)). Qed.
Lemma lem2968808 (n : nat) (q : nat) : (term8 n q) = (term8 n q).
Proof. exact (eq_refl (term8 n q)). Qed.
Lemma lem2968815 (r : nat) : (term43 r) = (term43 r).
Proof. exact (eq_refl (term43 r)). Qed.
Lemma lem2968816 (r : nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem2968823 (q : nat) : (term44 q) = (term45 q).
Proof. exact (@lem1032084 term2 q). Qed.
Lemma lem2968824 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem2968825 (q : nat) : (term46 q) = (term47 q).
Proof. exact (MK_COMB (@lem2968824) (@lem2968823 q)). Qed.
Lemma lem2968828 (q : nat) (r : nat) : (term48 q r) = (term49 q r).
Proof. exact (MK_COMB (@lem2968825 q) (@lem2968816 r)). Qed.
Lemma lem2968831 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem2968832 (n : nat) (q : nat) (r : nat) : (n = (term48 q r)) = (n = (term49 q r)).
Proof. exact (MK_COMB (@lem2968831 n) (@lem2968828 q r)). Qed.
Lemma lem2968833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2968834 (n : nat) (q : nat) (r : nat) : (term50 n q r) = (term51 n q r).
Proof. exact (MK_COMB (@lem2968833) (@lem2968832 n q r)). Qed.
Lemma lem2968835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2968836 (n : nat) (q : nat) (r : nat) : (term52 n q r) = (term53 n q r).
Proof. exact (MK_COMB (@lem2968835) (@lem2968834 n q r)). Qed.
Lemma lem2968837 (n : nat) (q : nat) (r : nat) : (term34 n q r) = (term54 n q r).
Proof. exact (MK_COMB (@lem2968836 n q r) (@lem2968815 r)). Qed.
Lemma lem2968838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2968839 (n : nat) (q : nat) (r : nat) : (term37 n q r) = (term55 n q r).
Proof. exact (MK_COMB (@lem2968838) (@lem2968837 n q r)). Qed.
Lemma lem2968840 (r : nat) (n : nat) (q : nat) : (term38 r n q) = (term56 r n q).
Proof. exact (MK_COMB (@lem2968839 n q r) (@lem2968808 n q)). Qed.
Lemma lem2968841 (n : nat) (q : nat) : (term39 n q) = (term57 n q).
Proof. exact (fun_ext (fun r : nat => @lem2968840 r n q)). Qed.
Lemma lem2968842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968843 (n : nat) (q : nat) : (term40 n q) = (term58 n q).
Proof. exact (MK_COMB (@lem2968842) (@lem2968841 n q)). Qed.
Lemma lem2968844 (n : nat) : (term41 n) = (term59 n).
Proof. exact (fun_ext (fun q : nat => @lem2968843 n q)). Qed.
Lemma lem2968845 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968846 (n : nat) : (term42 n) = (term60 n).
Proof. exact (MK_COMB (@lem2968845) (@lem2968844 n)). Qed.
Lemma lem2968849 (n : nat) : (term23 n) = (term60 n).
Proof. exact (TRANS (@lem2968777 n) (@lem2968846 n)). Qed.
Lemma lem2968851 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem2968852 (n : nat) (q : nat) (r : nat) : (n = (term49 q r)) = ((int_of_num n) = (term61 q r)).
Proof. exact (@lem2968851 n (term49 q r)). Qed.
Lemma lem2968856 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem2968857 (q : nat) (r : nat) : (term61 q r) = (term64 q r).
Proof. exact (@lem2968856 (term45 q) r). Qed.
Lemma lem2968859 (k : nat) (n : nat) : (term65 k n) = (term66 k n).
Proof. exact (EQ_MP (@lem2841378 k n) (@lem2841377 k n)). Qed.
Lemma lem2968860 (q : nat) : (term67 q) = (term68 q).
Proof. exact (@lem2968859 term27 q). Qed.
Lemma lem2968861 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2968862 (q : nat) : (term69 q) = (term70 q).
Proof. exact (MK_COMB (@lem2968861) (@lem2968860 q)). Qed.
Lemma lem2968863 (r : nat) : (int_of_num r) = (int_of_num r).
Proof. exact (eq_refl (int_of_num r)). Qed.
Lemma lem2968864 (q : nat) (r : nat) : (term64 q r) = (term71 q r).
Proof. exact (MK_COMB (@lem2968862 q) (@lem2968863 r)). Qed.
Lemma lem2968865 (q : nat) (r : nat) : (term61 q r) = (term71 q r).
Proof. exact (TRANS (@lem2968857 q r) (@lem2968864 q r)). Qed.
Lemma lem2968866 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem2968867 (n : nat) (q : nat) (r : nat) : ((int_of_num n) = (term61 q r)) = ((int_of_num n) = (term71 q r)).
Proof. exact (MK_COMB (@lem2968866 n) (@lem2968865 q r)). Qed.
Lemma lem2968868 (n : nat) (q : nat) (r : nat) : (n = (term49 q r)) = ((int_of_num n) = (term71 q r)).
Proof. exact (TRANS (@lem2968852 n q r) (@lem2968867 n q r)). Qed.
Lemma lem2968869 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2968870 (n : nat) (q : nat) (r : nat) : (term51 n q r) = (term73 n q r).
Proof. exact (MK_COMB (@lem2968869) (@lem2968868 n q r)). Qed.
Lemma lem2968871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2968872 (n : nat) (q : nat) (r : nat) : (term53 n q r) = (term74 n q r).
Proof. exact (MK_COMB (@lem2968871) (@lem2968870 n q r)). Qed.
Lemma lem2968874 (m : nat) (n : nat) : (Peano.lt m n) = (term75 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem2968875 (r : nat) : (term76 r) = (term77 r).
Proof. exact (@lem2968874 r term2). Qed.
Lemma lem2968876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2968877 (r : nat) : (term43 r) = (term78 r).
Proof. exact (MK_COMB (@lem2968876) (@lem2968875 r)). Qed.
Lemma lem2968878 (n : nat) (q : nat) (r : nat) : (term54 n q r) = (term79 n q r).
Proof. exact (MK_COMB (@lem2968872 n q r) (@lem2968877 r)). Qed.
Lemma lem2968879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2968880 (n : nat) (q : nat) (r : nat) : (term55 n q r) = (term80 n q r).
Proof. exact (MK_COMB (@lem2968879) (@lem2968878 n q r)). Qed.
Lemma lem2968882 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem2968883 (n : nat) (q : nat) : (n = (term45 q)) = ((int_of_num n) = (term67 q)).
Proof. exact (@lem2968882 n (term45 q)). Qed.
Lemma lem2968887 (k : nat) (n : nat) : (term65 k n) = (term66 k n).
Proof. exact (EQ_MP (@lem2841378 k n) (@lem2841377 k n)). Qed.
Lemma lem2968888 (q : nat) : (term67 q) = (term68 q).
Proof. exact (@lem2968887 term27 q). Qed.
Lemma lem2968889 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem2968890 (n : nat) (q : nat) : ((int_of_num n) = (term67 q)) = ((int_of_num n) = (term68 q)).
Proof. exact (MK_COMB (@lem2968889 n) (@lem2968888 q)). Qed.
Lemma lem2968891 (n : nat) (q : nat) : (n = (term45 q)) = ((int_of_num n) = (term68 q)).
Proof. exact (TRANS (@lem2968883 n q) (@lem2968890 n q)). Qed.
Lemma lem2968892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2968893 (n : nat) (q : nat) : (term81 n q) = (term82 n q).
Proof. exact (MK_COMB (@lem2968892) (@lem2968891 n q)). Qed.
Lemma lem2968895 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem2968896 (n : nat) (q : nat) : (n = (term83 q)) = ((int_of_num n) = (term84 q)).
Proof. exact (@lem2968895 n (term83 q)). Qed.
Lemma lem2968900 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem2968901 (q : nat) : (term84 q) = (term85 q).
Proof. exact (@lem2968900 (term45 q) term86). Qed.
Lemma lem2968903 (k : nat) (n : nat) : (term65 k n) = (term66 k n).
Proof. exact (EQ_MP (@lem2841378 k n) (@lem2841377 k n)). Qed.
Lemma lem2968904 (q : nat) : (term67 q) = (term68 q).
Proof. exact (@lem2968903 term27 q). Qed.
Lemma lem2968905 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2968906 (q : nat) : (term69 q) = (term70 q).
Proof. exact (MK_COMB (@lem2968905) (@lem2968904 q)). Qed.
Lemma lem2968907 : term87 = term87.
Proof. exact (eq_refl term87). Qed.
Lemma lem2968908 (q : nat) : (term85 q) = (term88 q).
Proof. exact (MK_COMB (@lem2968906 q) (@lem2968907)). Qed.
Lemma lem2968909 (q : nat) : (term84 q) = (term88 q).
Proof. exact (TRANS (@lem2968901 q) (@lem2968908 q)). Qed.
Lemma lem2968910 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem2968911 (n : nat) (q : nat) : ((int_of_num n) = (term84 q)) = ((int_of_num n) = (term88 q)).
Proof. exact (MK_COMB (@lem2968910 n) (@lem2968909 q)). Qed.
Lemma lem2968912 (n : nat) (q : nat) : (n = (term83 q)) = ((int_of_num n) = (term88 q)).
Proof. exact (TRANS (@lem2968896 n q) (@lem2968911 n q)). Qed.
Lemma lem2968913 (n : nat) (q : nat) : (term8 n q) = (term89 n q).
Proof. exact (MK_COMB (@lem2968893 n q) (@lem2968912 n q)). Qed.
Lemma lem2968914 (r : nat) (n : nat) (q : nat) : (term56 r n q) = (term90 r n q).
Proof. exact (MK_COMB (@lem2968880 n q r) (@lem2968913 n q)). Qed.
Lemma lem2968915 (n : nat) (q : nat) : (term57 n q) = (term91 n q).
Proof. exact (fun_ext (fun r : nat => @lem2968914 r n q)). Qed.
Lemma lem2968916 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968917 (n : nat) (q : nat) : (term58 n q) = (term92 n q).
Proof. exact (MK_COMB (@lem2968916) (@lem2968915 n q)). Qed.
Lemma lem2968918 (n : nat) : (term59 n) = (term93 n).
Proof. exact (fun_ext (fun q : nat => @lem2968917 n q)). Qed.
Lemma lem2968919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2968920 (n : nat) : (term60 n) = (term94 n).
Proof. exact (MK_COMB (@lem2968919) (@lem2968918 n)). Qed.
Lemma lem2968921 (n : nat) : (term23 n) = (term94 n).
Proof. exact (TRANS (@lem2968849 n) (@lem2968920 n)). Qed.
Lemma lem2968922 (n : nat) : term95 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem2968923 (n : nat) : (term95 n) = (term96 n).
Proof. exact (eq_refl (term95 n)). Qed.
Lemma lem2968924 (n : nat) : term96 n.
Proof. exact (EQ_MP (@lem2968923 n) (@lem2968922 n)). Qed.
Lemma lem2968925 (q : nat) : term95 q.
Proof. exact (@lem2307535 q). Qed.
Lemma lem2968926 (q : nat) : (term95 q) = (term96 q).
Proof. exact (eq_refl (term95 q)). Qed.
Lemma lem2968927 (q : nat) : term96 q.
Proof. exact (EQ_MP (@lem2968926 q) (@lem2968925 q)). Qed.
Lemma lem2968928 (r : nat) : term95 r.
Proof. exact (@lem2307535 r). Qed.
Lemma lem2968929 (r : nat) : (term95 r) = (term96 r).
Proof. exact (eq_refl (term95 r)). Qed.
Lemma lem2968930 (r : nat) : term96 r.
Proof. exact (EQ_MP (@lem2968929 r) (@lem2968928 r)). Qed.
Lemma lem2968931 (_31796 : int) (_31794 : int) (_31795 : int) : (term97 _31796 _31794 _31795) = (term98 _31796 _31794 _31795).
Proof. exact (@lem2318604 (term98 _31796 _31794 _31795)). Qed.
Lemma lem2968954 (_31794 : int) (_31795 : int) (_31796 : int) : (term99 _31794 _31795 _31796) = (_31794 = (term100 _31795 _31796)).
Proof. exact (@lem16933 (_31794 = (term100 _31795 _31796))). Qed.
Lemma lem2968957 (_31796 : int) : (term101 _31796) = (term102 _31796).
Proof. exact (@lem16933 (term102 _31796)). Qed.
Lemma lem2968958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2968959 (_31794 : int) (_31795 : int) (_31796 : int) : (term103 _31794 _31795 _31796) = (term104 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2968958) (@lem2968954 _31794 _31795 _31796)). Qed.
Lemma lem2968960 (_31794 : int) (_31795 : int) (_31796 : int) : (term105 _31794 _31795 _31796) = (term106 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2968959 _31794 _31795 _31796) (@lem2968957 _31796)). Qed.
Lemma lem2968961 (_31794 : int) (_31795 : int) (_31796 : int) : (term107 _31794 _31795 _31796) = (term105 _31794 _31795 _31796).
Proof. exact (@lem17160 (term108 _31794 _31795 _31796) (term109 _31796)). Qed.
Lemma lem2968962 (_31794 : int) (_31795 : int) (_31796 : int) : (term107 _31794 _31795 _31796) = (term106 _31794 _31795 _31796).
Proof. exact (TRANS (@lem2968961 _31794 _31795 _31796) (@lem2968960 _31794 _31795 _31796)). Qed.
Lemma lem2968969 (_31794 : int) (_31795 : int) : (term110 _31794 _31795) = (term111 _31794 _31795).
Proof. exact (@lem17160 (_31794 = (term112 _31795)) (_31794 = (term113 _31795))). Qed.
Lemma lem2968970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2968971 (_31794 : int) (_31795 : int) (_31796 : int) : (term114 _31794 _31795 _31796) = (term115 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2968970) (@lem2968962 _31794 _31795 _31796)). Qed.
Lemma lem2968972 (_31796 : int) (_31794 : int) (_31795 : int) : (term116 _31796 _31794 _31795) = (term117 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2968971 _31794 _31795 _31796) (@lem2968969 _31794 _31795)). Qed.
Lemma lem2968973 (_31796 : int) (_31794 : int) (_31795 : int) : (term118 _31796 _31794 _31795) = (term116 _31796 _31794 _31795).
Proof. exact (@lem17160 (term119 _31794 _31795 _31796) (term120 _31794 _31795)). Qed.
Lemma lem2968974 (_31796 : int) (_31794 : int) (_31795 : int) : (term118 _31796 _31794 _31795) = (term117 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2968973 _31796 _31794 _31795) (@lem2968972 _31796 _31794 _31795)). Qed.
Lemma lem2968976 (_31796 : int) : (term121 _31796) = (term121 _31796).
Proof. exact (eq_refl (term121 _31796)). Qed.
Lemma lem2968977 (_31796 : int) (_31794 : int) (_31795 : int) : (term122 _31796 _31794 _31795) = (term123 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2968976 _31796) (@lem2968974 _31796 _31794 _31795)). Qed.
Lemma lem2968978 (_31796 : int) (_31794 : int) (_31795 : int) : (term124 _31796 _31794 _31795) = (term122 _31796 _31794 _31795).
Proof. exact (@lem17362 (term125 _31796) (term126 _31796 _31794 _31795)). Qed.
Lemma lem2968979 (_31796 : int) (_31794 : int) (_31795 : int) : (term124 _31796 _31794 _31795) = (term123 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2968978 _31796 _31794 _31795) (@lem2968977 _31796 _31794 _31795)). Qed.
Lemma lem2968981 (_31795 : int) : (term121 _31795) = (term121 _31795).
Proof. exact (eq_refl (term121 _31795)). Qed.
Lemma lem2968982 (_31796 : int) (_31794 : int) (_31795 : int) : (term127 _31796 _31794 _31795) = (term128 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2968981 _31795) (@lem2968979 _31796 _31794 _31795)). Qed.
Lemma lem2968983 (_31796 : int) (_31794 : int) (_31795 : int) : (term129 _31796 _31794 _31795) = (term127 _31796 _31794 _31795).
Proof. exact (@lem17362 (term125 _31795) (term130 _31796 _31794 _31795)). Qed.
Lemma lem2968984 (_31796 : int) (_31794 : int) (_31795 : int) : (term129 _31796 _31794 _31795) = (term128 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2968983 _31796 _31794 _31795) (@lem2968982 _31796 _31794 _31795)). Qed.
Lemma lem2968986 (_31794 : int) : (term121 _31794) = (term121 _31794).
Proof. exact (eq_refl (term121 _31794)). Qed.
Lemma lem2968987 (_31796 : int) (_31794 : int) (_31795 : int) : (term131 _31796 _31794 _31795) = (term132 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2968986 _31794) (@lem2968984 _31796 _31794 _31795)). Qed.
Lemma lem2968988 (_31796 : int) (_31794 : int) (_31795 : int) : (term133 _31796 _31794 _31795) = (term131 _31796 _31794 _31795).
Proof. exact (@lem17362 (term125 _31794) (term134 _31796 _31794 _31795)). Qed.
Lemma lem2969020 (_31796 : int) (_31794 : int) (_31795 : int) : (term133 _31796 _31794 _31795) = (term132 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2968988 _31796 _31794 _31795) (@lem2968987 _31796 _31794 _31795)). Qed.
Lemma lem2969023 (x : int) (y : int) : (int_le x y) = (term135 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2969024 (_31794 : int) : (term125 _31794) = (term136 _31794).
Proof. exact (@lem2969023 term137 _31794). Qed.
Lemma lem2969026 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969027 : term139 = term140.
Proof. exact (@lem2969026 (NUMERAL 0)). Qed.
Lemma lem2969028 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2969029 : term141 = term142.
Proof. exact (MK_COMB (@lem2969028) (@lem2969027)). Qed.
Lemma lem2969030 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2969031 (_31794 : int) : (term136 _31794) = (term143 _31794).
Proof. exact (MK_COMB (@lem2969029) (@lem2969030 _31794)). Qed.
Lemma lem2969033 (_31794 : int) : (term125 _31794) = (term143 _31794).
Proof. exact (TRANS (@lem2969024 _31794) (@lem2969031 _31794)). Qed.
Lemma lem2969036 (x : int) (y : int) : (int_le x y) = (term135 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2969037 (_31795 : int) : (term125 _31795) = (term136 _31795).
Proof. exact (@lem2969036 term137 _31795). Qed.
Lemma lem2969039 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969040 : term139 = term140.
Proof. exact (@lem2969039 (NUMERAL 0)). Qed.
Lemma lem2969041 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2969042 : term141 = term142.
Proof. exact (MK_COMB (@lem2969041) (@lem2969040)). Qed.
Lemma lem2969043 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2969044 (_31795 : int) : (term136 _31795) = (term143 _31795).
Proof. exact (MK_COMB (@lem2969042) (@lem2969043 _31795)). Qed.
Lemma lem2969046 (_31795 : int) : (term125 _31795) = (term143 _31795).
Proof. exact (TRANS (@lem2969037 _31795) (@lem2969044 _31795)). Qed.
Lemma lem2969049 (x : int) (y : int) : (int_le x y) = (term135 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2969050 (_31796 : int) : (term125 _31796) = (term136 _31796).
Proof. exact (@lem2969049 term137 _31796). Qed.
Lemma lem2969052 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969053 : term139 = term140.
Proof. exact (@lem2969052 (NUMERAL 0)). Qed.
Lemma lem2969054 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2969055 : term141 = term142.
Proof. exact (MK_COMB (@lem2969054) (@lem2969053)). Qed.
Lemma lem2969056 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2969057 (_31796 : int) : (term136 _31796) = (term143 _31796).
Proof. exact (MK_COMB (@lem2969055) (@lem2969056 _31796)). Qed.
Lemma lem2969059 (_31796 : int) : (term125 _31796) = (term143 _31796).
Proof. exact (TRANS (@lem2969050 _31796) (@lem2969057 _31796)). Qed.
Lemma lem2969062 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2969063 (_31794 : int) (_31795 : int) (_31796 : int) : (_31794 = (term100 _31795 _31796)) = ((real_of_int _31794) = (term144 _31795 _31796)).
Proof. exact (@lem2969062 _31794 (term100 _31795 _31796)). Qed.
Lemma lem2969067 (x : int) (y : int) : (term145 x y) = (term146 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2969068 (_31795 : int) (_31796 : int) : (term144 _31795 _31796) = (term147 _31795 _31796).
Proof. exact (@lem2969067 (term112 _31795) _31796). Qed.
Lemma lem2969070 (x : int) (y : int) : (term148 x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2969071 (_31795 : int) : (term150 _31795) = (term151 _31795).
Proof. exact (@lem2969070 term152 _31795). Qed.
Lemma lem2969073 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969074 : term153 = term154.
Proof. exact (@lem2969073 term2). Qed.
Lemma lem2969075 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969076 : term155 = term156.
Proof. exact (MK_COMB (@lem2969075) (@lem2969074)). Qed.
Lemma lem2969077 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2969078 (_31795 : int) : (term151 _31795) = (term157 _31795).
Proof. exact (MK_COMB (@lem2969076) (@lem2969077 _31795)). Qed.
Lemma lem2969079 (_31795 : int) : (term150 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2969071 _31795) (@lem2969078 _31795)). Qed.
Lemma lem2969080 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969081 (_31795 : int) : (term158 _31795) = (term159 _31795).
Proof. exact (MK_COMB (@lem2969080) (@lem2969079 _31795)). Qed.
Lemma lem2969082 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2969083 (_31795 : int) (_31796 : int) : (term147 _31795 _31796) = (term160 _31795 _31796).
Proof. exact (MK_COMB (@lem2969081 _31795) (@lem2969082 _31796)). Qed.
Lemma lem2969084 (_31795 : int) (_31796 : int) : (term144 _31795 _31796) = (term160 _31795 _31796).
Proof. exact (TRANS (@lem2969068 _31795 _31796) (@lem2969083 _31795 _31796)). Qed.
Lemma lem2969085 (_31794 : int) : (term161 _31794) = (term161 _31794).
Proof. exact (eq_refl (term161 _31794)). Qed.
Lemma lem2969086 (_31794 : int) (_31795 : int) (_31796 : int) : ((real_of_int _31794) = (term144 _31795 _31796)) = ((real_of_int _31794) = (term160 _31795 _31796)).
Proof. exact (MK_COMB (@lem2969085 _31794) (@lem2969084 _31795 _31796)). Qed.
Lemma lem2969088 (_31794 : int) (_31795 : int) (_31796 : int) : (_31794 = (term100 _31795 _31796)) = ((real_of_int _31794) = (term160 _31795 _31796)).
Proof. exact (TRANS (@lem2969063 _31794 _31795 _31796) (@lem2969086 _31794 _31795 _31796)). Qed.
Lemma lem2969090 (x : int) (y : int) : (int_lt x y) = (term162 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2969091 (_31796 : int) : (term102 _31796) = (term163 _31796).
Proof. exact (@lem2969090 _31796 term152). Qed.
Lemma lem2969093 (x : int) (y : int) : (int_le x y) = (term135 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2969094 (_31796 : int) : (term163 _31796) = (term164 _31796).
Proof. exact (@lem2969093 (term165 _31796) term152). Qed.
Lemma lem2969096 (x : int) (y : int) : (term145 x y) = (term146 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2969097 (_31796 : int) : (term166 _31796) = (term167 _31796).
Proof. exact (@lem2969096 _31796 term87). Qed.
Lemma lem2969099 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969100 : term168 = term169.
Proof. exact (@lem2969099 term86). Qed.
Lemma lem2969101 (_31796 : int) : (term170 _31796) = (term170 _31796).
Proof. exact (eq_refl (term170 _31796)). Qed.
Lemma lem2969102 (_31796 : int) : (term167 _31796) = (term171 _31796).
Proof. exact (MK_COMB (@lem2969101 _31796) (@lem2969100)). Qed.
Lemma lem2969103 (_31796 : int) : (term166 _31796) = (term171 _31796).
Proof. exact (TRANS (@lem2969097 _31796) (@lem2969102 _31796)). Qed.
Lemma lem2969104 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2969105 (_31796 : int) : (term172 _31796) = (term173 _31796).
Proof. exact (MK_COMB (@lem2969104) (@lem2969103 _31796)). Qed.
Lemma lem2969107 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969108 : term153 = term154.
Proof. exact (@lem2969107 term2). Qed.
Lemma lem2969109 (_31796 : int) : (term164 _31796) = (term174 _31796).
Proof. exact (MK_COMB (@lem2969105 _31796) (@lem2969108)). Qed.
Lemma lem2969110 (_31796 : int) : (term163 _31796) = (term174 _31796).
Proof. exact (TRANS (@lem2969094 _31796) (@lem2969109 _31796)). Qed.
Lemma lem2969111 (_31796 : int) : (term102 _31796) = (term174 _31796).
Proof. exact (TRANS (@lem2969091 _31796) (@lem2969110 _31796)). Qed.
Lemma lem2969112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2969113 (_31794 : int) (_31795 : int) (_31796 : int) : (term104 _31794 _31795 _31796) = (term175 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2969112) (@lem2969088 _31794 _31795 _31796)). Qed.
Lemma lem2969114 (_31794 : int) (_31795 : int) (_31796 : int) : (term106 _31794 _31795 _31796) = (term176 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2969113 _31794 _31795 _31796) (@lem2969111 _31796)). Qed.
Lemma lem2969116 (y : int) (x : int) : (term177 x y) = (term178 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2969117 (_31795 : int) (_31794 : int) : (term179 _31794 _31795) = (term180 _31795 _31794).
Proof. exact (@lem2969116 (term112 _31795) _31794). Qed.
Lemma lem2969119 (x : int) (y : int) : (int_le x y) = (term135 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2969120 (_31794 : int) (_31795 : int) : (term181 _31794 _31795) = (term182 _31794 _31795).
Proof. exact (@lem2969119 (term165 _31794) (term112 _31795)). Qed.
Lemma lem2969122 (x : int) (y : int) : (term145 x y) = (term146 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2969123 (_31794 : int) : (term166 _31794) = (term167 _31794).
Proof. exact (@lem2969122 _31794 term87). Qed.
Lemma lem2969125 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969126 : term168 = term169.
Proof. exact (@lem2969125 term86). Qed.
Lemma lem2969127 (_31794 : int) : (term170 _31794) = (term170 _31794).
Proof. exact (eq_refl (term170 _31794)). Qed.
Lemma lem2969128 (_31794 : int) : (term167 _31794) = (term171 _31794).
Proof. exact (MK_COMB (@lem2969127 _31794) (@lem2969126)). Qed.
Lemma lem2969129 (_31794 : int) : (term166 _31794) = (term171 _31794).
Proof. exact (TRANS (@lem2969123 _31794) (@lem2969128 _31794)). Qed.
Lemma lem2969130 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2969131 (_31794 : int) : (term172 _31794) = (term173 _31794).
Proof. exact (MK_COMB (@lem2969130) (@lem2969129 _31794)). Qed.
Lemma lem2969133 (x : int) (y : int) : (term148 x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2969134 (_31795 : int) : (term150 _31795) = (term151 _31795).
Proof. exact (@lem2969133 term152 _31795). Qed.
Lemma lem2969136 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969137 : term153 = term154.
Proof. exact (@lem2969136 term2). Qed.
Lemma lem2969138 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969139 : term155 = term156.
Proof. exact (MK_COMB (@lem2969138) (@lem2969137)). Qed.
Lemma lem2969140 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2969141 (_31795 : int) : (term151 _31795) = (term157 _31795).
Proof. exact (MK_COMB (@lem2969139) (@lem2969140 _31795)). Qed.
Lemma lem2969142 (_31795 : int) : (term150 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2969134 _31795) (@lem2969141 _31795)). Qed.
Lemma lem2969143 (_31794 : int) (_31795 : int) : (term182 _31794 _31795) = (term183 _31794 _31795).
Proof. exact (MK_COMB (@lem2969131 _31794) (@lem2969142 _31795)). Qed.
Lemma lem2969144 (_31794 : int) (_31795 : int) : (term181 _31794 _31795) = (term183 _31794 _31795).
Proof. exact (TRANS (@lem2969120 _31794 _31795) (@lem2969143 _31794 _31795)). Qed.
Lemma lem2969145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2969146 (_31794 : int) (_31795 : int) : (term184 _31794 _31795) = (term185 _31794 _31795).
Proof. exact (MK_COMB (@lem2969145) (@lem2969144 _31794 _31795)). Qed.
Lemma lem2969148 (x : int) (y : int) : (int_le x y) = (term135 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2969149 (_31795 : int) (_31794 : int) : (term186 _31795 _31794) = (term187 _31795 _31794).
Proof. exact (@lem2969148 (term113 _31795) _31794). Qed.
Lemma lem2969151 (x : int) (y : int) : (term145 x y) = (term146 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2969152 (_31795 : int) : (term188 _31795) = (term189 _31795).
Proof. exact (@lem2969151 (term112 _31795) term87). Qed.
Lemma lem2969154 (x : int) (y : int) : (term148 x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2969155 (_31795 : int) : (term150 _31795) = (term151 _31795).
Proof. exact (@lem2969154 term152 _31795). Qed.
Lemma lem2969157 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969158 : term153 = term154.
Proof. exact (@lem2969157 term2). Qed.
Lemma lem2969159 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969160 : term155 = term156.
Proof. exact (MK_COMB (@lem2969159) (@lem2969158)). Qed.
Lemma lem2969161 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2969162 (_31795 : int) : (term151 _31795) = (term157 _31795).
Proof. exact (MK_COMB (@lem2969160) (@lem2969161 _31795)). Qed.
Lemma lem2969163 (_31795 : int) : (term150 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2969155 _31795) (@lem2969162 _31795)). Qed.
Lemma lem2969164 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969165 (_31795 : int) : (term158 _31795) = (term159 _31795).
Proof. exact (MK_COMB (@lem2969164) (@lem2969163 _31795)). Qed.
Lemma lem2969167 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969168 : term168 = term169.
Proof. exact (@lem2969167 term86). Qed.
Lemma lem2969169 (_31795 : int) : (term189 _31795) = (term190 _31795).
Proof. exact (MK_COMB (@lem2969165 _31795) (@lem2969168)). Qed.
Lemma lem2969170 (_31795 : int) : (term188 _31795) = (term190 _31795).
Proof. exact (TRANS (@lem2969152 _31795) (@lem2969169 _31795)). Qed.
Lemma lem2969171 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2969172 (_31795 : int) : (term191 _31795) = (term192 _31795).
Proof. exact (MK_COMB (@lem2969171) (@lem2969170 _31795)). Qed.
Lemma lem2969173 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2969174 (_31795 : int) (_31794 : int) : (term187 _31795 _31794) = (term193 _31795 _31794).
Proof. exact (MK_COMB (@lem2969172 _31795) (@lem2969173 _31794)). Qed.
Lemma lem2969175 (_31795 : int) (_31794 : int) : (term186 _31795 _31794) = (term193 _31795 _31794).
Proof. exact (TRANS (@lem2969149 _31795 _31794) (@lem2969174 _31795 _31794)). Qed.
Lemma lem2969176 (_31795 : int) (_31794 : int) : (term180 _31795 _31794) = (term194 _31795 _31794).
Proof. exact (MK_COMB (@lem2969146 _31794 _31795) (@lem2969175 _31795 _31794)). Qed.
Lemma lem2969177 (_31795 : int) (_31794 : int) : (term179 _31794 _31795) = (term194 _31795 _31794).
Proof. exact (TRANS (@lem2969117 _31795 _31794) (@lem2969176 _31795 _31794)). Qed.
Lemma lem2969179 (y : int) (x : int) : (term177 x y) = (term178 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2969180 (_31795 : int) (_31794 : int) : (term195 _31794 _31795) = (term196 _31795 _31794).
Proof. exact (@lem2969179 (term113 _31795) _31794). Qed.
Lemma lem2969182 (x : int) (y : int) : (int_le x y) = (term135 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2969183 (_31794 : int) (_31795 : int) : (term197 _31794 _31795) = (term198 _31794 _31795).
Proof. exact (@lem2969182 (term165 _31794) (term113 _31795)). Qed.
Lemma lem2969185 (x : int) (y : int) : (term145 x y) = (term146 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2969186 (_31794 : int) : (term166 _31794) = (term167 _31794).
Proof. exact (@lem2969185 _31794 term87). Qed.
Lemma lem2969188 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969189 : term168 = term169.
Proof. exact (@lem2969188 term86). Qed.
Lemma lem2969190 (_31794 : int) : (term170 _31794) = (term170 _31794).
Proof. exact (eq_refl (term170 _31794)). Qed.
Lemma lem2969191 (_31794 : int) : (term167 _31794) = (term171 _31794).
Proof. exact (MK_COMB (@lem2969190 _31794) (@lem2969189)). Qed.
Lemma lem2969192 (_31794 : int) : (term166 _31794) = (term171 _31794).
Proof. exact (TRANS (@lem2969186 _31794) (@lem2969191 _31794)). Qed.
Lemma lem2969193 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2969194 (_31794 : int) : (term172 _31794) = (term173 _31794).
Proof. exact (MK_COMB (@lem2969193) (@lem2969192 _31794)). Qed.
Lemma lem2969196 (x : int) (y : int) : (term145 x y) = (term146 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2969197 (_31795 : int) : (term188 _31795) = (term189 _31795).
Proof. exact (@lem2969196 (term112 _31795) term87). Qed.
Lemma lem2969199 (x : int) (y : int) : (term148 x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2969200 (_31795 : int) : (term150 _31795) = (term151 _31795).
Proof. exact (@lem2969199 term152 _31795). Qed.
Lemma lem2969202 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969203 : term153 = term154.
Proof. exact (@lem2969202 term2). Qed.
Lemma lem2969204 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969205 : term155 = term156.
Proof. exact (MK_COMB (@lem2969204) (@lem2969203)). Qed.
Lemma lem2969206 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2969207 (_31795 : int) : (term151 _31795) = (term157 _31795).
Proof. exact (MK_COMB (@lem2969205) (@lem2969206 _31795)). Qed.
Lemma lem2969208 (_31795 : int) : (term150 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2969200 _31795) (@lem2969207 _31795)). Qed.
Lemma lem2969209 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969210 (_31795 : int) : (term158 _31795) = (term159 _31795).
Proof. exact (MK_COMB (@lem2969209) (@lem2969208 _31795)). Qed.
Lemma lem2969212 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969213 : term168 = term169.
Proof. exact (@lem2969212 term86). Qed.
Lemma lem2969214 (_31795 : int) : (term189 _31795) = (term190 _31795).
Proof. exact (MK_COMB (@lem2969210 _31795) (@lem2969213)). Qed.
Lemma lem2969215 (_31795 : int) : (term188 _31795) = (term190 _31795).
Proof. exact (TRANS (@lem2969197 _31795) (@lem2969214 _31795)). Qed.
Lemma lem2969216 (_31794 : int) (_31795 : int) : (term198 _31794 _31795) = (term199 _31794 _31795).
Proof. exact (MK_COMB (@lem2969194 _31794) (@lem2969215 _31795)). Qed.
Lemma lem2969217 (_31794 : int) (_31795 : int) : (term197 _31794 _31795) = (term199 _31794 _31795).
Proof. exact (TRANS (@lem2969183 _31794 _31795) (@lem2969216 _31794 _31795)). Qed.
Lemma lem2969218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2969219 (_31794 : int) (_31795 : int) : (term200 _31794 _31795) = (term201 _31794 _31795).
Proof. exact (MK_COMB (@lem2969218) (@lem2969217 _31794 _31795)). Qed.
Lemma lem2969221 (x : int) (y : int) : (int_le x y) = (term135 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2969222 (_31795 : int) (_31794 : int) : (term202 _31795 _31794) = (term203 _31795 _31794).
Proof. exact (@lem2969221 (term204 _31795) _31794). Qed.
Lemma lem2969224 (x : int) (y : int) : (term145 x y) = (term146 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2969225 (_31795 : int) : (term205 _31795) = (term206 _31795).
Proof. exact (@lem2969224 (term113 _31795) term87). Qed.
Lemma lem2969227 (x : int) (y : int) : (term145 x y) = (term146 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2969228 (_31795 : int) : (term188 _31795) = (term189 _31795).
Proof. exact (@lem2969227 (term112 _31795) term87). Qed.
Lemma lem2969230 (x : int) (y : int) : (term148 x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2969231 (_31795 : int) : (term150 _31795) = (term151 _31795).
Proof. exact (@lem2969230 term152 _31795). Qed.
Lemma lem2969233 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969234 : term153 = term154.
Proof. exact (@lem2969233 term2). Qed.
Lemma lem2969235 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969236 : term155 = term156.
Proof. exact (MK_COMB (@lem2969235) (@lem2969234)). Qed.
Lemma lem2969237 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2969238 (_31795 : int) : (term151 _31795) = (term157 _31795).
Proof. exact (MK_COMB (@lem2969236) (@lem2969237 _31795)). Qed.
Lemma lem2969239 (_31795 : int) : (term150 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2969231 _31795) (@lem2969238 _31795)). Qed.
Lemma lem2969240 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969241 (_31795 : int) : (term158 _31795) = (term159 _31795).
Proof. exact (MK_COMB (@lem2969240) (@lem2969239 _31795)). Qed.
Lemma lem2969243 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969244 : term168 = term169.
Proof. exact (@lem2969243 term86). Qed.
Lemma lem2969245 (_31795 : int) : (term189 _31795) = (term190 _31795).
Proof. exact (MK_COMB (@lem2969241 _31795) (@lem2969244)). Qed.
Lemma lem2969246 (_31795 : int) : (term188 _31795) = (term190 _31795).
Proof. exact (TRANS (@lem2969228 _31795) (@lem2969245 _31795)). Qed.
Lemma lem2969247 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969248 (_31795 : int) : (term207 _31795) = (term208 _31795).
Proof. exact (MK_COMB (@lem2969247) (@lem2969246 _31795)). Qed.
Lemma lem2969250 (n : nat) : (term138 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2969251 : term168 = term169.
Proof. exact (@lem2969250 term86). Qed.
Lemma lem2969252 (_31795 : int) : (term206 _31795) = (term209 _31795).
Proof. exact (MK_COMB (@lem2969248 _31795) (@lem2969251)). Qed.
Lemma lem2969253 (_31795 : int) : (term205 _31795) = (term209 _31795).
Proof. exact (TRANS (@lem2969225 _31795) (@lem2969252 _31795)). Qed.
Lemma lem2969254 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2969255 (_31795 : int) : (term210 _31795) = (term211 _31795).
Proof. exact (MK_COMB (@lem2969254) (@lem2969253 _31795)). Qed.
Lemma lem2969256 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2969257 (_31795 : int) (_31794 : int) : (term203 _31795 _31794) = (term212 _31795 _31794).
Proof. exact (MK_COMB (@lem2969255 _31795) (@lem2969256 _31794)). Qed.
Lemma lem2969258 (_31795 : int) (_31794 : int) : (term202 _31795 _31794) = (term212 _31795 _31794).
Proof. exact (TRANS (@lem2969222 _31795 _31794) (@lem2969257 _31795 _31794)). Qed.
Lemma lem2969259 (_31795 : int) (_31794 : int) : (term196 _31795 _31794) = (term213 _31795 _31794).
Proof. exact (MK_COMB (@lem2969219 _31794 _31795) (@lem2969258 _31795 _31794)). Qed.
Lemma lem2969260 (_31795 : int) (_31794 : int) : (term195 _31794 _31795) = (term213 _31795 _31794).
Proof. exact (TRANS (@lem2969180 _31795 _31794) (@lem2969259 _31795 _31794)). Qed.
Lemma lem2969261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2969262 (_31795 : int) (_31794 : int) : (term214 _31794 _31795) = (term215 _31795 _31794).
Proof. exact (MK_COMB (@lem2969261) (@lem2969177 _31795 _31794)). Qed.
Lemma lem2969263 (_31795 : int) (_31794 : int) : (term111 _31794 _31795) = (term216 _31795 _31794).
Proof. exact (MK_COMB (@lem2969262 _31795 _31794) (@lem2969260 _31795 _31794)). Qed.
Lemma lem2969264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2969265 (_31794 : int) (_31795 : int) (_31796 : int) : (term115 _31794 _31795 _31796) = (term217 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2969264) (@lem2969114 _31794 _31795 _31796)). Qed.
Lemma lem2969266 (_31796 : int) (_31795 : int) (_31794 : int) : (term117 _31796 _31794 _31795) = (term218 _31796 _31795 _31794).
Proof. exact (MK_COMB (@lem2969265 _31794 _31795 _31796) (@lem2969263 _31795 _31794)). Qed.
Lemma lem2969267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2969268 (_31796 : int) : (term121 _31796) = (term219 _31796).
Proof. exact (MK_COMB (@lem2969267) (@lem2969059 _31796)). Qed.
Lemma lem2969269 (_31796 : int) (_31795 : int) (_31794 : int) : (term123 _31796 _31794 _31795) = (term220 _31796 _31795 _31794).
Proof. exact (MK_COMB (@lem2969268 _31796) (@lem2969266 _31796 _31795 _31794)). Qed.
Lemma lem2969270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2969271 (_31795 : int) : (term121 _31795) = (term219 _31795).
Proof. exact (MK_COMB (@lem2969270) (@lem2969046 _31795)). Qed.
Lemma lem2969272 (_31796 : int) (_31795 : int) (_31794 : int) : (term128 _31796 _31794 _31795) = (term221 _31796 _31795 _31794).
Proof. exact (MK_COMB (@lem2969271 _31795) (@lem2969269 _31796 _31795 _31794)). Qed.
Lemma lem2969273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2969274 (_31794 : int) : (term121 _31794) = (term219 _31794).
Proof. exact (MK_COMB (@lem2969273) (@lem2969033 _31794)). Qed.
Lemma lem2969275 (_31796 : int) (_31795 : int) (_31794 : int) : (term132 _31796 _31794 _31795) = (term222 _31796 _31795 _31794).
Proof. exact (MK_COMB (@lem2969274 _31794) (@lem2969272 _31796 _31795 _31794)). Qed.
Lemma lem2969276 (_31796 : int) (_31795 : int) (_31794 : int) : (term133 _31796 _31794 _31795) = (term222 _31796 _31795 _31794).
Proof. exact (TRANS (@lem2969020 _31796 _31794 _31795) (@lem2969275 _31796 _31795 _31794)). Qed.
Lemma lem2969280 (t : Prop) : (term223 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2969366 (_31796 : int) (_31795 : int) (_31794 : int) : (term224 _31796 _31795 _31794) = (term222 _31796 _31795 _31794).
Proof. exact (@lem2969280 (term222 _31796 _31795 _31794)). Qed.
Lemma lem2969367 (_31794 : int) : (term143 _31794) = (term225 _31794).
Proof. exact (@lem1988287 (real_of_int _31794) term140). Qed.
Lemma lem2969373 (_31794 : int) : (term226 _31794) = (term227 _31794).
Proof. exact (@lem1982792 (real_of_int _31794) term140). Qed.
Lemma lem2969375 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969376 : term140 = term229.
Proof. exact (@lem2969375 (NUMERAL 0)). Qed.
Lemma lem2969378 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969379 : term232 = term233.
Proof. exact (@lem2969378 term86). Qed.
Lemma lem2969380 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969381 : term234 = term235.
Proof. exact (MK_COMB (@lem2969380) (@lem2969379)). Qed.
Lemma lem2969382 : term236 = term237.
Proof. exact (MK_COMB (@lem2969381) (@lem2969376)). Qed.
Lemma lem2969383 : term237 = term238.
Proof. exact (@lem1981613 term232 term140 term169 term169). Qed.
Lemma lem2969385 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969386 : term241 = term242.
Proof. exact (@lem2969385 term86 term86). Qed.
Lemma lem2969387 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969388 : term244 = term86.
Proof. exact (EQ_MP (@lem2969387) (@lem940073)). Qed.
Lemma lem2969389 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969390 : term242 = term169.
Proof. exact (MK_COMB (@lem2969389) (@lem2969388)). Qed.
Lemma lem2969391 : term241 = term169.
Proof. exact (TRANS (@lem2969386) (@lem2969390)). Qed.
Lemma lem2969393 (x : nat) : (term245 x) = term140.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2969394 : term236 = term140.
Proof. exact (@lem2969393 term86). Qed.
Lemma lem2969395 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2969396 : term246 = term247.
Proof. exact (MK_COMB (@lem2969395) (@lem2969394)). Qed.
Lemma lem2969397 : term238 = term229.
Proof. exact (MK_COMB (@lem2969396) (@lem2969391)). Qed.
Lemma lem2969398 : term237 = term229.
Proof. exact (TRANS (@lem2969383) (@lem2969397)). Qed.
Lemma lem2969399 : term236 = term229.
Proof. exact (TRANS (@lem2969382) (@lem2969398)). Qed.
Lemma lem2969401 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2969402 : term229 = term140.
Proof. exact (@lem2969401 term140). Qed.
Lemma lem2969403 : term236 = term140.
Proof. exact (TRANS (@lem2969399) (@lem2969402)). Qed.
Lemma lem2969404 (_31794 : int) : (term170 _31794) = (term170 _31794).
Proof. exact (eq_refl (term170 _31794)). Qed.
Lemma lem2969405 (_31794 : int) : (term227 _31794) = (term249 _31794).
Proof. exact (MK_COMB (@lem2969404 _31794) (@lem2969403)). Qed.
Lemma lem2969406 (_31794 : int) : (term249 _31794) = (real_of_int _31794).
Proof. exact (@lem1982723 (real_of_int _31794)). Qed.
Lemma lem2969407 (_31794 : int) : (term227 _31794) = (real_of_int _31794).
Proof. exact (TRANS (@lem2969405 _31794) (@lem2969406 _31794)). Qed.
Lemma lem2969409 (_31794 : int) : (term226 _31794) = (real_of_int _31794).
Proof. exact (TRANS (@lem2969373 _31794) (@lem2969407 _31794)). Qed.
Lemma lem2969410 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2969411 (_31794 : int) : (term250 _31794) = (term251 _31794).
Proof. exact (MK_COMB (@lem2969410) (@lem2969409 _31794)). Qed.
Lemma lem2969412 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2969413 (_31794 : int) : (term225 _31794) = (term252 _31794).
Proof. exact (MK_COMB (@lem2969411 _31794) (@lem2969412)). Qed.
Lemma lem2969414 (_31794 : int) : (term143 _31794) = (term252 _31794).
Proof. exact (TRANS (@lem2969367 _31794) (@lem2969413 _31794)). Qed.
Lemma lem2969415 (_31795 : int) : (term143 _31795) = (term225 _31795).
Proof. exact (@lem1988287 (real_of_int _31795) term140). Qed.
Lemma lem2969421 (_31795 : int) : (term226 _31795) = (term227 _31795).
Proof. exact (@lem1982792 (real_of_int _31795) term140). Qed.
Lemma lem2969423 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969424 : term140 = term229.
Proof. exact (@lem2969423 (NUMERAL 0)). Qed.
Lemma lem2969426 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969427 : term232 = term233.
Proof. exact (@lem2969426 term86). Qed.
Lemma lem2969428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969429 : term234 = term235.
Proof. exact (MK_COMB (@lem2969428) (@lem2969427)). Qed.
Lemma lem2969430 : term236 = term237.
Proof. exact (MK_COMB (@lem2969429) (@lem2969424)). Qed.
Lemma lem2969431 : term237 = term238.
Proof. exact (@lem1981613 term232 term140 term169 term169). Qed.
Lemma lem2969433 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969434 : term241 = term242.
Proof. exact (@lem2969433 term86 term86). Qed.
Lemma lem2969435 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969436 : term244 = term86.
Proof. exact (EQ_MP (@lem2969435) (@lem940073)). Qed.
Lemma lem2969437 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969438 : term242 = term169.
Proof. exact (MK_COMB (@lem2969437) (@lem2969436)). Qed.
Lemma lem2969439 : term241 = term169.
Proof. exact (TRANS (@lem2969434) (@lem2969438)). Qed.
Lemma lem2969441 (x : nat) : (term245 x) = term140.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2969442 : term236 = term140.
Proof. exact (@lem2969441 term86). Qed.
Lemma lem2969443 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2969444 : term246 = term247.
Proof. exact (MK_COMB (@lem2969443) (@lem2969442)). Qed.
Lemma lem2969445 : term238 = term229.
Proof. exact (MK_COMB (@lem2969444) (@lem2969439)). Qed.
Lemma lem2969446 : term237 = term229.
Proof. exact (TRANS (@lem2969431) (@lem2969445)). Qed.
Lemma lem2969447 : term236 = term229.
Proof. exact (TRANS (@lem2969430) (@lem2969446)). Qed.
Lemma lem2969449 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2969450 : term229 = term140.
Proof. exact (@lem2969449 term140). Qed.
Lemma lem2969451 : term236 = term140.
Proof. exact (TRANS (@lem2969447) (@lem2969450)). Qed.
Lemma lem2969452 (_31795 : int) : (term170 _31795) = (term170 _31795).
Proof. exact (eq_refl (term170 _31795)). Qed.
Lemma lem2969453 (_31795 : int) : (term227 _31795) = (term249 _31795).
Proof. exact (MK_COMB (@lem2969452 _31795) (@lem2969451)). Qed.
Lemma lem2969454 (_31795 : int) : (term249 _31795) = (real_of_int _31795).
Proof. exact (@lem1982723 (real_of_int _31795)). Qed.
Lemma lem2969455 (_31795 : int) : (term227 _31795) = (real_of_int _31795).
Proof. exact (TRANS (@lem2969453 _31795) (@lem2969454 _31795)). Qed.
Lemma lem2969457 (_31795 : int) : (term226 _31795) = (real_of_int _31795).
Proof. exact (TRANS (@lem2969421 _31795) (@lem2969455 _31795)). Qed.
Lemma lem2969458 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2969459 (_31795 : int) : (term250 _31795) = (term251 _31795).
Proof. exact (MK_COMB (@lem2969458) (@lem2969457 _31795)). Qed.
Lemma lem2969460 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2969461 (_31795 : int) : (term225 _31795) = (term252 _31795).
Proof. exact (MK_COMB (@lem2969459 _31795) (@lem2969460)). Qed.
Lemma lem2969462 (_31795 : int) : (term143 _31795) = (term252 _31795).
Proof. exact (TRANS (@lem2969415 _31795) (@lem2969461 _31795)). Qed.
Lemma lem2969463 (_31796 : int) : (term143 _31796) = (term225 _31796).
Proof. exact (@lem1988287 (real_of_int _31796) term140). Qed.
Lemma lem2969469 (_31796 : int) : (term226 _31796) = (term227 _31796).
Proof. exact (@lem1982792 (real_of_int _31796) term140). Qed.
Lemma lem2969471 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969472 : term140 = term229.
Proof. exact (@lem2969471 (NUMERAL 0)). Qed.
Lemma lem2969474 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969475 : term232 = term233.
Proof. exact (@lem2969474 term86). Qed.
Lemma lem2969476 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969477 : term234 = term235.
Proof. exact (MK_COMB (@lem2969476) (@lem2969475)). Qed.
Lemma lem2969478 : term236 = term237.
Proof. exact (MK_COMB (@lem2969477) (@lem2969472)). Qed.
Lemma lem2969479 : term237 = term238.
Proof. exact (@lem1981613 term232 term140 term169 term169). Qed.
Lemma lem2969481 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969482 : term241 = term242.
Proof. exact (@lem2969481 term86 term86). Qed.
Lemma lem2969483 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969484 : term244 = term86.
Proof. exact (EQ_MP (@lem2969483) (@lem940073)). Qed.
Lemma lem2969485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969486 : term242 = term169.
Proof. exact (MK_COMB (@lem2969485) (@lem2969484)). Qed.
Lemma lem2969487 : term241 = term169.
Proof. exact (TRANS (@lem2969482) (@lem2969486)). Qed.
Lemma lem2969489 (x : nat) : (term245 x) = term140.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2969490 : term236 = term140.
Proof. exact (@lem2969489 term86). Qed.
Lemma lem2969491 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2969492 : term246 = term247.
Proof. exact (MK_COMB (@lem2969491) (@lem2969490)). Qed.
Lemma lem2969493 : term238 = term229.
Proof. exact (MK_COMB (@lem2969492) (@lem2969487)). Qed.
Lemma lem2969494 : term237 = term229.
Proof. exact (TRANS (@lem2969479) (@lem2969493)). Qed.
Lemma lem2969495 : term236 = term229.
Proof. exact (TRANS (@lem2969478) (@lem2969494)). Qed.
Lemma lem2969497 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2969498 : term229 = term140.
Proof. exact (@lem2969497 term140). Qed.
Lemma lem2969499 : term236 = term140.
Proof. exact (TRANS (@lem2969495) (@lem2969498)). Qed.
Lemma lem2969500 (_31796 : int) : (term170 _31796) = (term170 _31796).
Proof. exact (eq_refl (term170 _31796)). Qed.
Lemma lem2969501 (_31796 : int) : (term227 _31796) = (term249 _31796).
Proof. exact (MK_COMB (@lem2969500 _31796) (@lem2969499)). Qed.
Lemma lem2969502 (_31796 : int) : (term249 _31796) = (real_of_int _31796).
Proof. exact (@lem1982723 (real_of_int _31796)). Qed.
Lemma lem2969503 (_31796 : int) : (term227 _31796) = (real_of_int _31796).
Proof. exact (TRANS (@lem2969501 _31796) (@lem2969502 _31796)). Qed.
Lemma lem2969505 (_31796 : int) : (term226 _31796) = (real_of_int _31796).
Proof. exact (TRANS (@lem2969469 _31796) (@lem2969503 _31796)). Qed.
Lemma lem2969506 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2969507 (_31796 : int) : (term250 _31796) = (term251 _31796).
Proof. exact (MK_COMB (@lem2969506) (@lem2969505 _31796)). Qed.
Lemma lem2969508 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2969509 (_31796 : int) : (term225 _31796) = (term252 _31796).
Proof. exact (MK_COMB (@lem2969507 _31796) (@lem2969508)). Qed.
Lemma lem2969510 (_31796 : int) : (term143 _31796) = (term252 _31796).
Proof. exact (TRANS (@lem2969463 _31796) (@lem2969509 _31796)). Qed.
Lemma lem2969511 (_31794 : int) (_31795 : int) (_31796 : int) : ((real_of_int _31794) = (term160 _31795 _31796)) = ((term253 _31794 _31795 _31796) = term140).
Proof. exact (@lem1988293 (real_of_int _31794) (term160 _31795 _31796)). Qed.
Lemma lem2969529 (_31794 : int) (_31795 : int) (_31796 : int) : (term253 _31794 _31795 _31796) = (term254 _31794 _31795 _31796).
Proof. exact (@lem1982792 (real_of_int _31794) (term160 _31795 _31796)). Qed.
Lemma lem2969530 (_31795 : int) (_31796 : int) : (term255 _31795 _31796) = (term256 _31795 _31796).
Proof. exact (@lem1982781 (term157 _31795) term232 (real_of_int _31796)). Qed.
Lemma lem2969531 (_31796 : int) : (term257 _31796) = (term257 _31796).
Proof. exact (eq_refl (term257 _31796)). Qed.
Lemma lem2969532 (_31795 : int) : (term258 _31795) = (term259 _31795).
Proof. exact (@lem1982749 term232 term154 (real_of_int _31795)). Qed.
Lemma lem2969534 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969535 : term154 = term260.
Proof. exact (@lem2969534 term2). Qed.
Lemma lem2969537 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969538 : term232 = term233.
Proof. exact (@lem2969537 term86). Qed.
Lemma lem2969539 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969540 : term234 = term235.
Proof. exact (MK_COMB (@lem2969539) (@lem2969538)). Qed.
Lemma lem2969541 : term261 = term262.
Proof. exact (MK_COMB (@lem2969540) (@lem2969535)). Qed.
Lemma lem2969542 : term262 = term263.
Proof. exact (@lem1981613 term232 term154 term169 term169). Qed.
Lemma lem2969544 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969545 : term241 = term242.
Proof. exact (@lem2969544 term86 term86). Qed.
Lemma lem2969546 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969547 : term244 = term86.
Proof. exact (EQ_MP (@lem2969546) (@lem940073)). Qed.
Lemma lem2969548 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969549 : term242 = term169.
Proof. exact (MK_COMB (@lem2969548) (@lem2969547)). Qed.
Lemma lem2969550 : term241 = term169.
Proof. exact (TRANS (@lem2969545) (@lem2969549)). Qed.
Lemma lem2969552 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2969553 : term261 = term266.
Proof. exact (@lem2969552 term86 term2). Qed.
Lemma lem2969554 : term267 = term27.
Proof. exact (@lem996238 term27). Qed.
Lemma lem2969555 : (term267 = term27) = (term268 = term2).
Proof. exact (@lem1007663 (BIT1 0) term27 term27). Qed.
Lemma lem2969556 : term268 = term2.
Proof. exact (EQ_MP (@lem2969555) (@lem2969554)). Qed.
Lemma lem2969557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969558 : term269 = term154.
Proof. exact (MK_COMB (@lem2969557) (@lem2969556)). Qed.
Lemma lem2969559 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2969560 : term266 = term270.
Proof. exact (MK_COMB (@lem2969559) (@lem2969558)). Qed.
Lemma lem2969561 : term261 = term270.
Proof. exact (TRANS (@lem2969553) (@lem2969560)). Qed.
Lemma lem2969562 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2969563 : term271 = term272.
Proof. exact (MK_COMB (@lem2969562) (@lem2969561)). Qed.
Lemma lem2969564 : term263 = term273.
Proof. exact (MK_COMB (@lem2969563) (@lem2969550)). Qed.
Lemma lem2969565 : term262 = term273.
Proof. exact (TRANS (@lem2969542) (@lem2969564)). Qed.
Lemma lem2969566 : term261 = term273.
Proof. exact (TRANS (@lem2969541) (@lem2969565)). Qed.
Lemma lem2969568 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2969569 : term273 = term270.
Proof. exact (@lem2969568 term270). Qed.
Lemma lem2969570 : term261 = term270.
Proof. exact (TRANS (@lem2969566) (@lem2969569)). Qed.
Lemma lem2969571 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969572 : term274 = term275.
Proof. exact (MK_COMB (@lem2969571) (@lem2969570)). Qed.
Lemma lem2969573 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2969574 (_31795 : int) : (term259 _31795) = (term276 _31795).
Proof. exact (MK_COMB (@lem2969572) (@lem2969573 _31795)). Qed.
Lemma lem2969575 (_31795 : int) : (term258 _31795) = (term276 _31795).
Proof. exact (TRANS (@lem2969532 _31795) (@lem2969574 _31795)). Qed.
Lemma lem2969576 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969577 (_31795 : int) : (term277 _31795) = (term278 _31795).
Proof. exact (MK_COMB (@lem2969576) (@lem2969575 _31795)). Qed.
Lemma lem2969578 (_31795 : int) (_31796 : int) : (term256 _31795 _31796) = (term279 _31795 _31796).
Proof. exact (MK_COMB (@lem2969577 _31795) (@lem2969531 _31796)). Qed.
Lemma lem2969579 (_31795 : int) (_31796 : int) : (term255 _31795 _31796) = (term279 _31795 _31796).
Proof. exact (TRANS (@lem2969530 _31795 _31796) (@lem2969578 _31795 _31796)). Qed.
Lemma lem2969580 (_31794 : int) : (term170 _31794) = (term170 _31794).
Proof. exact (eq_refl (term170 _31794)). Qed.
Lemma lem2969583 (_31794 : int) (_31795 : int) (_31796 : int) : (term254 _31794 _31795 _31796) = (term280 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2969580 _31794) (@lem2969579 _31795 _31796)). Qed.
Lemma lem2969585 (_31794 : int) (_31795 : int) (_31796 : int) : (term253 _31794 _31795 _31796) = (term280 _31794 _31795 _31796).
Proof. exact (TRANS (@lem2969529 _31794 _31795 _31796) (@lem2969583 _31794 _31795 _31796)). Qed.
Lemma lem2969586 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2969587 (_31794 : int) (_31795 : int) (_31796 : int) : (term281 _31794 _31795 _31796) = (term282 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2969586) (@lem2969585 _31794 _31795 _31796)). Qed.
Lemma lem2969588 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2969589 (_31794 : int) (_31795 : int) (_31796 : int) : ((term253 _31794 _31795 _31796) = term140) = ((term280 _31794 _31795 _31796) = term140).
Proof. exact (MK_COMB (@lem2969587 _31794 _31795 _31796) (@lem2969588)). Qed.
Lemma lem2969590 (_31794 : int) (_31795 : int) (_31796 : int) : ((real_of_int _31794) = (term160 _31795 _31796)) = ((term280 _31794 _31795 _31796) = term140).
Proof. exact (TRANS (@lem2969511 _31794 _31795 _31796) (@lem2969589 _31794 _31795 _31796)). Qed.
Lemma lem2969591 (_31796 : int) : (term174 _31796) = (term283 _31796).
Proof. exact (@lem1988287 term154 (term171 _31796)). Qed.
Lemma lem2969603 (_31796 : int) : (term284 _31796) = (term285 _31796).
Proof. exact (@lem1982792 term154 (term171 _31796)). Qed.
Lemma lem2969604 (_31796 : int) : (term286 _31796) = (term287 _31796).
Proof. exact (@lem1982781 (real_of_int _31796) term232 term169). Qed.
Lemma lem2969606 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969607 : term169 = term288.
Proof. exact (@lem2969606 term86). Qed.
Lemma lem2969609 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969610 : term232 = term233.
Proof. exact (@lem2969609 term86). Qed.
Lemma lem2969611 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969612 : term234 = term235.
Proof. exact (MK_COMB (@lem2969611) (@lem2969610)). Qed.
Lemma lem2969613 : term289 = term290.
Proof. exact (MK_COMB (@lem2969612) (@lem2969607)). Qed.
Lemma lem2969614 : term290 = term291.
Proof. exact (@lem1981613 term232 term169 term169 term169). Qed.
Lemma lem2969616 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969617 : term241 = term242.
Proof. exact (@lem2969616 term86 term86). Qed.
Lemma lem2969618 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969619 : term244 = term86.
Proof. exact (EQ_MP (@lem2969618) (@lem940073)). Qed.
Lemma lem2969620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969621 : term242 = term169.
Proof. exact (MK_COMB (@lem2969620) (@lem2969619)). Qed.
Lemma lem2969622 : term241 = term169.
Proof. exact (TRANS (@lem2969617) (@lem2969621)). Qed.
Lemma lem2969624 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2969625 : term289 = term292.
Proof. exact (@lem2969624 term86 term86). Qed.
Lemma lem2969626 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969627 : term244 = term86.
Proof. exact (EQ_MP (@lem2969626) (@lem940073)). Qed.
Lemma lem2969628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969629 : term242 = term169.
Proof. exact (MK_COMB (@lem2969628) (@lem2969627)). Qed.
Lemma lem2969630 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2969631 : term292 = term232.
Proof. exact (MK_COMB (@lem2969630) (@lem2969629)). Qed.
Lemma lem2969632 : term289 = term232.
Proof. exact (TRANS (@lem2969625) (@lem2969631)). Qed.
Lemma lem2969633 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2969634 : term293 = term294.
Proof. exact (MK_COMB (@lem2969633) (@lem2969632)). Qed.
Lemma lem2969635 : term291 = term233.
Proof. exact (MK_COMB (@lem2969634) (@lem2969622)). Qed.
Lemma lem2969636 : term290 = term233.
Proof. exact (TRANS (@lem2969614) (@lem2969635)). Qed.
Lemma lem2969637 : term289 = term233.
Proof. exact (TRANS (@lem2969613) (@lem2969636)). Qed.
Lemma lem2969639 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2969640 : term233 = term232.
Proof. exact (@lem2969639 term232). Qed.
Lemma lem2969641 : term289 = term232.
Proof. exact (TRANS (@lem2969637) (@lem2969640)). Qed.
Lemma lem2969644 (_31796 : int) : (term295 _31796) = (term295 _31796).
Proof. exact (eq_refl (term295 _31796)). Qed.
Lemma lem2969645 (_31796 : int) : (term287 _31796) = (term296 _31796).
Proof. exact (MK_COMB (@lem2969644 _31796) (@lem2969641)). Qed.
Lemma lem2969646 (_31796 : int) : (term286 _31796) = (term296 _31796).
Proof. exact (TRANS (@lem2969604 _31796) (@lem2969645 _31796)). Qed.
Lemma lem2969647 : term297 = term297.
Proof. exact (eq_refl term297). Qed.
Lemma lem2969648 (_31796 : int) : (term285 _31796) = (term298 _31796).
Proof. exact (MK_COMB (@lem2969647) (@lem2969646 _31796)). Qed.
Lemma lem2969649 (_31796 : int) : (term298 _31796) = (term299 _31796).
Proof. exact (@lem1982757 (term257 _31796) term154 term232). Qed.
Lemma lem2969651 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969652 : term232 = term233.
Proof. exact (@lem2969651 term86). Qed.
Lemma lem2969654 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969655 : term154 = term260.
Proof. exact (@lem2969654 term2). Qed.
Lemma lem2969656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969657 : term297 = term300.
Proof. exact (MK_COMB (@lem2969656) (@lem2969655)). Qed.
Lemma lem2969658 : term301 = term302.
Proof. exact (MK_COMB (@lem2969657) (@lem2969652)). Qed.
Lemma lem2969659 : term303.
Proof. exact (@lem1981473 term154 term169 term232 term169 term169 term169). Qed.
Lemma lem2969661 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2969662 : term305 = term306.
Proof. exact (@lem2969661 (NUMERAL 0) term86). Qed.
Lemma lem2969663 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2969664 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2969665 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2969664 h1) (fun h1 : term306 = True => @lem2969663)). Qed.
Lemma lem2969666 : term306 = True.
Proof. exact (EQ_MP (@lem2969665) (@lem2969663)). Qed.
Lemma lem2969667 : term305 = True.
Proof. exact (TRANS (@lem2969662) (@lem2969666)). Qed.
Lemma lem2969668 : True = term305.
Proof. exact (SYM (@lem2969667)). Qed.
Lemma lem2969669 : term305.
Proof. exact (EQ_MP (@lem2969668) (@lem0)). Qed.
Lemma lem2969670 : term308.
Proof. exact (@lem2969659 (@lem2969669)). Qed.
Lemma lem2969672 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2969673 : term305 = term306.
Proof. exact (@lem2969672 (NUMERAL 0) term86). Qed.
Lemma lem2969674 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2969675 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2969676 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2969675 h1) (fun h1 : term306 = True => @lem2969674)). Qed.
Lemma lem2969677 : term306 = True.
Proof. exact (EQ_MP (@lem2969676) (@lem2969674)). Qed.
Lemma lem2969678 : term305 = True.
Proof. exact (TRANS (@lem2969673) (@lem2969677)). Qed.
Lemma lem2969679 : True = term305.
Proof. exact (SYM (@lem2969678)). Qed.
Lemma lem2969680 : term305.
Proof. exact (EQ_MP (@lem2969679) (@lem0)). Qed.
Lemma lem2969681 : term309.
Proof. exact (@lem2969670 (@lem2969680)). Qed.
Lemma lem2969683 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2969684 : term305 = term306.
Proof. exact (@lem2969683 (NUMERAL 0) term86). Qed.
Lemma lem2969685 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2969686 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2969687 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2969686 h1) (fun h1 : term306 = True => @lem2969685)). Qed.
Lemma lem2969688 : term306 = True.
Proof. exact (EQ_MP (@lem2969687) (@lem2969685)). Qed.
Lemma lem2969689 : term305 = True.
Proof. exact (TRANS (@lem2969684) (@lem2969688)). Qed.
Lemma lem2969690 : True = term305.
Proof. exact (SYM (@lem2969689)). Qed.
Lemma lem2969691 : term305.
Proof. exact (EQ_MP (@lem2969690) (@lem0)). Qed.
Lemma lem2969692 : term310.
Proof. exact (@lem2969681 (@lem2969691)). Qed.
Lemma lem2969694 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2969695 : term289 = term292.
Proof. exact (@lem2969694 term86 term86). Qed.
Lemma lem2969696 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969697 : term244 = term86.
Proof. exact (EQ_MP (@lem2969696) (@lem940073)). Qed.
Lemma lem2969698 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969699 : term242 = term169.
Proof. exact (MK_COMB (@lem2969698) (@lem2969697)). Qed.
Lemma lem2969700 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2969701 : term292 = term232.
Proof. exact (MK_COMB (@lem2969700) (@lem2969699)). Qed.
Lemma lem2969702 : term289 = term232.
Proof. exact (TRANS (@lem2969695) (@lem2969701)). Qed.
Lemma lem2969704 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969705 : term311 = term312.
Proof. exact (@lem2969704 term2 term86). Qed.
Lemma lem2969706 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2969707 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2969708 : term314 = term2.
Proof. exact (EQ_MP (@lem2969707) (@lem2969706)). Qed.
Lemma lem2969709 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969710 : term312 = term154.
Proof. exact (MK_COMB (@lem2969709) (@lem2969708)). Qed.
Lemma lem2969711 : term311 = term154.
Proof. exact (TRANS (@lem2969705) (@lem2969710)). Qed.
Lemma lem2969712 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969713 : term315 = term297.
Proof. exact (MK_COMB (@lem2969712) (@lem2969711)). Qed.
Lemma lem2969714 : term316 = term301.
Proof. exact (MK_COMB (@lem2969713) (@lem2969702)). Qed.
Lemma lem2969717 : term317 = term169.
Proof. exact (@lem1367769 term86 term86). Qed.
Lemma lem2969718 : term318 = term27.
Proof. exact (@lem706885). Qed.
Lemma lem2969719 : (term318 = term27) = (term319 = term2).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term27). Qed.
Lemma lem2969720 : term319 = term2.
Proof. exact (EQ_MP (@lem2969719) (@lem2969718)). Qed.
Lemma lem2969721 : term2 = term319.
Proof. exact (SYM (@lem2969720)). Qed.
Lemma lem2969722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969723 : term154 = term320.
Proof. exact (MK_COMB (@lem2969722) (@lem2969721)). Qed.
Lemma lem2969724 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969725 : term297 = term321.
Proof. exact (MK_COMB (@lem2969724) (@lem2969723)). Qed.
Lemma lem2969726 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem2969727 : term301 = term317.
Proof. exact (MK_COMB (@lem2969725) (@lem2969726)). Qed.
Lemma lem2969728 : term301 = term169.
Proof. exact (TRANS (@lem2969727) (@lem2969717)). Qed.
Lemma lem2969729 : term316 = term169.
Proof. exact (TRANS (@lem2969714) (@lem2969728)). Qed.
Lemma lem2969730 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969731 : term322 = term323.
Proof. exact (MK_COMB (@lem2969730) (@lem2969729)). Qed.
Lemma lem2969732 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2969733 : term324 = term241.
Proof. exact (MK_COMB (@lem2969731) (@lem2969732)). Qed.
Lemma lem2969735 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969736 : term241 = term242.
Proof. exact (@lem2969735 term86 term86). Qed.
Lemma lem2969737 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969738 : term244 = term86.
Proof. exact (EQ_MP (@lem2969737) (@lem940073)). Qed.
Lemma lem2969739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969740 : term242 = term169.
Proof. exact (MK_COMB (@lem2969739) (@lem2969738)). Qed.
Lemma lem2969741 : term241 = term169.
Proof. exact (TRANS (@lem2969736) (@lem2969740)). Qed.
Lemma lem2969742 : term324 = term169.
Proof. exact (TRANS (@lem2969733) (@lem2969741)). Qed.
Lemma lem2969744 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969745 : term241 = term242.
Proof. exact (@lem2969744 term86 term86). Qed.
Lemma lem2969746 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969747 : term244 = term86.
Proof. exact (EQ_MP (@lem2969746) (@lem940073)). Qed.
Lemma lem2969748 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969749 : term242 = term169.
Proof. exact (MK_COMB (@lem2969748) (@lem2969747)). Qed.
Lemma lem2969750 : term241 = term169.
Proof. exact (TRANS (@lem2969745) (@lem2969749)). Qed.
Lemma lem2969751 : term323 = term323.
Proof. exact (eq_refl term323). Qed.
Lemma lem2969752 : term325 = term241.
Proof. exact (MK_COMB (@lem2969751) (@lem2969750)). Qed.
Lemma lem2969754 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969755 : term241 = term242.
Proof. exact (@lem2969754 term86 term86). Qed.
Lemma lem2969756 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969757 : term244 = term86.
Proof. exact (EQ_MP (@lem2969756) (@lem940073)). Qed.
Lemma lem2969758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969759 : term242 = term169.
Proof. exact (MK_COMB (@lem2969758) (@lem2969757)). Qed.
Lemma lem2969760 : term241 = term169.
Proof. exact (TRANS (@lem2969755) (@lem2969759)). Qed.
Lemma lem2969761 : term325 = term169.
Proof. exact (TRANS (@lem2969752) (@lem2969760)). Qed.
Lemma lem2969762 : term169 = term325.
Proof. exact (SYM (@lem2969761)). Qed.
Lemma lem2969763 : term324 = term325.
Proof. exact (TRANS (@lem2969742) (@lem2969762)). Qed.
Lemma lem2969764 : term302 = term288.
Proof. exact (@lem2969692 (@lem2969763)). Qed.
Lemma lem2969765 : term301 = term288.
Proof. exact (TRANS (@lem2969658) (@lem2969764)). Qed.
Lemma lem2969767 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2969768 : term288 = term169.
Proof. exact (@lem2969767 term169). Qed.
Lemma lem2969769 : term301 = term169.
Proof. exact (TRANS (@lem2969765) (@lem2969768)). Qed.
Lemma lem2969770 (_31796 : int) : (term295 _31796) = (term295 _31796).
Proof. exact (eq_refl (term295 _31796)). Qed.
Lemma lem2969771 (_31796 : int) : (term299 _31796) = (term326 _31796).
Proof. exact (MK_COMB (@lem2969770 _31796) (@lem2969769)). Qed.
Lemma lem2969772 (_31796 : int) : (term298 _31796) = (term326 _31796).
Proof. exact (TRANS (@lem2969649 _31796) (@lem2969771 _31796)). Qed.
Lemma lem2969773 (_31796 : int) : (term285 _31796) = (term326 _31796).
Proof. exact (TRANS (@lem2969648 _31796) (@lem2969772 _31796)). Qed.
Lemma lem2969775 (_31796 : int) : (term284 _31796) = (term326 _31796).
Proof. exact (TRANS (@lem2969603 _31796) (@lem2969773 _31796)). Qed.
Lemma lem2969776 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2969777 (_31796 : int) : (term327 _31796) = (term328 _31796).
Proof. exact (MK_COMB (@lem2969776) (@lem2969775 _31796)). Qed.
Lemma lem2969778 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2969779 (_31796 : int) : (term283 _31796) = (term329 _31796).
Proof. exact (MK_COMB (@lem2969777 _31796) (@lem2969778)). Qed.
Lemma lem2969780 (_31796 : int) : (term174 _31796) = (term329 _31796).
Proof. exact (TRANS (@lem2969591 _31796) (@lem2969779 _31796)). Qed.
Lemma lem2969781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2969782 (_31794 : int) (_31795 : int) (_31796 : int) : (term175 _31794 _31795 _31796) = (term330 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2969781) (@lem2969590 _31794 _31795 _31796)). Qed.
Lemma lem2969783 (_31794 : int) (_31795 : int) (_31796 : int) : (term176 _31794 _31795 _31796) = (term331 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2969782 _31794 _31795 _31796) (@lem2969780 _31796)). Qed.
Lemma lem2969784 (_31795 : int) (_31794 : int) : (term183 _31794 _31795) = (term332 _31795 _31794).
Proof. exact (@lem1988287 (term157 _31795) (term171 _31794)). Qed.
Lemma lem2969802 (_31795 : int) (_31794 : int) : (term333 _31795 _31794) = (term334 _31795 _31794).
Proof. exact (@lem1982792 (term157 _31795) (term171 _31794)). Qed.
Lemma lem2969803 (_31794 : int) : (term286 _31794) = (term287 _31794).
Proof. exact (@lem1982781 (real_of_int _31794) term232 term169). Qed.
Lemma lem2969805 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969806 : term169 = term288.
Proof. exact (@lem2969805 term86). Qed.
Lemma lem2969808 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969809 : term232 = term233.
Proof. exact (@lem2969808 term86). Qed.
Lemma lem2969810 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969811 : term234 = term235.
Proof. exact (MK_COMB (@lem2969810) (@lem2969809)). Qed.
Lemma lem2969812 : term289 = term290.
Proof. exact (MK_COMB (@lem2969811) (@lem2969806)). Qed.
Lemma lem2969813 : term290 = term291.
Proof. exact (@lem1981613 term232 term169 term169 term169). Qed.
Lemma lem2969815 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969816 : term241 = term242.
Proof. exact (@lem2969815 term86 term86). Qed.
Lemma lem2969817 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969818 : term244 = term86.
Proof. exact (EQ_MP (@lem2969817) (@lem940073)). Qed.
Lemma lem2969819 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969820 : term242 = term169.
Proof. exact (MK_COMB (@lem2969819) (@lem2969818)). Qed.
Lemma lem2969821 : term241 = term169.
Proof. exact (TRANS (@lem2969816) (@lem2969820)). Qed.
Lemma lem2969823 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2969824 : term289 = term292.
Proof. exact (@lem2969823 term86 term86). Qed.
Lemma lem2969825 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969826 : term244 = term86.
Proof. exact (EQ_MP (@lem2969825) (@lem940073)). Qed.
Lemma lem2969827 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969828 : term242 = term169.
Proof. exact (MK_COMB (@lem2969827) (@lem2969826)). Qed.
Lemma lem2969829 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2969830 : term292 = term232.
Proof. exact (MK_COMB (@lem2969829) (@lem2969828)). Qed.
Lemma lem2969831 : term289 = term232.
Proof. exact (TRANS (@lem2969824) (@lem2969830)). Qed.
Lemma lem2969832 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2969833 : term293 = term294.
Proof. exact (MK_COMB (@lem2969832) (@lem2969831)). Qed.
Lemma lem2969834 : term291 = term233.
Proof. exact (MK_COMB (@lem2969833) (@lem2969821)). Qed.
Lemma lem2969835 : term290 = term233.
Proof. exact (TRANS (@lem2969813) (@lem2969834)). Qed.
Lemma lem2969836 : term289 = term233.
Proof. exact (TRANS (@lem2969812) (@lem2969835)). Qed.
Lemma lem2969838 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2969839 : term233 = term232.
Proof. exact (@lem2969838 term232). Qed.
Lemma lem2969840 : term289 = term232.
Proof. exact (TRANS (@lem2969836) (@lem2969839)). Qed.
Lemma lem2969843 (_31794 : int) : (term295 _31794) = (term295 _31794).
Proof. exact (eq_refl (term295 _31794)). Qed.
Lemma lem2969844 (_31794 : int) : (term287 _31794) = (term296 _31794).
Proof. exact (MK_COMB (@lem2969843 _31794) (@lem2969840)). Qed.
Lemma lem2969845 (_31794 : int) : (term286 _31794) = (term296 _31794).
Proof. exact (TRANS (@lem2969803 _31794) (@lem2969844 _31794)). Qed.
Lemma lem2969846 (_31795 : int) : (term159 _31795) = (term159 _31795).
Proof. exact (eq_refl (term159 _31795)). Qed.
Lemma lem2969847 (_31795 : int) (_31794 : int) : (term334 _31795 _31794) = (term335 _31795 _31794).
Proof. exact (MK_COMB (@lem2969846 _31795) (@lem2969845 _31794)). Qed.
Lemma lem2969852 (_31794 : int) (_31795 : int) : (term335 _31795 _31794) = (term336 _31794 _31795).
Proof. exact (@lem1982757 (term257 _31794) (term157 _31795) term232). Qed.
Lemma lem2969853 (_31794 : int) (_31795 : int) : (term334 _31795 _31794) = (term336 _31794 _31795).
Proof. exact (TRANS (@lem2969847 _31795 _31794) (@lem2969852 _31794 _31795)). Qed.
Lemma lem2969855 (_31794 : int) (_31795 : int) : (term333 _31795 _31794) = (term336 _31794 _31795).
Proof. exact (TRANS (@lem2969802 _31795 _31794) (@lem2969853 _31794 _31795)). Qed.
Lemma lem2969856 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2969857 (_31794 : int) (_31795 : int) : (term337 _31795 _31794) = (term338 _31794 _31795).
Proof. exact (MK_COMB (@lem2969856) (@lem2969855 _31794 _31795)). Qed.
Lemma lem2969858 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2969859 (_31794 : int) (_31795 : int) : (term332 _31795 _31794) = (term339 _31794 _31795).
Proof. exact (MK_COMB (@lem2969857 _31794 _31795) (@lem2969858)). Qed.
Lemma lem2969860 (_31794 : int) (_31795 : int) : (term183 _31794 _31795) = (term339 _31794 _31795).
Proof. exact (TRANS (@lem2969784 _31795 _31794) (@lem2969859 _31794 _31795)). Qed.
Lemma lem2969861 (_31794 : int) (_31795 : int) : (term193 _31795 _31794) = (term340 _31794 _31795).
Proof. exact (@lem1988287 (real_of_int _31794) (term190 _31795)). Qed.
Lemma lem2969879 (_31794 : int) (_31795 : int) : (term341 _31794 _31795) = (term342 _31794 _31795).
Proof. exact (@lem1982792 (real_of_int _31794) (term190 _31795)). Qed.
Lemma lem2969880 (_31795 : int) : (term343 _31795) = (term344 _31795).
Proof. exact (@lem1982781 (term157 _31795) term232 term169). Qed.
Lemma lem2969882 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969883 : term169 = term288.
Proof. exact (@lem2969882 term86). Qed.
Lemma lem2969885 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969886 : term232 = term233.
Proof. exact (@lem2969885 term86). Qed.
Lemma lem2969887 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969888 : term234 = term235.
Proof. exact (MK_COMB (@lem2969887) (@lem2969886)). Qed.
Lemma lem2969889 : term289 = term290.
Proof. exact (MK_COMB (@lem2969888) (@lem2969883)). Qed.
Lemma lem2969890 : term290 = term291.
Proof. exact (@lem1981613 term232 term169 term169 term169). Qed.
Lemma lem2969892 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969893 : term241 = term242.
Proof. exact (@lem2969892 term86 term86). Qed.
Lemma lem2969894 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969895 : term244 = term86.
Proof. exact (EQ_MP (@lem2969894) (@lem940073)). Qed.
Lemma lem2969896 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969897 : term242 = term169.
Proof. exact (MK_COMB (@lem2969896) (@lem2969895)). Qed.
Lemma lem2969898 : term241 = term169.
Proof. exact (TRANS (@lem2969893) (@lem2969897)). Qed.
Lemma lem2969900 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2969901 : term289 = term292.
Proof. exact (@lem2969900 term86 term86). Qed.
Lemma lem2969902 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969903 : term244 = term86.
Proof. exact (EQ_MP (@lem2969902) (@lem940073)). Qed.
Lemma lem2969904 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969905 : term242 = term169.
Proof. exact (MK_COMB (@lem2969904) (@lem2969903)). Qed.
Lemma lem2969906 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2969907 : term292 = term232.
Proof. exact (MK_COMB (@lem2969906) (@lem2969905)). Qed.
Lemma lem2969908 : term289 = term232.
Proof. exact (TRANS (@lem2969901) (@lem2969907)). Qed.
Lemma lem2969909 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2969910 : term293 = term294.
Proof. exact (MK_COMB (@lem2969909) (@lem2969908)). Qed.
Lemma lem2969911 : term291 = term233.
Proof. exact (MK_COMB (@lem2969910) (@lem2969898)). Qed.
Lemma lem2969912 : term290 = term233.
Proof. exact (TRANS (@lem2969890) (@lem2969911)). Qed.
Lemma lem2969913 : term289 = term233.
Proof. exact (TRANS (@lem2969889) (@lem2969912)). Qed.
Lemma lem2969915 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2969916 : term233 = term232.
Proof. exact (@lem2969915 term232). Qed.
Lemma lem2969917 : term289 = term232.
Proof. exact (TRANS (@lem2969913) (@lem2969916)). Qed.
Lemma lem2969918 (_31795 : int) : (term258 _31795) = (term259 _31795).
Proof. exact (@lem1982749 term232 term154 (real_of_int _31795)). Qed.
Lemma lem2969920 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2969921 : term154 = term260.
Proof. exact (@lem2969920 term2). Qed.
Lemma lem2969923 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2969924 : term232 = term233.
Proof. exact (@lem2969923 term86). Qed.
Lemma lem2969925 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969926 : term234 = term235.
Proof. exact (MK_COMB (@lem2969925) (@lem2969924)). Qed.
Lemma lem2969927 : term261 = term262.
Proof. exact (MK_COMB (@lem2969926) (@lem2969921)). Qed.
Lemma lem2969928 : term262 = term263.
Proof. exact (@lem1981613 term232 term154 term169 term169). Qed.
Lemma lem2969930 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2969931 : term241 = term242.
Proof. exact (@lem2969930 term86 term86). Qed.
Lemma lem2969932 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2969933 : term244 = term86.
Proof. exact (EQ_MP (@lem2969932) (@lem940073)). Qed.
Lemma lem2969934 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969935 : term242 = term169.
Proof. exact (MK_COMB (@lem2969934) (@lem2969933)). Qed.
Lemma lem2969936 : term241 = term169.
Proof. exact (TRANS (@lem2969931) (@lem2969935)). Qed.
Lemma lem2969938 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2969939 : term261 = term266.
Proof. exact (@lem2969938 term86 term2). Qed.
Lemma lem2969940 : term267 = term27.
Proof. exact (@lem996238 term27). Qed.
Lemma lem2969941 : (term267 = term27) = (term268 = term2).
Proof. exact (@lem1007663 (BIT1 0) term27 term27). Qed.
Lemma lem2969942 : term268 = term2.
Proof. exact (EQ_MP (@lem2969941) (@lem2969940)). Qed.
Lemma lem2969943 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2969944 : term269 = term154.
Proof. exact (MK_COMB (@lem2969943) (@lem2969942)). Qed.
Lemma lem2969945 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2969946 : term266 = term270.
Proof. exact (MK_COMB (@lem2969945) (@lem2969944)). Qed.
Lemma lem2969947 : term261 = term270.
Proof. exact (TRANS (@lem2969939) (@lem2969946)). Qed.
Lemma lem2969948 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2969949 : term271 = term272.
Proof. exact (MK_COMB (@lem2969948) (@lem2969947)). Qed.
Lemma lem2969950 : term263 = term273.
Proof. exact (MK_COMB (@lem2969949) (@lem2969936)). Qed.
Lemma lem2969951 : term262 = term273.
Proof. exact (TRANS (@lem2969928) (@lem2969950)). Qed.
Lemma lem2969952 : term261 = term273.
Proof. exact (TRANS (@lem2969927) (@lem2969951)). Qed.
Lemma lem2969954 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2969955 : term273 = term270.
Proof. exact (@lem2969954 term270). Qed.
Lemma lem2969956 : term261 = term270.
Proof. exact (TRANS (@lem2969952) (@lem2969955)). Qed.
Lemma lem2969957 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2969958 : term274 = term275.
Proof. exact (MK_COMB (@lem2969957) (@lem2969956)). Qed.
Lemma lem2969959 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2969960 (_31795 : int) : (term259 _31795) = (term276 _31795).
Proof. exact (MK_COMB (@lem2969958) (@lem2969959 _31795)). Qed.
Lemma lem2969961 (_31795 : int) : (term258 _31795) = (term276 _31795).
Proof. exact (TRANS (@lem2969918 _31795) (@lem2969960 _31795)). Qed.
Lemma lem2969962 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2969963 (_31795 : int) : (term277 _31795) = (term278 _31795).
Proof. exact (MK_COMB (@lem2969962) (@lem2969961 _31795)). Qed.
Lemma lem2969964 (_31795 : int) : (term344 _31795) = (term345 _31795).
Proof. exact (MK_COMB (@lem2969963 _31795) (@lem2969917)). Qed.
Lemma lem2969965 (_31795 : int) : (term343 _31795) = (term345 _31795).
Proof. exact (TRANS (@lem2969880 _31795) (@lem2969964 _31795)). Qed.
Lemma lem2969966 (_31794 : int) : (term170 _31794) = (term170 _31794).
Proof. exact (eq_refl (term170 _31794)). Qed.
Lemma lem2969969 (_31794 : int) (_31795 : int) : (term342 _31794 _31795) = (term346 _31794 _31795).
Proof. exact (MK_COMB (@lem2969966 _31794) (@lem2969965 _31795)). Qed.
Lemma lem2969971 (_31794 : int) (_31795 : int) : (term341 _31794 _31795) = (term346 _31794 _31795).
Proof. exact (TRANS (@lem2969879 _31794 _31795) (@lem2969969 _31794 _31795)). Qed.
Lemma lem2969972 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2969973 (_31794 : int) (_31795 : int) : (term347 _31794 _31795) = (term348 _31794 _31795).
Proof. exact (MK_COMB (@lem2969972) (@lem2969971 _31794 _31795)). Qed.
Lemma lem2969974 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2969975 (_31794 : int) (_31795 : int) : (term340 _31794 _31795) = (term349 _31794 _31795).
Proof. exact (MK_COMB (@lem2969973 _31794 _31795) (@lem2969974)). Qed.
Lemma lem2969976 (_31794 : int) (_31795 : int) : (term193 _31795 _31794) = (term349 _31794 _31795).
Proof. exact (TRANS (@lem2969861 _31794 _31795) (@lem2969975 _31794 _31795)). Qed.
Lemma lem2969977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2969978 (_31794 : int) (_31795 : int) : (term185 _31794 _31795) = (term350 _31794 _31795).
Proof. exact (MK_COMB (@lem2969977) (@lem2969860 _31794 _31795)). Qed.
Lemma lem2969979 (_31794 : int) (_31795 : int) : (term194 _31795 _31794) = (term351 _31794 _31795).
Proof. exact (MK_COMB (@lem2969978 _31794 _31795) (@lem2969976 _31794 _31795)). Qed.
Lemma lem2969980 (_31795 : int) (_31794 : int) : (term199 _31794 _31795) = (term352 _31795 _31794).
Proof. exact (@lem1988287 (term190 _31795) (term171 _31794)). Qed.
Lemma lem2970004 (_31795 : int) (_31794 : int) : (term353 _31795 _31794) = (term354 _31795 _31794).
Proof. exact (@lem1982792 (term190 _31795) (term171 _31794)). Qed.
Lemma lem2970005 (_31794 : int) : (term286 _31794) = (term287 _31794).
Proof. exact (@lem1982781 (real_of_int _31794) term232 term169). Qed.
Lemma lem2970007 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970008 : term169 = term288.
Proof. exact (@lem2970007 term86). Qed.
Lemma lem2970010 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2970011 : term232 = term233.
Proof. exact (@lem2970010 term86). Qed.
Lemma lem2970012 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970013 : term234 = term235.
Proof. exact (MK_COMB (@lem2970012) (@lem2970011)). Qed.
Lemma lem2970014 : term289 = term290.
Proof. exact (MK_COMB (@lem2970013) (@lem2970008)). Qed.
Lemma lem2970015 : term290 = term291.
Proof. exact (@lem1981613 term232 term169 term169 term169). Qed.
Lemma lem2970017 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970018 : term241 = term242.
Proof. exact (@lem2970017 term86 term86). Qed.
Lemma lem2970019 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970020 : term244 = term86.
Proof. exact (EQ_MP (@lem2970019) (@lem940073)). Qed.
Lemma lem2970021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970022 : term242 = term169.
Proof. exact (MK_COMB (@lem2970021) (@lem2970020)). Qed.
Lemma lem2970023 : term241 = term169.
Proof. exact (TRANS (@lem2970018) (@lem2970022)). Qed.
Lemma lem2970025 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2970026 : term289 = term292.
Proof. exact (@lem2970025 term86 term86). Qed.
Lemma lem2970027 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970028 : term244 = term86.
Proof. exact (EQ_MP (@lem2970027) (@lem940073)). Qed.
Lemma lem2970029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970030 : term242 = term169.
Proof. exact (MK_COMB (@lem2970029) (@lem2970028)). Qed.
Lemma lem2970031 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2970032 : term292 = term232.
Proof. exact (MK_COMB (@lem2970031) (@lem2970030)). Qed.
Lemma lem2970033 : term289 = term232.
Proof. exact (TRANS (@lem2970026) (@lem2970032)). Qed.
Lemma lem2970034 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2970035 : term293 = term294.
Proof. exact (MK_COMB (@lem2970034) (@lem2970033)). Qed.
Lemma lem2970036 : term291 = term233.
Proof. exact (MK_COMB (@lem2970035) (@lem2970023)). Qed.
Lemma lem2970037 : term290 = term233.
Proof. exact (TRANS (@lem2970015) (@lem2970036)). Qed.
Lemma lem2970038 : term289 = term233.
Proof. exact (TRANS (@lem2970014) (@lem2970037)). Qed.
Lemma lem2970040 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2970041 : term233 = term232.
Proof. exact (@lem2970040 term232). Qed.
Lemma lem2970042 : term289 = term232.
Proof. exact (TRANS (@lem2970038) (@lem2970041)). Qed.
Lemma lem2970045 (_31794 : int) : (term295 _31794) = (term295 _31794).
Proof. exact (eq_refl (term295 _31794)). Qed.
Lemma lem2970046 (_31794 : int) : (term287 _31794) = (term296 _31794).
Proof. exact (MK_COMB (@lem2970045 _31794) (@lem2970042)). Qed.
Lemma lem2970047 (_31794 : int) : (term286 _31794) = (term296 _31794).
Proof. exact (TRANS (@lem2970005 _31794) (@lem2970046 _31794)). Qed.
Lemma lem2970048 (_31795 : int) : (term208 _31795) = (term208 _31795).
Proof. exact (eq_refl (term208 _31795)). Qed.
Lemma lem2970049 (_31795 : int) (_31794 : int) : (term354 _31795 _31794) = (term355 _31795 _31794).
Proof. exact (MK_COMB (@lem2970048 _31795) (@lem2970047 _31794)). Qed.
Lemma lem2970050 (_31794 : int) (_31795 : int) : (term355 _31795 _31794) = (term356 _31794 _31795).
Proof. exact (@lem1982757 (term257 _31794) (term190 _31795) term232). Qed.
Lemma lem2970051 (_31795 : int) : (term357 _31795) = (term358 _31795).
Proof. exact (@lem1982755 (term157 _31795) term169 term232). Qed.
Lemma lem2970053 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2970054 : term232 = term233.
Proof. exact (@lem2970053 term86). Qed.
Lemma lem2970056 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970057 : term169 = term288.
Proof. exact (@lem2970056 term86). Qed.
Lemma lem2970058 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970059 : term359 = term360.
Proof. exact (MK_COMB (@lem2970058) (@lem2970057)). Qed.
Lemma lem2970060 : term361 = term362.
Proof. exact (MK_COMB (@lem2970059) (@lem2970054)). Qed.
Lemma lem2970061 : term363.
Proof. exact (@lem1981473 term169 term169 term232 term169 term140 term169). Qed.
Lemma lem2970063 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970064 : term305 = term306.
Proof. exact (@lem2970063 (NUMERAL 0) term86). Qed.
Lemma lem2970065 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970066 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970067 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970066 h1) (fun h1 : term306 = True => @lem2970065)). Qed.
Lemma lem2970068 : term306 = True.
Proof. exact (EQ_MP (@lem2970067) (@lem2970065)). Qed.
Lemma lem2970069 : term305 = True.
Proof. exact (TRANS (@lem2970064) (@lem2970068)). Qed.
Lemma lem2970070 : True = term305.
Proof. exact (SYM (@lem2970069)). Qed.
Lemma lem2970071 : term305.
Proof. exact (EQ_MP (@lem2970070) (@lem0)). Qed.
Lemma lem2970072 : term364.
Proof. exact (@lem2970061 (@lem2970071)). Qed.
Lemma lem2970074 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970075 : term305 = term306.
Proof. exact (@lem2970074 (NUMERAL 0) term86). Qed.
Lemma lem2970076 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970077 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970078 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970077 h1) (fun h1 : term306 = True => @lem2970076)). Qed.
Lemma lem2970079 : term306 = True.
Proof. exact (EQ_MP (@lem2970078) (@lem2970076)). Qed.
Lemma lem2970080 : term305 = True.
Proof. exact (TRANS (@lem2970075) (@lem2970079)). Qed.
Lemma lem2970081 : True = term305.
Proof. exact (SYM (@lem2970080)). Qed.
Lemma lem2970082 : term305.
Proof. exact (EQ_MP (@lem2970081) (@lem0)). Qed.
Lemma lem2970083 : term365.
Proof. exact (@lem2970072 (@lem2970082)). Qed.
Lemma lem2970085 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970086 : term305 = term306.
Proof. exact (@lem2970085 (NUMERAL 0) term86). Qed.
Lemma lem2970087 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970088 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970089 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970088 h1) (fun h1 : term306 = True => @lem2970087)). Qed.
Lemma lem2970090 : term306 = True.
Proof. exact (EQ_MP (@lem2970089) (@lem2970087)). Qed.
Lemma lem2970091 : term305 = True.
Proof. exact (TRANS (@lem2970086) (@lem2970090)). Qed.
Lemma lem2970092 : True = term305.
Proof. exact (SYM (@lem2970091)). Qed.
Lemma lem2970093 : term305.
Proof. exact (EQ_MP (@lem2970092) (@lem0)). Qed.
Lemma lem2970094 : term366.
Proof. exact (@lem2970083 (@lem2970093)). Qed.
Lemma lem2970096 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2970097 : term289 = term292.
Proof. exact (@lem2970096 term86 term86). Qed.
Lemma lem2970098 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970099 : term244 = term86.
Proof. exact (EQ_MP (@lem2970098) (@lem940073)). Qed.
Lemma lem2970100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970101 : term242 = term169.
Proof. exact (MK_COMB (@lem2970100) (@lem2970099)). Qed.
Lemma lem2970102 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2970103 : term292 = term232.
Proof. exact (MK_COMB (@lem2970102) (@lem2970101)). Qed.
Lemma lem2970104 : term289 = term232.
Proof. exact (TRANS (@lem2970097) (@lem2970103)). Qed.
Lemma lem2970106 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970107 : term241 = term242.
Proof. exact (@lem2970106 term86 term86). Qed.
Lemma lem2970108 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970109 : term244 = term86.
Proof. exact (EQ_MP (@lem2970108) (@lem940073)). Qed.
Lemma lem2970110 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970111 : term242 = term169.
Proof. exact (MK_COMB (@lem2970110) (@lem2970109)). Qed.
Lemma lem2970112 : term241 = term169.
Proof. exact (TRANS (@lem2970107) (@lem2970111)). Qed.
Lemma lem2970113 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970114 : term367 = term359.
Proof. exact (MK_COMB (@lem2970113) (@lem2970112)). Qed.
Lemma lem2970115 : term368 = term361.
Proof. exact (MK_COMB (@lem2970114) (@lem2970104)). Qed.
Lemma lem2970117 (m : nat) : (term369 m) = term140.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2970118 : term361 = term140.
Proof. exact (@lem2970117 term86). Qed.
Lemma lem2970119 : term368 = term140.
Proof. exact (TRANS (@lem2970115) (@lem2970118)). Qed.
Lemma lem2970120 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970121 : term370 = term371.
Proof. exact (MK_COMB (@lem2970120) (@lem2970119)). Qed.
Lemma lem2970122 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2970123 : term372 = term373.
Proof. exact (MK_COMB (@lem2970121) (@lem2970122)). Qed.
Lemma lem2970125 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2970126 : term373 = term140.
Proof. exact (@lem2970125 term86). Qed.
Lemma lem2970127 : term372 = term140.
Proof. exact (TRANS (@lem2970123) (@lem2970126)). Qed.
Lemma lem2970129 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970130 : term241 = term242.
Proof. exact (@lem2970129 term86 term86). Qed.
Lemma lem2970131 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970132 : term244 = term86.
Proof. exact (EQ_MP (@lem2970131) (@lem940073)). Qed.
Lemma lem2970133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970134 : term242 = term169.
Proof. exact (MK_COMB (@lem2970133) (@lem2970132)). Qed.
Lemma lem2970135 : term241 = term169.
Proof. exact (TRANS (@lem2970130) (@lem2970134)). Qed.
Lemma lem2970136 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2970137 : term375 = term373.
Proof. exact (MK_COMB (@lem2970136) (@lem2970135)). Qed.
Lemma lem2970139 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2970140 : term373 = term140.
Proof. exact (@lem2970139 term86). Qed.
Lemma lem2970141 : term375 = term140.
Proof. exact (TRANS (@lem2970137) (@lem2970140)). Qed.
Lemma lem2970142 : term140 = term375.
Proof. exact (SYM (@lem2970141)). Qed.
Lemma lem2970143 : term372 = term375.
Proof. exact (TRANS (@lem2970127) (@lem2970142)). Qed.
Lemma lem2970144 : term362 = term229.
Proof. exact (@lem2970094 (@lem2970143)). Qed.
Lemma lem2970145 : term361 = term229.
Proof. exact (TRANS (@lem2970060) (@lem2970144)). Qed.
Lemma lem2970147 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2970148 : term229 = term140.
Proof. exact (@lem2970147 term140). Qed.
Lemma lem2970149 : term361 = term140.
Proof. exact (TRANS (@lem2970145) (@lem2970148)). Qed.
Lemma lem2970150 (_31795 : int) : (term159 _31795) = (term159 _31795).
Proof. exact (eq_refl (term159 _31795)). Qed.
Lemma lem2970151 (_31795 : int) : (term358 _31795) = (term376 _31795).
Proof. exact (MK_COMB (@lem2970150 _31795) (@lem2970149)). Qed.
Lemma lem2970152 (_31795 : int) : (term357 _31795) = (term376 _31795).
Proof. exact (TRANS (@lem2970051 _31795) (@lem2970151 _31795)). Qed.
Lemma lem2970153 (_31795 : int) : (term376 _31795) = (term157 _31795).
Proof. exact (@lem1982723 (term157 _31795)). Qed.
Lemma lem2970154 (_31795 : int) : (term357 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2970152 _31795) (@lem2970153 _31795)). Qed.
Lemma lem2970155 (_31794 : int) : (term295 _31794) = (term295 _31794).
Proof. exact (eq_refl (term295 _31794)). Qed.
Lemma lem2970156 (_31794 : int) (_31795 : int) : (term356 _31794 _31795) = (term377 _31794 _31795).
Proof. exact (MK_COMB (@lem2970155 _31794) (@lem2970154 _31795)). Qed.
Lemma lem2970157 (_31794 : int) (_31795 : int) : (term355 _31795 _31794) = (term377 _31794 _31795).
Proof. exact (TRANS (@lem2970050 _31794 _31795) (@lem2970156 _31794 _31795)). Qed.
Lemma lem2970158 (_31794 : int) (_31795 : int) : (term354 _31795 _31794) = (term377 _31794 _31795).
Proof. exact (TRANS (@lem2970049 _31795 _31794) (@lem2970157 _31794 _31795)). Qed.
Lemma lem2970160 (_31794 : int) (_31795 : int) : (term353 _31795 _31794) = (term377 _31794 _31795).
Proof. exact (TRANS (@lem2970004 _31795 _31794) (@lem2970158 _31794 _31795)). Qed.
Lemma lem2970161 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2970162 (_31794 : int) (_31795 : int) : (term378 _31795 _31794) = (term379 _31794 _31795).
Proof. exact (MK_COMB (@lem2970161) (@lem2970160 _31794 _31795)). Qed.
Lemma lem2970163 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2970164 (_31794 : int) (_31795 : int) : (term352 _31795 _31794) = (term380 _31794 _31795).
Proof. exact (MK_COMB (@lem2970162 _31794 _31795) (@lem2970163)). Qed.
Lemma lem2970165 (_31794 : int) (_31795 : int) : (term199 _31794 _31795) = (term380 _31794 _31795).
Proof. exact (TRANS (@lem2969980 _31795 _31794) (@lem2970164 _31794 _31795)). Qed.
Lemma lem2970166 (_31794 : int) (_31795 : int) : (term212 _31795 _31794) = (term381 _31794 _31795).
Proof. exact (@lem1988287 (real_of_int _31794) (term209 _31795)). Qed.
Lemma lem2970184 (_31795 : int) : (term209 _31795) = (term382 _31795).
Proof. exact (@lem1982755 (term157 _31795) term169 term169). Qed.
Lemma lem2970186 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970187 : term169 = term288.
Proof. exact (@lem2970186 term86). Qed.
Lemma lem2970189 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970190 : term169 = term288.
Proof. exact (@lem2970189 term86). Qed.
Lemma lem2970191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970192 : term359 = term360.
Proof. exact (MK_COMB (@lem2970191) (@lem2970190)). Qed.
Lemma lem2970193 : term383 = term384.
Proof. exact (MK_COMB (@lem2970192) (@lem2970187)). Qed.
Lemma lem2970194 : term385.
Proof. exact (@lem1981473 term169 term169 term169 term169 term154 term169). Qed.
Lemma lem2970196 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970197 : term305 = term306.
Proof. exact (@lem2970196 (NUMERAL 0) term86). Qed.
Lemma lem2970198 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970199 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970200 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970199 h1) (fun h1 : term306 = True => @lem2970198)). Qed.
Lemma lem2970201 : term306 = True.
Proof. exact (EQ_MP (@lem2970200) (@lem2970198)). Qed.
Lemma lem2970202 : term305 = True.
Proof. exact (TRANS (@lem2970197) (@lem2970201)). Qed.
Lemma lem2970203 : True = term305.
Proof. exact (SYM (@lem2970202)). Qed.
Lemma lem2970204 : term305.
Proof. exact (EQ_MP (@lem2970203) (@lem0)). Qed.
Lemma lem2970205 : term386.
Proof. exact (@lem2970194 (@lem2970204)). Qed.
Lemma lem2970207 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970208 : term305 = term306.
Proof. exact (@lem2970207 (NUMERAL 0) term86). Qed.
Lemma lem2970209 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970210 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970211 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970210 h1) (fun h1 : term306 = True => @lem2970209)). Qed.
Lemma lem2970212 : term306 = True.
Proof. exact (EQ_MP (@lem2970211) (@lem2970209)). Qed.
Lemma lem2970213 : term305 = True.
Proof. exact (TRANS (@lem2970208) (@lem2970212)). Qed.
Lemma lem2970214 : True = term305.
Proof. exact (SYM (@lem2970213)). Qed.
Lemma lem2970215 : term305.
Proof. exact (EQ_MP (@lem2970214) (@lem0)). Qed.
Lemma lem2970216 : term387.
Proof. exact (@lem2970205 (@lem2970215)). Qed.
Lemma lem2970218 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970219 : term305 = term306.
Proof. exact (@lem2970218 (NUMERAL 0) term86). Qed.
Lemma lem2970220 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970221 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970222 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970221 h1) (fun h1 : term306 = True => @lem2970220)). Qed.
Lemma lem2970223 : term306 = True.
Proof. exact (EQ_MP (@lem2970222) (@lem2970220)). Qed.
Lemma lem2970224 : term305 = True.
Proof. exact (TRANS (@lem2970219) (@lem2970223)). Qed.
Lemma lem2970225 : True = term305.
Proof. exact (SYM (@lem2970224)). Qed.
Lemma lem2970226 : term305.
Proof. exact (EQ_MP (@lem2970225) (@lem0)). Qed.
Lemma lem2970227 : term388.
Proof. exact (@lem2970216 (@lem2970226)). Qed.
Lemma lem2970229 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970230 : term241 = term242.
Proof. exact (@lem2970229 term86 term86). Qed.
Lemma lem2970231 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970232 : term244 = term86.
Proof. exact (EQ_MP (@lem2970231) (@lem940073)). Qed.
Lemma lem2970233 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970234 : term242 = term169.
Proof. exact (MK_COMB (@lem2970233) (@lem2970232)). Qed.
Lemma lem2970235 : term241 = term169.
Proof. exact (TRANS (@lem2970230) (@lem2970234)). Qed.
Lemma lem2970237 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970238 : term241 = term242.
Proof. exact (@lem2970237 term86 term86). Qed.
Lemma lem2970239 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970240 : term244 = term86.
Proof. exact (EQ_MP (@lem2970239) (@lem940073)). Qed.
Lemma lem2970241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970242 : term242 = term169.
Proof. exact (MK_COMB (@lem2970241) (@lem2970240)). Qed.
Lemma lem2970243 : term241 = term169.
Proof. exact (TRANS (@lem2970238) (@lem2970242)). Qed.
Lemma lem2970244 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970245 : term367 = term359.
Proof. exact (MK_COMB (@lem2970244) (@lem2970243)). Qed.
Lemma lem2970246 : term389 = term383.
Proof. exact (MK_COMB (@lem2970245) (@lem2970235)). Qed.
Lemma lem2970247 : term383 = term320.
Proof. exact (@lem1367770 term86 term86). Qed.
Lemma lem2970248 : term318 = term27.
Proof. exact (@lem706885). Qed.
Lemma lem2970249 : (term318 = term27) = (term319 = term2).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term27). Qed.
Lemma lem2970250 : term319 = term2.
Proof. exact (EQ_MP (@lem2970249) (@lem2970248)). Qed.
Lemma lem2970251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970252 : term320 = term154.
Proof. exact (MK_COMB (@lem2970251) (@lem2970250)). Qed.
Lemma lem2970253 : term383 = term154.
Proof. exact (TRANS (@lem2970247) (@lem2970252)). Qed.
Lemma lem2970254 : term389 = term154.
Proof. exact (TRANS (@lem2970246) (@lem2970253)). Qed.
Lemma lem2970255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970256 : term390 = term156.
Proof. exact (MK_COMB (@lem2970255) (@lem2970254)). Qed.
Lemma lem2970257 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2970258 : term391 = term311.
Proof. exact (MK_COMB (@lem2970256) (@lem2970257)). Qed.
Lemma lem2970260 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970261 : term311 = term312.
Proof. exact (@lem2970260 term2 term86). Qed.
Lemma lem2970262 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2970263 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2970264 : term314 = term2.
Proof. exact (EQ_MP (@lem2970263) (@lem2970262)). Qed.
Lemma lem2970265 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970266 : term312 = term154.
Proof. exact (MK_COMB (@lem2970265) (@lem2970264)). Qed.
Lemma lem2970267 : term311 = term154.
Proof. exact (TRANS (@lem2970261) (@lem2970266)). Qed.
Lemma lem2970268 : term391 = term154.
Proof. exact (TRANS (@lem2970258) (@lem2970267)). Qed.
Lemma lem2970270 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970271 : term241 = term242.
Proof. exact (@lem2970270 term86 term86). Qed.
Lemma lem2970272 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970273 : term244 = term86.
Proof. exact (EQ_MP (@lem2970272) (@lem940073)). Qed.
Lemma lem2970274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970275 : term242 = term169.
Proof. exact (MK_COMB (@lem2970274) (@lem2970273)). Qed.
Lemma lem2970276 : term241 = term169.
Proof. exact (TRANS (@lem2970271) (@lem2970275)). Qed.
Lemma lem2970277 : term156 = term156.
Proof. exact (eq_refl term156). Qed.
Lemma lem2970278 : term392 = term311.
Proof. exact (MK_COMB (@lem2970277) (@lem2970276)). Qed.
Lemma lem2970280 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970281 : term311 = term312.
Proof. exact (@lem2970280 term2 term86). Qed.
Lemma lem2970282 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2970283 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2970284 : term314 = term2.
Proof. exact (EQ_MP (@lem2970283) (@lem2970282)). Qed.
Lemma lem2970285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970286 : term312 = term154.
Proof. exact (MK_COMB (@lem2970285) (@lem2970284)). Qed.
Lemma lem2970287 : term311 = term154.
Proof. exact (TRANS (@lem2970281) (@lem2970286)). Qed.
Lemma lem2970288 : term392 = term154.
Proof. exact (TRANS (@lem2970278) (@lem2970287)). Qed.
Lemma lem2970289 : term154 = term392.
Proof. exact (SYM (@lem2970288)). Qed.
Lemma lem2970290 : term391 = term392.
Proof. exact (TRANS (@lem2970268) (@lem2970289)). Qed.
Lemma lem2970291 : term384 = term260.
Proof. exact (@lem2970227 (@lem2970290)). Qed.
Lemma lem2970292 : term383 = term260.
Proof. exact (TRANS (@lem2970193) (@lem2970291)). Qed.
Lemma lem2970294 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2970295 : term260 = term154.
Proof. exact (@lem2970294 term154). Qed.
Lemma lem2970296 : term383 = term154.
Proof. exact (TRANS (@lem2970292) (@lem2970295)). Qed.
Lemma lem2970297 (_31795 : int) : (term159 _31795) = (term159 _31795).
Proof. exact (eq_refl (term159 _31795)). Qed.
Lemma lem2970298 (_31795 : int) : (term382 _31795) = (term393 _31795).
Proof. exact (MK_COMB (@lem2970297 _31795) (@lem2970296)). Qed.
Lemma lem2970300 (_31795 : int) : (term209 _31795) = (term393 _31795).
Proof. exact (TRANS (@lem2970184 _31795) (@lem2970298 _31795)). Qed.
Lemma lem2970303 (_31794 : int) : (term394 _31794) = (term394 _31794).
Proof. exact (eq_refl (term394 _31794)). Qed.
Lemma lem2970304 (_31794 : int) (_31795 : int) : (term395 _31794 _31795) = (term396 _31794 _31795).
Proof. exact (MK_COMB (@lem2970303 _31794) (@lem2970300 _31795)). Qed.
Lemma lem2970305 (_31794 : int) (_31795 : int) : (term396 _31794 _31795) = (term397 _31794 _31795).
Proof. exact (@lem1982792 (real_of_int _31794) (term393 _31795)). Qed.
Lemma lem2970306 (_31795 : int) : (term398 _31795) = (term399 _31795).
Proof. exact (@lem1982781 (term157 _31795) term232 term154). Qed.
Lemma lem2970308 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970309 : term154 = term260.
Proof. exact (@lem2970308 term2). Qed.
Lemma lem2970311 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2970312 : term232 = term233.
Proof. exact (@lem2970311 term86). Qed.
Lemma lem2970313 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970314 : term234 = term235.
Proof. exact (MK_COMB (@lem2970313) (@lem2970312)). Qed.
Lemma lem2970315 : term261 = term262.
Proof. exact (MK_COMB (@lem2970314) (@lem2970309)). Qed.
Lemma lem2970316 : term262 = term263.
Proof. exact (@lem1981613 term232 term154 term169 term169). Qed.
Lemma lem2970318 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970319 : term241 = term242.
Proof. exact (@lem2970318 term86 term86). Qed.
Lemma lem2970320 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970321 : term244 = term86.
Proof. exact (EQ_MP (@lem2970320) (@lem940073)). Qed.
Lemma lem2970322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970323 : term242 = term169.
Proof. exact (MK_COMB (@lem2970322) (@lem2970321)). Qed.
Lemma lem2970324 : term241 = term169.
Proof. exact (TRANS (@lem2970319) (@lem2970323)). Qed.
Lemma lem2970326 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2970327 : term261 = term266.
Proof. exact (@lem2970326 term86 term2). Qed.
Lemma lem2970328 : term267 = term27.
Proof. exact (@lem996238 term27). Qed.
Lemma lem2970329 : (term267 = term27) = (term268 = term2).
Proof. exact (@lem1007663 (BIT1 0) term27 term27). Qed.
Lemma lem2970330 : term268 = term2.
Proof. exact (EQ_MP (@lem2970329) (@lem2970328)). Qed.
Lemma lem2970331 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970332 : term269 = term154.
Proof. exact (MK_COMB (@lem2970331) (@lem2970330)). Qed.
Lemma lem2970333 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2970334 : term266 = term270.
Proof. exact (MK_COMB (@lem2970333) (@lem2970332)). Qed.
Lemma lem2970335 : term261 = term270.
Proof. exact (TRANS (@lem2970327) (@lem2970334)). Qed.
Lemma lem2970336 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2970337 : term271 = term272.
Proof. exact (MK_COMB (@lem2970336) (@lem2970335)). Qed.
Lemma lem2970338 : term263 = term273.
Proof. exact (MK_COMB (@lem2970337) (@lem2970324)). Qed.
Lemma lem2970339 : term262 = term273.
Proof. exact (TRANS (@lem2970316) (@lem2970338)). Qed.
Lemma lem2970340 : term261 = term273.
Proof. exact (TRANS (@lem2970315) (@lem2970339)). Qed.
Lemma lem2970342 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2970343 : term273 = term270.
Proof. exact (@lem2970342 term270). Qed.
Lemma lem2970344 : term261 = term270.
Proof. exact (TRANS (@lem2970340) (@lem2970343)). Qed.
Lemma lem2970345 (_31795 : int) : (term258 _31795) = (term259 _31795).
Proof. exact (@lem1982749 term232 term154 (real_of_int _31795)). Qed.
Lemma lem2970347 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970348 : term154 = term260.
Proof. exact (@lem2970347 term2). Qed.
Lemma lem2970350 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2970351 : term232 = term233.
Proof. exact (@lem2970350 term86). Qed.
Lemma lem2970352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970353 : term234 = term235.
Proof. exact (MK_COMB (@lem2970352) (@lem2970351)). Qed.
Lemma lem2970354 : term261 = term262.
Proof. exact (MK_COMB (@lem2970353) (@lem2970348)). Qed.
Lemma lem2970355 : term262 = term263.
Proof. exact (@lem1981613 term232 term154 term169 term169). Qed.
Lemma lem2970357 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970358 : term241 = term242.
Proof. exact (@lem2970357 term86 term86). Qed.
Lemma lem2970359 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970360 : term244 = term86.
Proof. exact (EQ_MP (@lem2970359) (@lem940073)). Qed.
Lemma lem2970361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970362 : term242 = term169.
Proof. exact (MK_COMB (@lem2970361) (@lem2970360)). Qed.
Lemma lem2970363 : term241 = term169.
Proof. exact (TRANS (@lem2970358) (@lem2970362)). Qed.
Lemma lem2970365 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2970366 : term261 = term266.
Proof. exact (@lem2970365 term86 term2). Qed.
Lemma lem2970367 : term267 = term27.
Proof. exact (@lem996238 term27). Qed.
Lemma lem2970368 : (term267 = term27) = (term268 = term2).
Proof. exact (@lem1007663 (BIT1 0) term27 term27). Qed.
Lemma lem2970369 : term268 = term2.
Proof. exact (EQ_MP (@lem2970368) (@lem2970367)). Qed.
Lemma lem2970370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970371 : term269 = term154.
Proof. exact (MK_COMB (@lem2970370) (@lem2970369)). Qed.
Lemma lem2970372 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2970373 : term266 = term270.
Proof. exact (MK_COMB (@lem2970372) (@lem2970371)). Qed.
Lemma lem2970374 : term261 = term270.
Proof. exact (TRANS (@lem2970366) (@lem2970373)). Qed.
Lemma lem2970375 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2970376 : term271 = term272.
Proof. exact (MK_COMB (@lem2970375) (@lem2970374)). Qed.
Lemma lem2970377 : term263 = term273.
Proof. exact (MK_COMB (@lem2970376) (@lem2970363)). Qed.
Lemma lem2970378 : term262 = term273.
Proof. exact (TRANS (@lem2970355) (@lem2970377)). Qed.
Lemma lem2970379 : term261 = term273.
Proof. exact (TRANS (@lem2970354) (@lem2970378)). Qed.
Lemma lem2970381 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2970382 : term273 = term270.
Proof. exact (@lem2970381 term270). Qed.
Lemma lem2970383 : term261 = term270.
Proof. exact (TRANS (@lem2970379) (@lem2970382)). Qed.
Lemma lem2970384 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970385 : term274 = term275.
Proof. exact (MK_COMB (@lem2970384) (@lem2970383)). Qed.
Lemma lem2970386 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2970387 (_31795 : int) : (term259 _31795) = (term276 _31795).
Proof. exact (MK_COMB (@lem2970385) (@lem2970386 _31795)). Qed.
Lemma lem2970388 (_31795 : int) : (term258 _31795) = (term276 _31795).
Proof. exact (TRANS (@lem2970345 _31795) (@lem2970387 _31795)). Qed.
Lemma lem2970389 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970390 (_31795 : int) : (term277 _31795) = (term278 _31795).
Proof. exact (MK_COMB (@lem2970389) (@lem2970388 _31795)). Qed.
Lemma lem2970391 (_31795 : int) : (term399 _31795) = (term400 _31795).
Proof. exact (MK_COMB (@lem2970390 _31795) (@lem2970344)). Qed.
Lemma lem2970392 (_31795 : int) : (term398 _31795) = (term400 _31795).
Proof. exact (TRANS (@lem2970306 _31795) (@lem2970391 _31795)). Qed.
Lemma lem2970393 (_31794 : int) : (term170 _31794) = (term170 _31794).
Proof. exact (eq_refl (term170 _31794)). Qed.
Lemma lem2970396 (_31794 : int) (_31795 : int) : (term397 _31794 _31795) = (term401 _31794 _31795).
Proof. exact (MK_COMB (@lem2970393 _31794) (@lem2970392 _31795)). Qed.
Lemma lem2970397 (_31794 : int) (_31795 : int) : (term396 _31794 _31795) = (term401 _31794 _31795).
Proof. exact (TRANS (@lem2970305 _31794 _31795) (@lem2970396 _31794 _31795)). Qed.
Lemma lem2970398 (_31794 : int) (_31795 : int) : (term395 _31794 _31795) = (term401 _31794 _31795).
Proof. exact (TRANS (@lem2970304 _31794 _31795) (@lem2970397 _31794 _31795)). Qed.
Lemma lem2970399 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2970400 (_31794 : int) (_31795 : int) : (term402 _31794 _31795) = (term403 _31794 _31795).
Proof. exact (MK_COMB (@lem2970399) (@lem2970398 _31794 _31795)). Qed.
Lemma lem2970401 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2970402 (_31794 : int) (_31795 : int) : (term381 _31794 _31795) = (term404 _31794 _31795).
Proof. exact (MK_COMB (@lem2970400 _31794 _31795) (@lem2970401)). Qed.
Lemma lem2970403 (_31794 : int) (_31795 : int) : (term212 _31795 _31794) = (term404 _31794 _31795).
Proof. exact (TRANS (@lem2970166 _31794 _31795) (@lem2970402 _31794 _31795)). Qed.
Lemma lem2970404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2970405 (_31794 : int) (_31795 : int) : (term201 _31794 _31795) = (term405 _31794 _31795).
Proof. exact (MK_COMB (@lem2970404) (@lem2970165 _31794 _31795)). Qed.
Lemma lem2970406 (_31794 : int) (_31795 : int) : (term213 _31795 _31794) = (term406 _31794 _31795).
Proof. exact (MK_COMB (@lem2970405 _31794 _31795) (@lem2970403 _31794 _31795)). Qed.
Lemma lem2970407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2970408 (_31794 : int) (_31795 : int) : (term215 _31795 _31794) = (term407 _31794 _31795).
Proof. exact (MK_COMB (@lem2970407) (@lem2969979 _31794 _31795)). Qed.
Lemma lem2970409 (_31794 : int) (_31795 : int) : (term216 _31795 _31794) = (term408 _31794 _31795).
Proof. exact (MK_COMB (@lem2970408 _31794 _31795) (@lem2970406 _31794 _31795)). Qed.
Lemma lem2970410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2970411 (_31794 : int) (_31795 : int) (_31796 : int) : (term217 _31794 _31795 _31796) = (term409 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2970410) (@lem2969783 _31794 _31795 _31796)). Qed.
Lemma lem2970412 (_31796 : int) (_31794 : int) (_31795 : int) : (term218 _31796 _31795 _31794) = (term410 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970411 _31794 _31795 _31796) (@lem2970409 _31794 _31795)). Qed.
Lemma lem2970413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2970414 (_31796 : int) : (term219 _31796) = (term411 _31796).
Proof. exact (MK_COMB (@lem2970413) (@lem2969510 _31796)). Qed.
Lemma lem2970415 (_31796 : int) (_31794 : int) (_31795 : int) : (term220 _31796 _31795 _31794) = (term412 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970414 _31796) (@lem2970412 _31796 _31794 _31795)). Qed.
Lemma lem2970416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2970417 (_31795 : int) : (term219 _31795) = (term411 _31795).
Proof. exact (MK_COMB (@lem2970416) (@lem2969462 _31795)). Qed.
Lemma lem2970418 (_31796 : int) (_31794 : int) (_31795 : int) : (term221 _31796 _31795 _31794) = (term413 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970417 _31795) (@lem2970415 _31796 _31794 _31795)). Qed.
Lemma lem2970419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2970420 (_31794 : int) : (term219 _31794) = (term411 _31794).
Proof. exact (MK_COMB (@lem2970419) (@lem2969414 _31794)). Qed.
Lemma lem2970421 (_31796 : int) (_31794 : int) (_31795 : int) : (term222 _31796 _31795 _31794) = (term414 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970420 _31794) (@lem2970418 _31796 _31794 _31795)). Qed.
Lemma lem2970428 (_31796 : int) (_31794 : int) (_31795 : int) : (term224 _31796 _31795 _31794) = (term414 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2969366 _31796 _31795 _31794) (@lem2970421 _31796 _31794 _31795)). Qed.
Lemma lem2970442 (_31794 : int) (_31795 : int) : (term408 _31794 _31795) = (term415 _31794 _31795).
Proof. exact (@lem19158 (term380 _31794 _31795) (term351 _31794 _31795) (term404 _31794 _31795)). Qed.
Lemma lem2970449 (_31794 : int) (_31795 : int) : (term416 _31794 _31795) = (term417 _31794 _31795).
Proof. exact (@lem19367 (term339 _31794 _31795) (term349 _31794 _31795) (term404 _31794 _31795)). Qed.
Lemma lem2970456 (_31794 : int) (_31795 : int) : (term418 _31794 _31795) = (term419 _31794 _31795).
Proof. exact (@lem19367 (term339 _31794 _31795) (term349 _31794 _31795) (term380 _31794 _31795)). Qed.
Lemma lem2970457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2970458 (_31794 : int) (_31795 : int) : (term420 _31794 _31795) = (term421 _31794 _31795).
Proof. exact (MK_COMB (@lem2970457) (@lem2970456 _31794 _31795)). Qed.
Lemma lem2970459 (_31794 : int) (_31795 : int) : (term415 _31794 _31795) = (term422 _31794 _31795).
Proof. exact (MK_COMB (@lem2970458 _31794 _31795) (@lem2970449 _31794 _31795)). Qed.
Lemma lem2970461 (_31794 : int) (_31795 : int) : (term408 _31794 _31795) = (term422 _31794 _31795).
Proof. exact (TRANS (@lem2970442 _31794 _31795) (@lem2970459 _31794 _31795)). Qed.
Lemma lem2970470 (_31794 : int) (_31795 : int) (_31796 : int) : (term409 _31794 _31795 _31796) = (term409 _31794 _31795 _31796).
Proof. exact (eq_refl (term409 _31794 _31795 _31796)). Qed.
Lemma lem2970471 (_31796 : int) (_31794 : int) (_31795 : int) : (term410 _31796 _31794 _31795) = (term423 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970470 _31794 _31795 _31796) (@lem2970461 _31794 _31795)). Qed.
Lemma lem2970472 (_31796 : int) (_31794 : int) (_31795 : int) : (term423 _31796 _31794 _31795) = (term424 _31796 _31794 _31795).
Proof. exact (@lem19158 (term419 _31794 _31795) (term331 _31794 _31795 _31796) (term417 _31794 _31795)). Qed.
Lemma lem2970479 (_31796 : int) (_31794 : int) (_31795 : int) : (term425 _31796 _31794 _31795) = (term426 _31796 _31794 _31795).
Proof. exact (@lem19158 (term427 _31794 _31795) (term331 _31794 _31795 _31796) (term428 _31794 _31795)). Qed.
Lemma lem2970486 (_31796 : int) (_31794 : int) (_31795 : int) : (term429 _31796 _31794 _31795) = (term430 _31796 _31794 _31795).
Proof. exact (@lem19158 (term431 _31794 _31795) (term331 _31794 _31795 _31796) (term432 _31794 _31795)). Qed.
Lemma lem2970487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2970488 (_31796 : int) (_31794 : int) (_31795 : int) : (term433 _31796 _31794 _31795) = (term434 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970487) (@lem2970486 _31796 _31794 _31795)). Qed.
Lemma lem2970489 (_31796 : int) (_31794 : int) (_31795 : int) : (term424 _31796 _31794 _31795) = (term435 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970488 _31796 _31794 _31795) (@lem2970479 _31796 _31794 _31795)). Qed.
Lemma lem2970490 (_31796 : int) (_31794 : int) (_31795 : int) : (term423 _31796 _31794 _31795) = (term435 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970472 _31796 _31794 _31795) (@lem2970489 _31796 _31794 _31795)). Qed.
Lemma lem2970491 (_31796 : int) (_31794 : int) (_31795 : int) : (term410 _31796 _31794 _31795) = (term435 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970471 _31796 _31794 _31795) (@lem2970490 _31796 _31794 _31795)). Qed.
Lemma lem2970494 (_31796 : int) : (term411 _31796) = (term411 _31796).
Proof. exact (eq_refl (term411 _31796)). Qed.
Lemma lem2970495 (_31796 : int) (_31794 : int) (_31795 : int) : (term412 _31796 _31794 _31795) = (term436 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970494 _31796) (@lem2970491 _31796 _31794 _31795)). Qed.
Lemma lem2970496 (_31796 : int) (_31794 : int) (_31795 : int) : (term436 _31796 _31794 _31795) = (term437 _31796 _31794 _31795).
Proof. exact (@lem19158 (term430 _31796 _31794 _31795) (term252 _31796) (term426 _31796 _31794 _31795)). Qed.
Lemma lem2970503 (_31796 : int) (_31794 : int) (_31795 : int) : (term438 _31796 _31794 _31795) = (term439 _31796 _31794 _31795).
Proof. exact (@lem19158 (term440 _31796 _31794 _31795) (term252 _31796) (term441 _31796 _31794 _31795)). Qed.
Lemma lem2970510 (_31796 : int) (_31794 : int) (_31795 : int) : (term442 _31796 _31794 _31795) = (term443 _31796 _31794 _31795).
Proof. exact (@lem19158 (term444 _31796 _31794 _31795) (term252 _31796) (term445 _31796 _31794 _31795)). Qed.
Lemma lem2970511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2970512 (_31796 : int) (_31794 : int) (_31795 : int) : (term446 _31796 _31794 _31795) = (term447 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970511) (@lem2970510 _31796 _31794 _31795)). Qed.
Lemma lem2970513 (_31796 : int) (_31794 : int) (_31795 : int) : (term437 _31796 _31794 _31795) = (term448 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970512 _31796 _31794 _31795) (@lem2970503 _31796 _31794 _31795)). Qed.
Lemma lem2970514 (_31796 : int) (_31794 : int) (_31795 : int) : (term436 _31796 _31794 _31795) = (term448 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970496 _31796 _31794 _31795) (@lem2970513 _31796 _31794 _31795)). Qed.
Lemma lem2970515 (_31796 : int) (_31794 : int) (_31795 : int) : (term412 _31796 _31794 _31795) = (term448 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970495 _31796 _31794 _31795) (@lem2970514 _31796 _31794 _31795)). Qed.
Lemma lem2970518 (_31795 : int) : (term411 _31795) = (term411 _31795).
Proof. exact (eq_refl (term411 _31795)). Qed.
Lemma lem2970519 (_31796 : int) (_31794 : int) (_31795 : int) : (term413 _31796 _31794 _31795) = (term449 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970518 _31795) (@lem2970515 _31796 _31794 _31795)). Qed.
Lemma lem2970520 (_31796 : int) (_31794 : int) (_31795 : int) : (term449 _31796 _31794 _31795) = (term450 _31796 _31794 _31795).
Proof. exact (@lem19158 (term443 _31796 _31794 _31795) (term252 _31795) (term439 _31796 _31794 _31795)). Qed.
Lemma lem2970527 (_31796 : int) (_31794 : int) (_31795 : int) : (term451 _31796 _31794 _31795) = (term452 _31796 _31794 _31795).
Proof. exact (@lem19158 (term453 _31796 _31794 _31795) (term252 _31795) (term454 _31796 _31794 _31795)). Qed.
Lemma lem2970534 (_31796 : int) (_31794 : int) (_31795 : int) : (term455 _31796 _31794 _31795) = (term456 _31796 _31794 _31795).
Proof. exact (@lem19158 (term457 _31796 _31794 _31795) (term252 _31795) (term458 _31796 _31794 _31795)). Qed.
Lemma lem2970535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2970536 (_31796 : int) (_31794 : int) (_31795 : int) : (term459 _31796 _31794 _31795) = (term460 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970535) (@lem2970534 _31796 _31794 _31795)). Qed.
Lemma lem2970537 (_31796 : int) (_31794 : int) (_31795 : int) : (term450 _31796 _31794 _31795) = (term461 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970536 _31796 _31794 _31795) (@lem2970527 _31796 _31794 _31795)). Qed.
Lemma lem2970538 (_31796 : int) (_31794 : int) (_31795 : int) : (term449 _31796 _31794 _31795) = (term461 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970520 _31796 _31794 _31795) (@lem2970537 _31796 _31794 _31795)). Qed.
Lemma lem2970539 (_31796 : int) (_31794 : int) (_31795 : int) : (term413 _31796 _31794 _31795) = (term461 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970519 _31796 _31794 _31795) (@lem2970538 _31796 _31794 _31795)). Qed.
Lemma lem2970542 (_31794 : int) : (term411 _31794) = (term411 _31794).
Proof. exact (eq_refl (term411 _31794)). Qed.
Lemma lem2970543 (_31796 : int) (_31794 : int) (_31795 : int) : (term414 _31796 _31794 _31795) = (term462 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970542 _31794) (@lem2970539 _31796 _31794 _31795)). Qed.
Lemma lem2970544 (_31796 : int) (_31794 : int) (_31795 : int) : (term462 _31796 _31794 _31795) = (term463 _31796 _31794 _31795).
Proof. exact (@lem19158 (term456 _31796 _31794 _31795) (term252 _31794) (term452 _31796 _31794 _31795)). Qed.
Lemma lem2970551 (_31796 : int) (_31794 : int) (_31795 : int) : (term464 _31796 _31794 _31795) = (term465 _31796 _31794 _31795).
Proof. exact (@lem19158 (term466 _31796 _31794 _31795) (term252 _31794) (term467 _31796 _31794 _31795)). Qed.
Lemma lem2970558 (_31796 : int) (_31794 : int) (_31795 : int) : (term468 _31796 _31794 _31795) = (term469 _31796 _31794 _31795).
Proof. exact (@lem19158 (term470 _31796 _31794 _31795) (term252 _31794) (term471 _31796 _31794 _31795)). Qed.
Lemma lem2970559 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2970560 (_31796 : int) (_31794 : int) (_31795 : int) : (term472 _31796 _31794 _31795) = (term473 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970559) (@lem2970558 _31796 _31794 _31795)). Qed.
Lemma lem2970561 (_31796 : int) (_31794 : int) (_31795 : int) : (term463 _31796 _31794 _31795) = (term474 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2970560 _31796 _31794 _31795) (@lem2970551 _31796 _31794 _31795)). Qed.
Lemma lem2970562 (_31796 : int) (_31794 : int) (_31795 : int) : (term462 _31796 _31794 _31795) = (term474 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970544 _31796 _31794 _31795) (@lem2970561 _31796 _31794 _31795)). Qed.
Lemma lem2970563 (_31796 : int) (_31794 : int) (_31795 : int) : (term414 _31796 _31794 _31795) = (term474 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970543 _31796 _31794 _31795) (@lem2970562 _31796 _31794 _31795)). Qed.
Lemma lem2970564 (_31796 : int) (_31794 : int) (_31795 : int) : (term224 _31796 _31795 _31794) = (term474 _31796 _31794 _31795).
Proof. exact (TRANS (@lem2970428 _31796 _31794 _31795) (@lem2970563 _31796 _31794 _31795)). Qed.
Lemma lem2970586 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term474 _31796 _31794 _31795) : term474 _31796 _31794 _31795.
Proof. exact (h1). Qed.
Lemma lem2970587 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term469 _31796 _31794 _31795) : term469 _31796 _31794 _31795.
Proof. exact (h1). Qed.
Lemma lem2970588 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term475 _31796 _31794 _31795.
Proof. exact (h1). Qed.
Lemma lem2970589 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term470 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2970588 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970591 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term457 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2970589 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970593 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term444 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2970591 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970594 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term252 _31796.
Proof. exact (proj1 (@lem2970591 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970595 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term431 _31794 _31795.
Proof. exact (proj2 (@lem2970593 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970596 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term331 _31794 _31795 _31796.
Proof. exact (proj1 (@lem2970593 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970598 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : (term280 _31794 _31795 _31796) = term140.
Proof. exact (proj1 (@lem2970596 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970600 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term339 _31794 _31795.
Proof. exact (proj1 (@lem2970595 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970602 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2970603 : term476 = term305.
Proof. exact (@lem2970602 term140 term169). Qed.
Lemma lem2970605 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970606 : term169 = term288.
Proof. exact (@lem2970605 term86). Qed.
Lemma lem2970608 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970609 : term140 = term229.
Proof. exact (@lem2970608 (NUMERAL 0)). Qed.
Lemma lem2970610 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2970611 : term477 = term478.
Proof. exact (MK_COMB (@lem2970610) (@lem2970609)). Qed.
Lemma lem2970612 : term305 = term479.
Proof. exact (MK_COMB (@lem2970611) (@lem2970606)). Qed.
Lemma lem2970613 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2970615 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970616 : term305 = term306.
Proof. exact (@lem2970615 (NUMERAL 0) term86). Qed.
Lemma lem2970617 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970618 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970619 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970618 h1) (fun h1 : term306 = True => @lem2970617)). Qed.
Lemma lem2970620 : term306 = True.
Proof. exact (EQ_MP (@lem2970619) (@lem2970617)). Qed.
Lemma lem2970621 : term305 = True.
Proof. exact (TRANS (@lem2970616) (@lem2970620)). Qed.
Lemma lem2970622 : True = term305.
Proof. exact (SYM (@lem2970621)). Qed.
Lemma lem2970623 : term305.
Proof. exact (EQ_MP (@lem2970622) (@lem0)). Qed.
Lemma lem2970624 : term481.
Proof. exact (@lem2970613 (@lem2970623)). Qed.
Lemma lem2970626 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970627 : term305 = term306.
Proof. exact (@lem2970626 (NUMERAL 0) term86). Qed.
Lemma lem2970628 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970629 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970630 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970629 h1) (fun h1 : term306 = True => @lem2970628)). Qed.
Lemma lem2970631 : term306 = True.
Proof. exact (EQ_MP (@lem2970630) (@lem2970628)). Qed.
Lemma lem2970632 : term305 = True.
Proof. exact (TRANS (@lem2970627) (@lem2970631)). Qed.
Lemma lem2970633 : True = term305.
Proof. exact (SYM (@lem2970632)). Qed.
Lemma lem2970634 : term305.
Proof. exact (EQ_MP (@lem2970633) (@lem0)). Qed.
Lemma lem2970635 : term479 = term482.
Proof. exact (@lem2970624 (@lem2970634)). Qed.
Lemma lem2970637 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970638 : term241 = term242.
Proof. exact (@lem2970637 term86 term86). Qed.
Lemma lem2970639 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970640 : term244 = term86.
Proof. exact (EQ_MP (@lem2970639) (@lem940073)). Qed.
Lemma lem2970641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970642 : term242 = term169.
Proof. exact (MK_COMB (@lem2970641) (@lem2970640)). Qed.
Lemma lem2970643 : term241 = term169.
Proof. exact (TRANS (@lem2970638) (@lem2970642)). Qed.
Lemma lem2970645 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2970646 : term373 = term140.
Proof. exact (@lem2970645 term86). Qed.
Lemma lem2970647 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2970648 : term483 = term477.
Proof. exact (MK_COMB (@lem2970647) (@lem2970646)). Qed.
Lemma lem2970649 : term482 = term305.
Proof. exact (MK_COMB (@lem2970648) (@lem2970643)). Qed.
Lemma lem2970651 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970652 : term305 = term306.
Proof. exact (@lem2970651 (NUMERAL 0) term86). Qed.
Lemma lem2970653 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970654 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970655 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970654 h1) (fun h1 : term306 = True => @lem2970653)). Qed.
Lemma lem2970656 : term306 = True.
Proof. exact (EQ_MP (@lem2970655) (@lem2970653)). Qed.
Lemma lem2970657 : term305 = True.
Proof. exact (TRANS (@lem2970652) (@lem2970656)). Qed.
Lemma lem2970658 : term482 = True.
Proof. exact (TRANS (@lem2970649) (@lem2970657)). Qed.
Lemma lem2970659 : term479 = True.
Proof. exact (TRANS (@lem2970635) (@lem2970658)). Qed.
Lemma lem2970660 : term305 = True.
Proof. exact (TRANS (@lem2970612) (@lem2970659)). Qed.
Lemma lem2970661 : term476 = True.
Proof. exact (TRANS (@lem2970603) (@lem2970660)). Qed.
Lemma lem2970662 : True = term476.
Proof. exact (SYM (@lem2970661)). Qed.
Lemma lem2970663 : term476.
Proof. exact (EQ_MP (@lem2970662) (@lem0)). Qed.
Lemma lem2970664 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term484 _31796.
Proof. exact (conj (@lem2970663) (@lem2970594 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970666 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2970667 (_31796 : int) : term486 _31796.
Proof. exact (@lem2970666 term169 (real_of_int _31796)). Qed.
Lemma lem2970668 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term487 _31796.
Proof. exact (@lem2970667 _31796 (@lem2970664 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970669 (_31796 : int) : (term488 _31796) = (real_of_int _31796).
Proof. exact (@lem1982733 (real_of_int _31796)). Qed.
Lemma lem2970670 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2970671 (_31796 : int) : (term489 _31796) = (term251 _31796).
Proof. exact (MK_COMB (@lem2970670) (@lem2970669 _31796)). Qed.
Lemma lem2970672 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2970673 (_31796 : int) : (term487 _31796) = (term252 _31796).
Proof. exact (MK_COMB (@lem2970671 _31796) (@lem2970672)). Qed.
Lemma lem2970674 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term252 _31796.
Proof. exact (EQ_MP (@lem2970673 _31796) (@lem2970668 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970676 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2970677 : term476 = term305.
Proof. exact (@lem2970676 term140 term169). Qed.
Lemma lem2970679 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970680 : term169 = term288.
Proof. exact (@lem2970679 term86). Qed.
Lemma lem2970682 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970683 : term140 = term229.
Proof. exact (@lem2970682 (NUMERAL 0)). Qed.
Lemma lem2970684 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2970685 : term477 = term478.
Proof. exact (MK_COMB (@lem2970684) (@lem2970683)). Qed.
Lemma lem2970686 : term305 = term479.
Proof. exact (MK_COMB (@lem2970685) (@lem2970680)). Qed.
Lemma lem2970687 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2970689 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970690 : term305 = term306.
Proof. exact (@lem2970689 (NUMERAL 0) term86). Qed.
Lemma lem2970691 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970692 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970693 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970692 h1) (fun h1 : term306 = True => @lem2970691)). Qed.
Lemma lem2970694 : term306 = True.
Proof. exact (EQ_MP (@lem2970693) (@lem2970691)). Qed.
Lemma lem2970695 : term305 = True.
Proof. exact (TRANS (@lem2970690) (@lem2970694)). Qed.
Lemma lem2970696 : True = term305.
Proof. exact (SYM (@lem2970695)). Qed.
Lemma lem2970697 : term305.
Proof. exact (EQ_MP (@lem2970696) (@lem0)). Qed.
Lemma lem2970698 : term481.
Proof. exact (@lem2970687 (@lem2970697)). Qed.
Lemma lem2970700 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970701 : term305 = term306.
Proof. exact (@lem2970700 (NUMERAL 0) term86). Qed.
Lemma lem2970702 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970703 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970704 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970703 h1) (fun h1 : term306 = True => @lem2970702)). Qed.
Lemma lem2970705 : term306 = True.
Proof. exact (EQ_MP (@lem2970704) (@lem2970702)). Qed.
Lemma lem2970706 : term305 = True.
Proof. exact (TRANS (@lem2970701) (@lem2970705)). Qed.
Lemma lem2970707 : True = term305.
Proof. exact (SYM (@lem2970706)). Qed.
Lemma lem2970708 : term305.
Proof. exact (EQ_MP (@lem2970707) (@lem0)). Qed.
Lemma lem2970709 : term479 = term482.
Proof. exact (@lem2970698 (@lem2970708)). Qed.
Lemma lem2970711 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970712 : term241 = term242.
Proof. exact (@lem2970711 term86 term86). Qed.
Lemma lem2970713 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970714 : term244 = term86.
Proof. exact (EQ_MP (@lem2970713) (@lem940073)). Qed.
Lemma lem2970715 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970716 : term242 = term169.
Proof. exact (MK_COMB (@lem2970715) (@lem2970714)). Qed.
Lemma lem2970717 : term241 = term169.
Proof. exact (TRANS (@lem2970712) (@lem2970716)). Qed.
Lemma lem2970719 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2970720 : term373 = term140.
Proof. exact (@lem2970719 term86). Qed.
Lemma lem2970721 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2970722 : term483 = term477.
Proof. exact (MK_COMB (@lem2970721) (@lem2970720)). Qed.
Lemma lem2970723 : term482 = term305.
Proof. exact (MK_COMB (@lem2970722) (@lem2970717)). Qed.
Lemma lem2970725 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970726 : term305 = term306.
Proof. exact (@lem2970725 (NUMERAL 0) term86). Qed.
Lemma lem2970727 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970728 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970729 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970728 h1) (fun h1 : term306 = True => @lem2970727)). Qed.
Lemma lem2970730 : term306 = True.
Proof. exact (EQ_MP (@lem2970729) (@lem2970727)). Qed.
Lemma lem2970731 : term305 = True.
Proof. exact (TRANS (@lem2970726) (@lem2970730)). Qed.
Lemma lem2970732 : term482 = True.
Proof. exact (TRANS (@lem2970723) (@lem2970731)). Qed.
Lemma lem2970733 : term479 = True.
Proof. exact (TRANS (@lem2970709) (@lem2970732)). Qed.
Lemma lem2970734 : term305 = True.
Proof. exact (TRANS (@lem2970686) (@lem2970733)). Qed.
Lemma lem2970735 : term476 = True.
Proof. exact (TRANS (@lem2970677) (@lem2970734)). Qed.
Lemma lem2970736 : True = term476.
Proof. exact (SYM (@lem2970735)). Qed.
Lemma lem2970737 : term476.
Proof. exact (EQ_MP (@lem2970736) (@lem0)). Qed.
Lemma lem2970738 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term490 _31794 _31795.
Proof. exact (conj (@lem2970737) (@lem2970600 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970740 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2970741 (_31794 : int) (_31795 : int) : term491 _31794 _31795.
Proof. exact (@lem2970740 term169 (term336 _31794 _31795)). Qed.
Lemma lem2970742 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term492 _31794 _31795.
Proof. exact (@lem2970741 _31794 _31795 (@lem2970738 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970743 (_31794 : int) (_31795 : int) : (term493 _31794 _31795) = (term336 _31794 _31795).
Proof. exact (@lem1982733 (term336 _31794 _31795)). Qed.
Lemma lem2970744 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2970745 (_31794 : int) (_31795 : int) : (term494 _31794 _31795) = (term338 _31794 _31795).
Proof. exact (MK_COMB (@lem2970744) (@lem2970743 _31794 _31795)). Qed.
Lemma lem2970746 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2970747 (_31794 : int) (_31795 : int) : (term492 _31794 _31795) = (term339 _31794 _31795).
Proof. exact (MK_COMB (@lem2970745 _31794 _31795) (@lem2970746)). Qed.
Lemma lem2970748 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term339 _31794 _31795.
Proof. exact (EQ_MP (@lem2970747 _31794 _31795) (@lem2970742 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970750 (y : real) : term495 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2970751 (_31794 : int) (_31795 : int) (_31796 : int) : term496 _31794 _31795 _31796.
Proof. exact (@lem2970750 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2970752 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term497 _31794 _31795 _31796.
Proof. exact (@lem2970751 _31794 _31795 _31796 (@lem2970598 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970753 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term498 _31794 _31795 _31796.
Proof. exact (@lem2970752 _31796 _31794 _31795 h1 term169). Qed.
Lemma lem2970754 (_31794 : int) (_31795 : int) (_31796 : int) : (term498 _31794 _31795 _31796) = ((term499 _31794 _31795 _31796) = term140).
Proof. exact (eq_refl (term498 _31794 _31795 _31796)). Qed.
Lemma lem2970755 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : (term499 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2970754 _31794 _31795 _31796) (@lem2970753 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970756 (_31794 : int) (_31795 : int) (_31796 : int) : (term499 _31794 _31795 _31796) = (term280 _31794 _31795 _31796).
Proof. exact (@lem1982733 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2970757 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2970758 (_31794 : int) (_31795 : int) (_31796 : int) : (term500 _31794 _31795 _31796) = (term282 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2970757) (@lem2970756 _31794 _31795 _31796)). Qed.
Lemma lem2970759 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2970760 (_31794 : int) (_31795 : int) (_31796 : int) : ((term499 _31794 _31795 _31796) = term140) = ((term280 _31794 _31795 _31796) = term140).
Proof. exact (MK_COMB (@lem2970758 _31794 _31795 _31796) (@lem2970759)). Qed.
Lemma lem2970761 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : (term280 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2970760 _31794 _31795 _31796) (@lem2970755 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970762 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term501 _31796 _31794 _31795.
Proof. exact (conj (@lem2970761 _31796 _31794 _31795 h1) (@lem2970748 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970764 (x : real) (y : real) : term502 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2970765 (_31796 : int) (_31794 : int) (_31795 : int) : term503 _31796 _31794 _31795.
Proof. exact (@lem2970764 (term280 _31794 _31795 _31796) (term336 _31794 _31795)). Qed.
Lemma lem2970766 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term504 _31796 _31794 _31795.
Proof. exact (@lem2970765 _31796 _31794 _31795 (@lem2970762 _31796 _31794 _31795 h1)). Qed.
Lemma lem2970767 (_31794 : int) (_31796 : int) (_31795 : int) : (term505 _31796 _31794 _31795) = (term506 _31794 _31796 _31795).
Proof. exact (@lem1982753 (real_of_int _31794) (term257 _31794) (term279 _31795 _31796) (term507 _31795)). Qed.
Lemma lem2970768 (_31794 : int) : (term508 _31794) = (term509 _31794).
Proof. exact (@lem1982715 term232 (real_of_int _31794)). Qed.
Lemma lem2970770 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970771 : term169 = term288.
Proof. exact (@lem2970770 term86). Qed.
Lemma lem2970773 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2970774 : term232 = term233.
Proof. exact (@lem2970773 term86). Qed.
Lemma lem2970775 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970776 : term510 = term511.
Proof. exact (MK_COMB (@lem2970775) (@lem2970774)). Qed.
Lemma lem2970777 : term512 = term513.
Proof. exact (MK_COMB (@lem2970776) (@lem2970771)). Qed.
Lemma lem2970778 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2970780 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970781 : term305 = term306.
Proof. exact (@lem2970780 (NUMERAL 0) term86). Qed.
Lemma lem2970782 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970783 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970784 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970783 h1) (fun h1 : term306 = True => @lem2970782)). Qed.
Lemma lem2970785 : term306 = True.
Proof. exact (EQ_MP (@lem2970784) (@lem2970782)). Qed.
Lemma lem2970786 : term305 = True.
Proof. exact (TRANS (@lem2970781) (@lem2970785)). Qed.
Lemma lem2970787 : True = term305.
Proof. exact (SYM (@lem2970786)). Qed.
Lemma lem2970788 : term305.
Proof. exact (EQ_MP (@lem2970787) (@lem0)). Qed.
Lemma lem2970789 : term515.
Proof. exact (@lem2970778 (@lem2970788)). Qed.
Lemma lem2970791 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970792 : term305 = term306.
Proof. exact (@lem2970791 (NUMERAL 0) term86). Qed.
Lemma lem2970793 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970794 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970795 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970794 h1) (fun h1 : term306 = True => @lem2970793)). Qed.
Lemma lem2970796 : term306 = True.
Proof. exact (EQ_MP (@lem2970795) (@lem2970793)). Qed.
Lemma lem2970797 : term305 = True.
Proof. exact (TRANS (@lem2970792) (@lem2970796)). Qed.
Lemma lem2970798 : True = term305.
Proof. exact (SYM (@lem2970797)). Qed.
Lemma lem2970799 : term305.
Proof. exact (EQ_MP (@lem2970798) (@lem0)). Qed.
Lemma lem2970800 : term516.
Proof. exact (@lem2970789 (@lem2970799)). Qed.
Lemma lem2970802 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970803 : term305 = term306.
Proof. exact (@lem2970802 (NUMERAL 0) term86). Qed.
Lemma lem2970804 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970805 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970806 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970805 h1) (fun h1 : term306 = True => @lem2970804)). Qed.
Lemma lem2970807 : term306 = True.
Proof. exact (EQ_MP (@lem2970806) (@lem2970804)). Qed.
Lemma lem2970808 : term305 = True.
Proof. exact (TRANS (@lem2970803) (@lem2970807)). Qed.
Lemma lem2970809 : True = term305.
Proof. exact (SYM (@lem2970808)). Qed.
Lemma lem2970810 : term305.
Proof. exact (EQ_MP (@lem2970809) (@lem0)). Qed.
Lemma lem2970811 : term517.
Proof. exact (@lem2970800 (@lem2970810)). Qed.
Lemma lem2970813 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970814 : term241 = term242.
Proof. exact (@lem2970813 term86 term86). Qed.
Lemma lem2970815 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970816 : term244 = term86.
Proof. exact (EQ_MP (@lem2970815) (@lem940073)). Qed.
Lemma lem2970817 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970818 : term242 = term169.
Proof. exact (MK_COMB (@lem2970817) (@lem2970816)). Qed.
Lemma lem2970819 : term241 = term169.
Proof. exact (TRANS (@lem2970814) (@lem2970818)). Qed.
Lemma lem2970821 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2970822 : term289 = term292.
Proof. exact (@lem2970821 term86 term86). Qed.
Lemma lem2970823 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970824 : term244 = term86.
Proof. exact (EQ_MP (@lem2970823) (@lem940073)). Qed.
Lemma lem2970825 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970826 : term242 = term169.
Proof. exact (MK_COMB (@lem2970825) (@lem2970824)). Qed.
Lemma lem2970827 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2970828 : term292 = term232.
Proof. exact (MK_COMB (@lem2970827) (@lem2970826)). Qed.
Lemma lem2970829 : term289 = term232.
Proof. exact (TRANS (@lem2970822) (@lem2970828)). Qed.
Lemma lem2970830 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970831 : term518 = term510.
Proof. exact (MK_COMB (@lem2970830) (@lem2970829)). Qed.
Lemma lem2970832 : term519 = term512.
Proof. exact (MK_COMB (@lem2970831) (@lem2970819)). Qed.
Lemma lem2970834 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2970835 : term512 = term140.
Proof. exact (@lem2970834 term86). Qed.
Lemma lem2970836 : term519 = term140.
Proof. exact (TRANS (@lem2970832) (@lem2970835)). Qed.
Lemma lem2970837 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970838 : term521 = term371.
Proof. exact (MK_COMB (@lem2970837) (@lem2970836)). Qed.
Lemma lem2970839 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2970840 : term522 = term373.
Proof. exact (MK_COMB (@lem2970838) (@lem2970839)). Qed.
Lemma lem2970842 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2970843 : term373 = term140.
Proof. exact (@lem2970842 term86). Qed.
Lemma lem2970844 : term522 = term140.
Proof. exact (TRANS (@lem2970840) (@lem2970843)). Qed.
Lemma lem2970846 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970847 : term241 = term242.
Proof. exact (@lem2970846 term86 term86). Qed.
Lemma lem2970848 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970849 : term244 = term86.
Proof. exact (EQ_MP (@lem2970848) (@lem940073)). Qed.
Lemma lem2970850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970851 : term242 = term169.
Proof. exact (MK_COMB (@lem2970850) (@lem2970849)). Qed.
Lemma lem2970852 : term241 = term169.
Proof. exact (TRANS (@lem2970847) (@lem2970851)). Qed.
Lemma lem2970853 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2970854 : term375 = term373.
Proof. exact (MK_COMB (@lem2970853) (@lem2970852)). Qed.
Lemma lem2970856 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2970857 : term373 = term140.
Proof. exact (@lem2970856 term86). Qed.
Lemma lem2970858 : term375 = term140.
Proof. exact (TRANS (@lem2970854) (@lem2970857)). Qed.
Lemma lem2970859 : term140 = term375.
Proof. exact (SYM (@lem2970858)). Qed.
Lemma lem2970860 : term522 = term375.
Proof. exact (TRANS (@lem2970844) (@lem2970859)). Qed.
Lemma lem2970861 : term513 = term229.
Proof. exact (@lem2970811 (@lem2970860)). Qed.
Lemma lem2970862 : term512 = term229.
Proof. exact (TRANS (@lem2970777) (@lem2970861)). Qed.
Lemma lem2970864 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2970865 : term229 = term140.
Proof. exact (@lem2970864 term140). Qed.
Lemma lem2970866 : term512 = term140.
Proof. exact (TRANS (@lem2970862) (@lem2970865)). Qed.
Lemma lem2970867 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970868 : term523 = term371.
Proof. exact (MK_COMB (@lem2970867) (@lem2970866)). Qed.
Lemma lem2970869 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2970870 (_31794 : int) : (term509 _31794) = (term524 _31794).
Proof. exact (MK_COMB (@lem2970868) (@lem2970869 _31794)). Qed.
Lemma lem2970871 (_31794 : int) : (term508 _31794) = (term524 _31794).
Proof. exact (TRANS (@lem2970768 _31794) (@lem2970870 _31794)). Qed.
Lemma lem2970872 (_31794 : int) : (term524 _31794) = term140.
Proof. exact (@lem1982719 (real_of_int _31794)). Qed.
Lemma lem2970873 (_31794 : int) : (term508 _31794) = term140.
Proof. exact (TRANS (@lem2970871 _31794) (@lem2970872 _31794)). Qed.
Lemma lem2970874 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970875 (_31794 : int) : (term525 _31794) = term526.
Proof. exact (MK_COMB (@lem2970874) (@lem2970873 _31794)). Qed.
Lemma lem2970876 (_31795 : int) (_31796 : int) : (term527 _31796 _31795) = (term528 _31795 _31796).
Proof. exact (@lem1982753 (term276 _31795) (term157 _31795) (term257 _31796) term232). Qed.
Lemma lem2970877 (_31795 : int) : (term529 _31795) = (term530 _31795).
Proof. exact (@lem1982711 term270 term154 (real_of_int _31795)). Qed.
Lemma lem2970879 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2970880 : term154 = term260.
Proof. exact (@lem2970879 term2). Qed.
Lemma lem2970882 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2970883 : term270 = term273.
Proof. exact (@lem2970882 term2). Qed.
Lemma lem2970884 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970885 : term531 = term532.
Proof. exact (MK_COMB (@lem2970884) (@lem2970883)). Qed.
Lemma lem2970886 : term533 = term534.
Proof. exact (MK_COMB (@lem2970885) (@lem2970880)). Qed.
Lemma lem2970887 : term535.
Proof. exact (@lem1981473 term270 term169 term154 term169 term140 term169). Qed.
Lemma lem2970889 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970890 : term305 = term306.
Proof. exact (@lem2970889 (NUMERAL 0) term86). Qed.
Lemma lem2970891 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970892 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970893 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970892 h1) (fun h1 : term306 = True => @lem2970891)). Qed.
Lemma lem2970894 : term306 = True.
Proof. exact (EQ_MP (@lem2970893) (@lem2970891)). Qed.
Lemma lem2970895 : term305 = True.
Proof. exact (TRANS (@lem2970890) (@lem2970894)). Qed.
Lemma lem2970896 : True = term305.
Proof. exact (SYM (@lem2970895)). Qed.
Lemma lem2970897 : term305.
Proof. exact (EQ_MP (@lem2970896) (@lem0)). Qed.
Lemma lem2970898 : term536.
Proof. exact (@lem2970887 (@lem2970897)). Qed.
Lemma lem2970900 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970901 : term305 = term306.
Proof. exact (@lem2970900 (NUMERAL 0) term86). Qed.
Lemma lem2970902 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970903 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970904 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970903 h1) (fun h1 : term306 = True => @lem2970902)). Qed.
Lemma lem2970905 : term306 = True.
Proof. exact (EQ_MP (@lem2970904) (@lem2970902)). Qed.
Lemma lem2970906 : term305 = True.
Proof. exact (TRANS (@lem2970901) (@lem2970905)). Qed.
Lemma lem2970907 : True = term305.
Proof. exact (SYM (@lem2970906)). Qed.
Lemma lem2970908 : term305.
Proof. exact (EQ_MP (@lem2970907) (@lem0)). Qed.
Lemma lem2970909 : term537.
Proof. exact (@lem2970898 (@lem2970908)). Qed.
Lemma lem2970911 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2970912 : term305 = term306.
Proof. exact (@lem2970911 (NUMERAL 0) term86). Qed.
Lemma lem2970913 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2970914 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2970915 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2970914 h1) (fun h1 : term306 = True => @lem2970913)). Qed.
Lemma lem2970916 : term306 = True.
Proof. exact (EQ_MP (@lem2970915) (@lem2970913)). Qed.
Lemma lem2970917 : term305 = True.
Proof. exact (TRANS (@lem2970912) (@lem2970916)). Qed.
Lemma lem2970918 : True = term305.
Proof. exact (SYM (@lem2970917)). Qed.
Lemma lem2970919 : term305.
Proof. exact (EQ_MP (@lem2970918) (@lem0)). Qed.
Lemma lem2970920 : term538.
Proof. exact (@lem2970909 (@lem2970919)). Qed.
Lemma lem2970922 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970923 : term311 = term312.
Proof. exact (@lem2970922 term2 term86). Qed.
Lemma lem2970924 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2970925 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2970926 : term314 = term2.
Proof. exact (EQ_MP (@lem2970925) (@lem2970924)). Qed.
Lemma lem2970927 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970928 : term312 = term154.
Proof. exact (MK_COMB (@lem2970927) (@lem2970926)). Qed.
Lemma lem2970929 : term311 = term154.
Proof. exact (TRANS (@lem2970923) (@lem2970928)). Qed.
Lemma lem2970931 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2970932 : term539 = term540.
Proof. exact (@lem2970931 term2 term86). Qed.
Lemma lem2970933 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2970934 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2970935 : term314 = term2.
Proof. exact (EQ_MP (@lem2970934) (@lem2970933)). Qed.
Lemma lem2970936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970937 : term312 = term154.
Proof. exact (MK_COMB (@lem2970936) (@lem2970935)). Qed.
Lemma lem2970938 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2970939 : term540 = term270.
Proof. exact (MK_COMB (@lem2970938) (@lem2970937)). Qed.
Lemma lem2970940 : term539 = term270.
Proof. exact (TRANS (@lem2970932) (@lem2970939)). Qed.
Lemma lem2970941 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970942 : term541 = term531.
Proof. exact (MK_COMB (@lem2970941) (@lem2970940)). Qed.
Lemma lem2970943 : term542 = term533.
Proof. exact (MK_COMB (@lem2970942) (@lem2970929)). Qed.
Lemma lem2970945 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2970946 : term533 = term140.
Proof. exact (@lem2970945 term2). Qed.
Lemma lem2970947 : term542 = term140.
Proof. exact (TRANS (@lem2970943) (@lem2970946)). Qed.
Lemma lem2970948 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970949 : term543 = term371.
Proof. exact (MK_COMB (@lem2970948) (@lem2970947)). Qed.
Lemma lem2970950 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2970951 : term544 = term373.
Proof. exact (MK_COMB (@lem2970949) (@lem2970950)). Qed.
Lemma lem2970953 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2970954 : term373 = term140.
Proof. exact (@lem2970953 term86). Qed.
Lemma lem2970955 : term544 = term140.
Proof. exact (TRANS (@lem2970951) (@lem2970954)). Qed.
Lemma lem2970957 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2970958 : term241 = term242.
Proof. exact (@lem2970957 term86 term86). Qed.
Lemma lem2970959 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2970960 : term244 = term86.
Proof. exact (EQ_MP (@lem2970959) (@lem940073)). Qed.
Lemma lem2970961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2970962 : term242 = term169.
Proof. exact (MK_COMB (@lem2970961) (@lem2970960)). Qed.
Lemma lem2970963 : term241 = term169.
Proof. exact (TRANS (@lem2970958) (@lem2970962)). Qed.
Lemma lem2970964 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2970965 : term375 = term373.
Proof. exact (MK_COMB (@lem2970964) (@lem2970963)). Qed.
Lemma lem2970967 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2970968 : term373 = term140.
Proof. exact (@lem2970967 term86). Qed.
Lemma lem2970969 : term375 = term140.
Proof. exact (TRANS (@lem2970965) (@lem2970968)). Qed.
Lemma lem2970970 : term140 = term375.
Proof. exact (SYM (@lem2970969)). Qed.
Lemma lem2970971 : term544 = term375.
Proof. exact (TRANS (@lem2970955) (@lem2970970)). Qed.
Lemma lem2970972 : term534 = term229.
Proof. exact (@lem2970920 (@lem2970971)). Qed.
Lemma lem2970973 : term533 = term229.
Proof. exact (TRANS (@lem2970886) (@lem2970972)). Qed.
Lemma lem2970975 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2970976 : term229 = term140.
Proof. exact (@lem2970975 term140). Qed.
Lemma lem2970977 : term533 = term140.
Proof. exact (TRANS (@lem2970973) (@lem2970976)). Qed.
Lemma lem2970978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2970979 : term545 = term371.
Proof. exact (MK_COMB (@lem2970978) (@lem2970977)). Qed.
Lemma lem2970980 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2970981 (_31795 : int) : (term530 _31795) = (term524 _31795).
Proof. exact (MK_COMB (@lem2970979) (@lem2970980 _31795)). Qed.
Lemma lem2970982 (_31795 : int) : (term529 _31795) = (term524 _31795).
Proof. exact (TRANS (@lem2970877 _31795) (@lem2970981 _31795)). Qed.
Lemma lem2970983 (_31795 : int) : (term524 _31795) = term140.
Proof. exact (@lem1982719 (real_of_int _31795)). Qed.
Lemma lem2970984 (_31795 : int) : (term529 _31795) = term140.
Proof. exact (TRANS (@lem2970982 _31795) (@lem2970983 _31795)). Qed.
Lemma lem2970985 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2970986 (_31795 : int) : (term546 _31795) = term526.
Proof. exact (MK_COMB (@lem2970985) (@lem2970984 _31795)). Qed.
Lemma lem2970987 (_31796 : int) : (term296 _31796) = (term296 _31796).
Proof. exact (eq_refl (term296 _31796)). Qed.
Lemma lem2970988 (_31795 : int) (_31796 : int) : (term528 _31795 _31796) = (term547 _31796).
Proof. exact (MK_COMB (@lem2970986 _31795) (@lem2970987 _31796)). Qed.
Lemma lem2970989 (_31795 : int) (_31796 : int) : (term527 _31796 _31795) = (term547 _31796).
Proof. exact (TRANS (@lem2970876 _31795 _31796) (@lem2970988 _31795 _31796)). Qed.
Lemma lem2970990 (_31796 : int) : (term547 _31796) = (term296 _31796).
Proof. exact (@lem1982721 (term296 _31796)). Qed.
Lemma lem2970991 (_31795 : int) (_31796 : int) : (term527 _31796 _31795) = (term296 _31796).
Proof. exact (TRANS (@lem2970989 _31795 _31796) (@lem2970990 _31796)). Qed.
Lemma lem2970992 (_31794 : int) (_31795 : int) (_31796 : int) : (term506 _31794 _31796 _31795) = (term547 _31796).
Proof. exact (MK_COMB (@lem2970875 _31794) (@lem2970991 _31795 _31796)). Qed.
Lemma lem2970993 (_31794 : int) (_31795 : int) (_31796 : int) : (term505 _31796 _31794 _31795) = (term547 _31796).
Proof. exact (TRANS (@lem2970767 _31794 _31796 _31795) (@lem2970992 _31794 _31795 _31796)). Qed.
Lemma lem2970994 (_31796 : int) : (term547 _31796) = (term296 _31796).
Proof. exact (@lem1982721 (term296 _31796)). Qed.
Lemma lem2970995 (_31794 : int) (_31795 : int) (_31796 : int) : (term505 _31796 _31794 _31795) = (term296 _31796).
Proof. exact (TRANS (@lem2970993 _31794 _31795 _31796) (@lem2970994 _31796)). Qed.
Lemma lem2970996 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2970997 (_31794 : int) (_31795 : int) (_31796 : int) : (term548 _31796 _31794 _31795) = (term549 _31796).
Proof. exact (MK_COMB (@lem2970996) (@lem2970995 _31794 _31795 _31796)). Qed.
Lemma lem2970998 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2970999 (_31794 : int) (_31795 : int) (_31796 : int) : (term504 _31796 _31794 _31795) = (term550 _31796).
Proof. exact (MK_COMB (@lem2970997 _31794 _31795 _31796) (@lem2970998)). Qed.
Lemma lem2971000 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term550 _31796.
Proof. exact (EQ_MP (@lem2970999 _31794 _31795 _31796) (@lem2970766 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971002 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2971003 : term476 = term305.
Proof. exact (@lem2971002 term140 term169). Qed.
Lemma lem2971005 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971006 : term169 = term288.
Proof. exact (@lem2971005 term86). Qed.
Lemma lem2971008 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971009 : term140 = term229.
Proof. exact (@lem2971008 (NUMERAL 0)). Qed.
Lemma lem2971010 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2971011 : term477 = term478.
Proof. exact (MK_COMB (@lem2971010) (@lem2971009)). Qed.
Lemma lem2971012 : term305 = term479.
Proof. exact (MK_COMB (@lem2971011) (@lem2971006)). Qed.
Lemma lem2971013 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2971015 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971016 : term305 = term306.
Proof. exact (@lem2971015 (NUMERAL 0) term86). Qed.
Lemma lem2971017 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971018 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971019 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971018 h1) (fun h1 : term306 = True => @lem2971017)). Qed.
Lemma lem2971020 : term306 = True.
Proof. exact (EQ_MP (@lem2971019) (@lem2971017)). Qed.
Lemma lem2971021 : term305 = True.
Proof. exact (TRANS (@lem2971016) (@lem2971020)). Qed.
Lemma lem2971022 : True = term305.
Proof. exact (SYM (@lem2971021)). Qed.
Lemma lem2971023 : term305.
Proof. exact (EQ_MP (@lem2971022) (@lem0)). Qed.
Lemma lem2971024 : term481.
Proof. exact (@lem2971013 (@lem2971023)). Qed.
Lemma lem2971026 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971027 : term305 = term306.
Proof. exact (@lem2971026 (NUMERAL 0) term86). Qed.
Lemma lem2971028 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971029 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971030 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971029 h1) (fun h1 : term306 = True => @lem2971028)). Qed.
Lemma lem2971031 : term306 = True.
Proof. exact (EQ_MP (@lem2971030) (@lem2971028)). Qed.
Lemma lem2971032 : term305 = True.
Proof. exact (TRANS (@lem2971027) (@lem2971031)). Qed.
Lemma lem2971033 : True = term305.
Proof. exact (SYM (@lem2971032)). Qed.
Lemma lem2971034 : term305.
Proof. exact (EQ_MP (@lem2971033) (@lem0)). Qed.
Lemma lem2971035 : term479 = term482.
Proof. exact (@lem2971024 (@lem2971034)). Qed.
Lemma lem2971037 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971038 : term241 = term242.
Proof. exact (@lem2971037 term86 term86). Qed.
Lemma lem2971039 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971040 : term244 = term86.
Proof. exact (EQ_MP (@lem2971039) (@lem940073)). Qed.
Lemma lem2971041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971042 : term242 = term169.
Proof. exact (MK_COMB (@lem2971041) (@lem2971040)). Qed.
Lemma lem2971043 : term241 = term169.
Proof. exact (TRANS (@lem2971038) (@lem2971042)). Qed.
Lemma lem2971045 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971046 : term373 = term140.
Proof. exact (@lem2971045 term86). Qed.
Lemma lem2971047 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2971048 : term483 = term477.
Proof. exact (MK_COMB (@lem2971047) (@lem2971046)). Qed.
Lemma lem2971049 : term482 = term305.
Proof. exact (MK_COMB (@lem2971048) (@lem2971043)). Qed.
Lemma lem2971051 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971052 : term305 = term306.
Proof. exact (@lem2971051 (NUMERAL 0) term86). Qed.
Lemma lem2971053 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971054 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971055 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971054 h1) (fun h1 : term306 = True => @lem2971053)). Qed.
Lemma lem2971056 : term306 = True.
Proof. exact (EQ_MP (@lem2971055) (@lem2971053)). Qed.
Lemma lem2971057 : term305 = True.
Proof. exact (TRANS (@lem2971052) (@lem2971056)). Qed.
Lemma lem2971058 : term482 = True.
Proof. exact (TRANS (@lem2971049) (@lem2971057)). Qed.
Lemma lem2971059 : term479 = True.
Proof. exact (TRANS (@lem2971035) (@lem2971058)). Qed.
Lemma lem2971060 : term305 = True.
Proof. exact (TRANS (@lem2971012) (@lem2971059)). Qed.
Lemma lem2971061 : term476 = True.
Proof. exact (TRANS (@lem2971003) (@lem2971060)). Qed.
Lemma lem2971062 : True = term476.
Proof. exact (SYM (@lem2971061)). Qed.
Lemma lem2971063 : term476.
Proof. exact (EQ_MP (@lem2971062) (@lem0)). Qed.
Lemma lem2971064 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term551 _31796.
Proof. exact (conj (@lem2971063) (@lem2971000 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971066 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2971067 (_31796 : int) : term552 _31796.
Proof. exact (@lem2971066 term169 (term296 _31796)). Qed.
Lemma lem2971068 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term553 _31796.
Proof. exact (@lem2971067 _31796 (@lem2971064 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971069 (_31796 : int) : (term554 _31796) = (term296 _31796).
Proof. exact (@lem1982733 (term296 _31796)). Qed.
Lemma lem2971070 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2971071 (_31796 : int) : (term555 _31796) = (term549 _31796).
Proof. exact (MK_COMB (@lem2971070) (@lem2971069 _31796)). Qed.
Lemma lem2971072 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2971073 (_31796 : int) : (term553 _31796) = (term550 _31796).
Proof. exact (MK_COMB (@lem2971071 _31796) (@lem2971072)). Qed.
Lemma lem2971074 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term550 _31796.
Proof. exact (EQ_MP (@lem2971073 _31796) (@lem2971068 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971075 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term556 _31796.
Proof. exact (conj (@lem2971074 _31796 _31794 _31795 h1) (@lem2970674 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971077 (x : real) (y : real) : term557 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2971078 (_31796 : int) : term558 _31796.
Proof. exact (@lem2971077 (term296 _31796) (real_of_int _31796)). Qed.
Lemma lem2971079 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term559 _31796.
Proof. exact (@lem2971078 _31796 (@lem2971075 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971080 (_31796 : int) : (term560 _31796) = (term561 _31796).
Proof. exact (@lem1982759 (term257 _31796) (real_of_int _31796) term232). Qed.
Lemma lem2971081 (_31796 : int) : (term562 _31796) = (term509 _31796).
Proof. exact (@lem1982713 term232 (real_of_int _31796)). Qed.
Lemma lem2971083 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971084 : term169 = term288.
Proof. exact (@lem2971083 term86). Qed.
Lemma lem2971086 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971087 : term232 = term233.
Proof. exact (@lem2971086 term86). Qed.
Lemma lem2971088 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971089 : term510 = term511.
Proof. exact (MK_COMB (@lem2971088) (@lem2971087)). Qed.
Lemma lem2971090 : term512 = term513.
Proof. exact (MK_COMB (@lem2971089) (@lem2971084)). Qed.
Lemma lem2971091 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2971093 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971094 : term305 = term306.
Proof. exact (@lem2971093 (NUMERAL 0) term86). Qed.
Lemma lem2971095 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971096 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971097 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971096 h1) (fun h1 : term306 = True => @lem2971095)). Qed.
Lemma lem2971098 : term306 = True.
Proof. exact (EQ_MP (@lem2971097) (@lem2971095)). Qed.
Lemma lem2971099 : term305 = True.
Proof. exact (TRANS (@lem2971094) (@lem2971098)). Qed.
Lemma lem2971100 : True = term305.
Proof. exact (SYM (@lem2971099)). Qed.
Lemma lem2971101 : term305.
Proof. exact (EQ_MP (@lem2971100) (@lem0)). Qed.
Lemma lem2971102 : term515.
Proof. exact (@lem2971091 (@lem2971101)). Qed.
Lemma lem2971104 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971105 : term305 = term306.
Proof. exact (@lem2971104 (NUMERAL 0) term86). Qed.
Lemma lem2971106 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971107 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971108 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971107 h1) (fun h1 : term306 = True => @lem2971106)). Qed.
Lemma lem2971109 : term306 = True.
Proof. exact (EQ_MP (@lem2971108) (@lem2971106)). Qed.
Lemma lem2971110 : term305 = True.
Proof. exact (TRANS (@lem2971105) (@lem2971109)). Qed.
Lemma lem2971111 : True = term305.
Proof. exact (SYM (@lem2971110)). Qed.
Lemma lem2971112 : term305.
Proof. exact (EQ_MP (@lem2971111) (@lem0)). Qed.
Lemma lem2971113 : term516.
Proof. exact (@lem2971102 (@lem2971112)). Qed.
Lemma lem2971115 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971116 : term305 = term306.
Proof. exact (@lem2971115 (NUMERAL 0) term86). Qed.
Lemma lem2971117 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971118 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971119 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971118 h1) (fun h1 : term306 = True => @lem2971117)). Qed.
Lemma lem2971120 : term306 = True.
Proof. exact (EQ_MP (@lem2971119) (@lem2971117)). Qed.
Lemma lem2971121 : term305 = True.
Proof. exact (TRANS (@lem2971116) (@lem2971120)). Qed.
Lemma lem2971122 : True = term305.
Proof. exact (SYM (@lem2971121)). Qed.
Lemma lem2971123 : term305.
Proof. exact (EQ_MP (@lem2971122) (@lem0)). Qed.
Lemma lem2971124 : term517.
Proof. exact (@lem2971113 (@lem2971123)). Qed.
Lemma lem2971126 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971127 : term241 = term242.
Proof. exact (@lem2971126 term86 term86). Qed.
Lemma lem2971128 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971129 : term244 = term86.
Proof. exact (EQ_MP (@lem2971128) (@lem940073)). Qed.
Lemma lem2971130 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971131 : term242 = term169.
Proof. exact (MK_COMB (@lem2971130) (@lem2971129)). Qed.
Lemma lem2971132 : term241 = term169.
Proof. exact (TRANS (@lem2971127) (@lem2971131)). Qed.
Lemma lem2971134 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2971135 : term289 = term292.
Proof. exact (@lem2971134 term86 term86). Qed.
Lemma lem2971136 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971137 : term244 = term86.
Proof. exact (EQ_MP (@lem2971136) (@lem940073)). Qed.
Lemma lem2971138 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971139 : term242 = term169.
Proof. exact (MK_COMB (@lem2971138) (@lem2971137)). Qed.
Lemma lem2971140 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2971141 : term292 = term232.
Proof. exact (MK_COMB (@lem2971140) (@lem2971139)). Qed.
Lemma lem2971142 : term289 = term232.
Proof. exact (TRANS (@lem2971135) (@lem2971141)). Qed.
Lemma lem2971143 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971144 : term518 = term510.
Proof. exact (MK_COMB (@lem2971143) (@lem2971142)). Qed.
Lemma lem2971145 : term519 = term512.
Proof. exact (MK_COMB (@lem2971144) (@lem2971132)). Qed.
Lemma lem2971147 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2971148 : term512 = term140.
Proof. exact (@lem2971147 term86). Qed.
Lemma lem2971149 : term519 = term140.
Proof. exact (TRANS (@lem2971145) (@lem2971148)). Qed.
Lemma lem2971150 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971151 : term521 = term371.
Proof. exact (MK_COMB (@lem2971150) (@lem2971149)). Qed.
Lemma lem2971152 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2971153 : term522 = term373.
Proof. exact (MK_COMB (@lem2971151) (@lem2971152)). Qed.
Lemma lem2971155 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971156 : term373 = term140.
Proof. exact (@lem2971155 term86). Qed.
Lemma lem2971157 : term522 = term140.
Proof. exact (TRANS (@lem2971153) (@lem2971156)). Qed.
Lemma lem2971159 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971160 : term241 = term242.
Proof. exact (@lem2971159 term86 term86). Qed.
Lemma lem2971161 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971162 : term244 = term86.
Proof. exact (EQ_MP (@lem2971161) (@lem940073)). Qed.
Lemma lem2971163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971164 : term242 = term169.
Proof. exact (MK_COMB (@lem2971163) (@lem2971162)). Qed.
Lemma lem2971165 : term241 = term169.
Proof. exact (TRANS (@lem2971160) (@lem2971164)). Qed.
Lemma lem2971166 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2971167 : term375 = term373.
Proof. exact (MK_COMB (@lem2971166) (@lem2971165)). Qed.
Lemma lem2971169 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971170 : term373 = term140.
Proof. exact (@lem2971169 term86). Qed.
Lemma lem2971171 : term375 = term140.
Proof. exact (TRANS (@lem2971167) (@lem2971170)). Qed.
Lemma lem2971172 : term140 = term375.
Proof. exact (SYM (@lem2971171)). Qed.
Lemma lem2971173 : term522 = term375.
Proof. exact (TRANS (@lem2971157) (@lem2971172)). Qed.
Lemma lem2971174 : term513 = term229.
Proof. exact (@lem2971124 (@lem2971173)). Qed.
Lemma lem2971175 : term512 = term229.
Proof. exact (TRANS (@lem2971090) (@lem2971174)). Qed.
Lemma lem2971177 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2971178 : term229 = term140.
Proof. exact (@lem2971177 term140). Qed.
Lemma lem2971179 : term512 = term140.
Proof. exact (TRANS (@lem2971175) (@lem2971178)). Qed.
Lemma lem2971180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971181 : term523 = term371.
Proof. exact (MK_COMB (@lem2971180) (@lem2971179)). Qed.
Lemma lem2971182 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2971183 (_31796 : int) : (term509 _31796) = (term524 _31796).
Proof. exact (MK_COMB (@lem2971181) (@lem2971182 _31796)). Qed.
Lemma lem2971184 (_31796 : int) : (term562 _31796) = (term524 _31796).
Proof. exact (TRANS (@lem2971081 _31796) (@lem2971183 _31796)). Qed.
Lemma lem2971185 (_31796 : int) : (term524 _31796) = term140.
Proof. exact (@lem1982719 (real_of_int _31796)). Qed.
Lemma lem2971186 (_31796 : int) : (term562 _31796) = term140.
Proof. exact (TRANS (@lem2971184 _31796) (@lem2971185 _31796)). Qed.
Lemma lem2971187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971188 (_31796 : int) : (term563 _31796) = term526.
Proof. exact (MK_COMB (@lem2971187) (@lem2971186 _31796)). Qed.
Lemma lem2971189 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem2971190 (_31796 : int) : (term561 _31796) = term564.
Proof. exact (MK_COMB (@lem2971188 _31796) (@lem2971189)). Qed.
Lemma lem2971191 (_31796 : int) : (term560 _31796) = term564.
Proof. exact (TRANS (@lem2971080 _31796) (@lem2971190 _31796)). Qed.
Lemma lem2971192 : term564 = term232.
Proof. exact (@lem1982721 term232). Qed.
Lemma lem2971193 (_31796 : int) : (term560 _31796) = term232.
Proof. exact (TRANS (@lem2971191 _31796) (@lem2971192)). Qed.
Lemma lem2971194 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2971195 (_31796 : int) : (term565 _31796) = term566.
Proof. exact (MK_COMB (@lem2971194) (@lem2971193 _31796)). Qed.
Lemma lem2971196 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2971197 (_31796 : int) : (term559 _31796) = term567.
Proof. exact (MK_COMB (@lem2971195 _31796) (@lem2971196)). Qed.
Lemma lem2971198 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : term567.
Proof. exact (EQ_MP (@lem2971197 _31796) (@lem2971079 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971200 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2971201 : term567 = term568.
Proof. exact (@lem2971200 term140 term232). Qed.
Lemma lem2971203 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971204 : term232 = term233.
Proof. exact (@lem2971203 term86). Qed.
Lemma lem2971206 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971207 : term140 = term229.
Proof. exact (@lem2971206 (NUMERAL 0)). Qed.
Lemma lem2971208 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2971209 : term142 = term569.
Proof. exact (MK_COMB (@lem2971208) (@lem2971207)). Qed.
Lemma lem2971210 : term568 = term570.
Proof. exact (MK_COMB (@lem2971209) (@lem2971204)). Qed.
Lemma lem2971211 : term571.
Proof. exact (@lem1980026 term140 term169 term232 term169). Qed.
Lemma lem2971213 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971214 : term305 = term306.
Proof. exact (@lem2971213 (NUMERAL 0) term86). Qed.
Lemma lem2971215 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971216 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971217 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971216 h1) (fun h1 : term306 = True => @lem2971215)). Qed.
Lemma lem2971218 : term306 = True.
Proof. exact (EQ_MP (@lem2971217) (@lem2971215)). Qed.
Lemma lem2971219 : term305 = True.
Proof. exact (TRANS (@lem2971214) (@lem2971218)). Qed.
Lemma lem2971220 : True = term305.
Proof. exact (SYM (@lem2971219)). Qed.
Lemma lem2971221 : term305.
Proof. exact (EQ_MP (@lem2971220) (@lem0)). Qed.
Lemma lem2971222 : term572.
Proof. exact (@lem2971211 (@lem2971221)). Qed.
Lemma lem2971224 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971225 : term305 = term306.
Proof. exact (@lem2971224 (NUMERAL 0) term86). Qed.
Lemma lem2971226 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971227 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971228 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971227 h1) (fun h1 : term306 = True => @lem2971226)). Qed.
Lemma lem2971229 : term306 = True.
Proof. exact (EQ_MP (@lem2971228) (@lem2971226)). Qed.
Lemma lem2971230 : term305 = True.
Proof. exact (TRANS (@lem2971225) (@lem2971229)). Qed.
Lemma lem2971231 : True = term305.
Proof. exact (SYM (@lem2971230)). Qed.
Lemma lem2971232 : term305.
Proof. exact (EQ_MP (@lem2971231) (@lem0)). Qed.
Lemma lem2971233 : term570 = term573.
Proof. exact (@lem2971222 (@lem2971232)). Qed.
Lemma lem2971235 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2971236 : term289 = term292.
Proof. exact (@lem2971235 term86 term86). Qed.
Lemma lem2971237 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971238 : term244 = term86.
Proof. exact (EQ_MP (@lem2971237) (@lem940073)). Qed.
Lemma lem2971239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971240 : term242 = term169.
Proof. exact (MK_COMB (@lem2971239) (@lem2971238)). Qed.
Lemma lem2971241 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2971242 : term292 = term232.
Proof. exact (MK_COMB (@lem2971241) (@lem2971240)). Qed.
Lemma lem2971243 : term289 = term232.
Proof. exact (TRANS (@lem2971236) (@lem2971242)). Qed.
Lemma lem2971245 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971246 : term373 = term140.
Proof. exact (@lem2971245 term86). Qed.
Lemma lem2971247 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2971248 : term574 = term142.
Proof. exact (MK_COMB (@lem2971247) (@lem2971246)). Qed.
Lemma lem2971249 : term573 = term568.
Proof. exact (MK_COMB (@lem2971248) (@lem2971243)). Qed.
Lemma lem2971251 (m : nat) (n : nat) : (term575 m n) = (term576 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2971252 : term568 = term577.
Proof. exact (@lem2971251 (NUMERAL 0) term86). Qed.
Lemma lem2971253 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971254 (h1 : term307 = (BIT1 0)) : (term86 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2971255 : (term307 = (BIT1 0)) = ((term86 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971254 h1) (fun h1 : (term86 = (NUMERAL 0)) = False => @lem2971253)). Qed.
Lemma lem2971256 : (term86 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2971255) (@lem2971253)). Qed.
Lemma lem2971257 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2971258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2971259 : term578 = (and True).
Proof. exact (MK_COMB (@lem2971258) (@lem2971257)). Qed.
Lemma lem2971260 : term577 = (True /\ False).
Proof. exact (MK_COMB (@lem2971259) (@lem2971256)). Qed.
Lemma lem2971262 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2971263 : term577 = False.
Proof. exact (TRANS (@lem2971260) (@lem2971262)). Qed.
Lemma lem2971264 : term568 = False.
Proof. exact (TRANS (@lem2971252) (@lem2971263)). Qed.
Lemma lem2971265 : term573 = False.
Proof. exact (TRANS (@lem2971249) (@lem2971264)). Qed.
Lemma lem2971266 : term570 = False.
Proof. exact (TRANS (@lem2971233) (@lem2971265)). Qed.
Lemma lem2971267 : term568 = False.
Proof. exact (TRANS (@lem2971210) (@lem2971266)). Qed.
Lemma lem2971268 : term567 = False.
Proof. exact (TRANS (@lem2971201) (@lem2971267)). Qed.
Lemma lem2971269 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term475 _31796 _31794 _31795) : False.
Proof. exact (EQ_MP (@lem2971268) (@lem2971198 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971270 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term579 _31796 _31794 _31795.
Proof. exact (h1). Qed.
Lemma lem2971271 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term471 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2971270 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971273 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term458 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2971271 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971275 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term445 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2971273 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971277 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term432 _31794 _31795.
Proof. exact (proj2 (@lem2971275 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971278 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term331 _31794 _31795 _31796.
Proof. exact (proj1 (@lem2971275 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971280 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : (term280 _31794 _31795 _31796) = term140.
Proof. exact (proj1 (@lem2971278 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971281 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term380 _31794 _31795.
Proof. exact (proj2 (@lem2971277 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971282 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term349 _31794 _31795.
Proof. exact (proj1 (@lem2971277 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971284 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2971285 : term476 = term305.
Proof. exact (@lem2971284 term140 term169). Qed.
Lemma lem2971287 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971288 : term169 = term288.
Proof. exact (@lem2971287 term86). Qed.
Lemma lem2971290 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971291 : term140 = term229.
Proof. exact (@lem2971290 (NUMERAL 0)). Qed.
Lemma lem2971292 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2971293 : term477 = term478.
Proof. exact (MK_COMB (@lem2971292) (@lem2971291)). Qed.
Lemma lem2971294 : term305 = term479.
Proof. exact (MK_COMB (@lem2971293) (@lem2971288)). Qed.
Lemma lem2971295 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2971297 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971298 : term305 = term306.
Proof. exact (@lem2971297 (NUMERAL 0) term86). Qed.
Lemma lem2971299 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971300 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971301 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971300 h1) (fun h1 : term306 = True => @lem2971299)). Qed.
Lemma lem2971302 : term306 = True.
Proof. exact (EQ_MP (@lem2971301) (@lem2971299)). Qed.
Lemma lem2971303 : term305 = True.
Proof. exact (TRANS (@lem2971298) (@lem2971302)). Qed.
Lemma lem2971304 : True = term305.
Proof. exact (SYM (@lem2971303)). Qed.
Lemma lem2971305 : term305.
Proof. exact (EQ_MP (@lem2971304) (@lem0)). Qed.
Lemma lem2971306 : term481.
Proof. exact (@lem2971295 (@lem2971305)). Qed.
Lemma lem2971308 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971309 : term305 = term306.
Proof. exact (@lem2971308 (NUMERAL 0) term86). Qed.
Lemma lem2971310 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971311 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971312 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971311 h1) (fun h1 : term306 = True => @lem2971310)). Qed.
Lemma lem2971313 : term306 = True.
Proof. exact (EQ_MP (@lem2971312) (@lem2971310)). Qed.
Lemma lem2971314 : term305 = True.
Proof. exact (TRANS (@lem2971309) (@lem2971313)). Qed.
Lemma lem2971315 : True = term305.
Proof. exact (SYM (@lem2971314)). Qed.
Lemma lem2971316 : term305.
Proof. exact (EQ_MP (@lem2971315) (@lem0)). Qed.
Lemma lem2971317 : term479 = term482.
Proof. exact (@lem2971306 (@lem2971316)). Qed.
Lemma lem2971319 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971320 : term241 = term242.
Proof. exact (@lem2971319 term86 term86). Qed.
Lemma lem2971321 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971322 : term244 = term86.
Proof. exact (EQ_MP (@lem2971321) (@lem940073)). Qed.
Lemma lem2971323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971324 : term242 = term169.
Proof. exact (MK_COMB (@lem2971323) (@lem2971322)). Qed.
Lemma lem2971325 : term241 = term169.
Proof. exact (TRANS (@lem2971320) (@lem2971324)). Qed.
Lemma lem2971327 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971328 : term373 = term140.
Proof. exact (@lem2971327 term86). Qed.
Lemma lem2971329 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2971330 : term483 = term477.
Proof. exact (MK_COMB (@lem2971329) (@lem2971328)). Qed.
Lemma lem2971331 : term482 = term305.
Proof. exact (MK_COMB (@lem2971330) (@lem2971325)). Qed.
Lemma lem2971333 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971334 : term305 = term306.
Proof. exact (@lem2971333 (NUMERAL 0) term86). Qed.
Lemma lem2971335 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971336 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971337 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971336 h1) (fun h1 : term306 = True => @lem2971335)). Qed.
Lemma lem2971338 : term306 = True.
Proof. exact (EQ_MP (@lem2971337) (@lem2971335)). Qed.
Lemma lem2971339 : term305 = True.
Proof. exact (TRANS (@lem2971334) (@lem2971338)). Qed.
Lemma lem2971340 : term482 = True.
Proof. exact (TRANS (@lem2971331) (@lem2971339)). Qed.
Lemma lem2971341 : term479 = True.
Proof. exact (TRANS (@lem2971317) (@lem2971340)). Qed.
Lemma lem2971342 : term305 = True.
Proof. exact (TRANS (@lem2971294) (@lem2971341)). Qed.
Lemma lem2971343 : term476 = True.
Proof. exact (TRANS (@lem2971285) (@lem2971342)). Qed.
Lemma lem2971344 : True = term476.
Proof. exact (SYM (@lem2971343)). Qed.
Lemma lem2971345 : term476.
Proof. exact (EQ_MP (@lem2971344) (@lem0)). Qed.
Lemma lem2971346 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term580 _31794 _31795.
Proof. exact (conj (@lem2971345) (@lem2971282 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971348 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2971349 (_31794 : int) (_31795 : int) : term581 _31794 _31795.
Proof. exact (@lem2971348 term169 (term346 _31794 _31795)). Qed.
Lemma lem2971350 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term582 _31794 _31795.
Proof. exact (@lem2971349 _31794 _31795 (@lem2971346 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971351 (_31794 : int) (_31795 : int) : (term583 _31794 _31795) = (term346 _31794 _31795).
Proof. exact (@lem1982733 (term346 _31794 _31795)). Qed.
Lemma lem2971352 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2971353 (_31794 : int) (_31795 : int) : (term584 _31794 _31795) = (term348 _31794 _31795).
Proof. exact (MK_COMB (@lem2971352) (@lem2971351 _31794 _31795)). Qed.
Lemma lem2971354 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2971355 (_31794 : int) (_31795 : int) : (term582 _31794 _31795) = (term349 _31794 _31795).
Proof. exact (MK_COMB (@lem2971353 _31794 _31795) (@lem2971354)). Qed.
Lemma lem2971356 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term349 _31794 _31795.
Proof. exact (EQ_MP (@lem2971355 _31794 _31795) (@lem2971350 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971358 (y : real) : term495 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2971359 (_31794 : int) (_31795 : int) (_31796 : int) : term496 _31794 _31795 _31796.
Proof. exact (@lem2971358 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2971360 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term497 _31794 _31795 _31796.
Proof. exact (@lem2971359 _31794 _31795 _31796 (@lem2971280 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971361 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term585 _31794 _31795 _31796.
Proof. exact (@lem2971360 _31796 _31794 _31795 h1 term232). Qed.
Lemma lem2971362 (_31794 : int) (_31795 : int) (_31796 : int) : (term585 _31794 _31795 _31796) = ((term586 _31794 _31795 _31796) = term140).
Proof. exact (eq_refl (term585 _31794 _31795 _31796)). Qed.
Lemma lem2971363 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : (term586 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2971362 _31794 _31795 _31796) (@lem2971361 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971364 (_31794 : int) (_31795 : int) (_31796 : int) : (term586 _31794 _31795 _31796) = (term587 _31794 _31795 _31796).
Proof. exact (@lem1982781 (real_of_int _31794) term232 (term279 _31795 _31796)). Qed.
Lemma lem2971365 (_31795 : int) (_31796 : int) : (term588 _31795 _31796) = (term589 _31795 _31796).
Proof. exact (@lem1982781 (term276 _31795) term232 (term257 _31796)). Qed.
Lemma lem2971366 (_31796 : int) : (term590 _31796) = (term591 _31796).
Proof. exact (@lem1982749 term232 term232 (real_of_int _31796)). Qed.
Lemma lem2971368 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971369 : term232 = term233.
Proof. exact (@lem2971368 term86). Qed.
Lemma lem2971371 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971372 : term232 = term233.
Proof. exact (@lem2971371 term86). Qed.
Lemma lem2971373 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971374 : term234 = term235.
Proof. exact (MK_COMB (@lem2971373) (@lem2971372)). Qed.
Lemma lem2971375 : term592 = term593.
Proof. exact (MK_COMB (@lem2971374) (@lem2971369)). Qed.
Lemma lem2971376 : term593 = term594.
Proof. exact (@lem1981613 term232 term232 term169 term169). Qed.
Lemma lem2971378 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971379 : term241 = term242.
Proof. exact (@lem2971378 term86 term86). Qed.
Lemma lem2971380 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971381 : term244 = term86.
Proof. exact (EQ_MP (@lem2971380) (@lem940073)). Qed.
Lemma lem2971382 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971383 : term242 = term169.
Proof. exact (MK_COMB (@lem2971382) (@lem2971381)). Qed.
Lemma lem2971384 : term241 = term169.
Proof. exact (TRANS (@lem2971379) (@lem2971383)). Qed.
Lemma lem2971386 (m : nat) (n : nat) : (term595 m n) = (term240 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2971387 : term592 = term242.
Proof. exact (@lem2971386 term86 term86). Qed.
Lemma lem2971388 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971389 : term244 = term86.
Proof. exact (EQ_MP (@lem2971388) (@lem940073)). Qed.
Lemma lem2971390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971391 : term242 = term169.
Proof. exact (MK_COMB (@lem2971390) (@lem2971389)). Qed.
Lemma lem2971392 : term592 = term169.
Proof. exact (TRANS (@lem2971387) (@lem2971391)). Qed.
Lemma lem2971393 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2971394 : term596 = term597.
Proof. exact (MK_COMB (@lem2971393) (@lem2971392)). Qed.
Lemma lem2971395 : term594 = term288.
Proof. exact (MK_COMB (@lem2971394) (@lem2971384)). Qed.
Lemma lem2971396 : term593 = term288.
Proof. exact (TRANS (@lem2971376) (@lem2971395)). Qed.
Lemma lem2971397 : term592 = term288.
Proof. exact (TRANS (@lem2971375) (@lem2971396)). Qed.
Lemma lem2971399 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2971400 : term288 = term169.
Proof. exact (@lem2971399 term169). Qed.
Lemma lem2971401 : term592 = term169.
Proof. exact (TRANS (@lem2971397) (@lem2971400)). Qed.
Lemma lem2971402 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971403 : term598 = term323.
Proof. exact (MK_COMB (@lem2971402) (@lem2971401)). Qed.
Lemma lem2971404 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2971405 (_31796 : int) : (term591 _31796) = (term488 _31796).
Proof. exact (MK_COMB (@lem2971403) (@lem2971404 _31796)). Qed.
Lemma lem2971406 (_31796 : int) : (term590 _31796) = (term488 _31796).
Proof. exact (TRANS (@lem2971366 _31796) (@lem2971405 _31796)). Qed.
Lemma lem2971407 (_31796 : int) : (term488 _31796) = (real_of_int _31796).
Proof. exact (@lem1982709 (real_of_int _31796)). Qed.
Lemma lem2971408 (_31796 : int) : (term590 _31796) = (real_of_int _31796).
Proof. exact (TRANS (@lem2971406 _31796) (@lem2971407 _31796)). Qed.
Lemma lem2971409 (_31795 : int) : (term599 _31795) = (term600 _31795).
Proof. exact (@lem1982749 term232 term270 (real_of_int _31795)). Qed.
Lemma lem2971411 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971412 : term270 = term273.
Proof. exact (@lem2971411 term2). Qed.
Lemma lem2971414 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971415 : term232 = term233.
Proof. exact (@lem2971414 term86). Qed.
Lemma lem2971416 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971417 : term234 = term235.
Proof. exact (MK_COMB (@lem2971416) (@lem2971415)). Qed.
Lemma lem2971418 : term601 = term602.
Proof. exact (MK_COMB (@lem2971417) (@lem2971412)). Qed.
Lemma lem2971419 : term602 = term603.
Proof. exact (@lem1981613 term232 term270 term169 term169). Qed.
Lemma lem2971421 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971422 : term241 = term242.
Proof. exact (@lem2971421 term86 term86). Qed.
Lemma lem2971423 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971424 : term244 = term86.
Proof. exact (EQ_MP (@lem2971423) (@lem940073)). Qed.
Lemma lem2971425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971426 : term242 = term169.
Proof. exact (MK_COMB (@lem2971425) (@lem2971424)). Qed.
Lemma lem2971427 : term241 = term169.
Proof. exact (TRANS (@lem2971422) (@lem2971426)). Qed.
Lemma lem2971429 (m : nat) (n : nat) : (term595 m n) = (term240 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2971430 : term601 = term269.
Proof. exact (@lem2971429 term86 term2). Qed.
Lemma lem2971431 : term267 = term27.
Proof. exact (@lem996238 term27). Qed.
Lemma lem2971432 : (term267 = term27) = (term268 = term2).
Proof. exact (@lem1007663 (BIT1 0) term27 term27). Qed.
Lemma lem2971433 : term268 = term2.
Proof. exact (EQ_MP (@lem2971432) (@lem2971431)). Qed.
Lemma lem2971434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971435 : term269 = term154.
Proof. exact (MK_COMB (@lem2971434) (@lem2971433)). Qed.
Lemma lem2971436 : term601 = term154.
Proof. exact (TRANS (@lem2971430) (@lem2971435)). Qed.
Lemma lem2971437 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2971438 : term604 = term605.
Proof. exact (MK_COMB (@lem2971437) (@lem2971436)). Qed.
Lemma lem2971439 : term603 = term260.
Proof. exact (MK_COMB (@lem2971438) (@lem2971427)). Qed.
Lemma lem2971440 : term602 = term260.
Proof. exact (TRANS (@lem2971419) (@lem2971439)). Qed.
Lemma lem2971441 : term601 = term260.
Proof. exact (TRANS (@lem2971418) (@lem2971440)). Qed.
Lemma lem2971443 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2971444 : term260 = term154.
Proof. exact (@lem2971443 term154). Qed.
Lemma lem2971445 : term601 = term154.
Proof. exact (TRANS (@lem2971441) (@lem2971444)). Qed.
Lemma lem2971446 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971447 : term606 = term156.
Proof. exact (MK_COMB (@lem2971446) (@lem2971445)). Qed.
Lemma lem2971448 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2971449 (_31795 : int) : (term600 _31795) = (term157 _31795).
Proof. exact (MK_COMB (@lem2971447) (@lem2971448 _31795)). Qed.
Lemma lem2971450 (_31795 : int) : (term599 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2971409 _31795) (@lem2971449 _31795)). Qed.
Lemma lem2971451 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971452 (_31795 : int) : (term607 _31795) = (term159 _31795).
Proof. exact (MK_COMB (@lem2971451) (@lem2971450 _31795)). Qed.
Lemma lem2971453 (_31795 : int) (_31796 : int) : (term589 _31795 _31796) = (term160 _31795 _31796).
Proof. exact (MK_COMB (@lem2971452 _31795) (@lem2971408 _31796)). Qed.
Lemma lem2971454 (_31795 : int) (_31796 : int) : (term588 _31795 _31796) = (term160 _31795 _31796).
Proof. exact (TRANS (@lem2971365 _31795 _31796) (@lem2971453 _31795 _31796)). Qed.
Lemma lem2971457 (_31794 : int) : (term295 _31794) = (term295 _31794).
Proof. exact (eq_refl (term295 _31794)). Qed.
Lemma lem2971458 (_31794 : int) (_31795 : int) (_31796 : int) : (term587 _31794 _31795 _31796) = (term608 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2971457 _31794) (@lem2971454 _31795 _31796)). Qed.
Lemma lem2971459 (_31794 : int) (_31795 : int) (_31796 : int) : (term586 _31794 _31795 _31796) = (term608 _31794 _31795 _31796).
Proof. exact (TRANS (@lem2971364 _31794 _31795 _31796) (@lem2971458 _31794 _31795 _31796)). Qed.
Lemma lem2971460 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2971461 (_31794 : int) (_31795 : int) (_31796 : int) : (term609 _31794 _31795 _31796) = (term610 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2971460) (@lem2971459 _31794 _31795 _31796)). Qed.
Lemma lem2971462 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2971463 (_31794 : int) (_31795 : int) (_31796 : int) : ((term586 _31794 _31795 _31796) = term140) = ((term608 _31794 _31795 _31796) = term140).
Proof. exact (MK_COMB (@lem2971461 _31794 _31795 _31796) (@lem2971462)). Qed.
Lemma lem2971464 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : (term608 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2971463 _31794 _31795 _31796) (@lem2971363 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971465 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term611 _31796 _31794 _31795.
Proof. exact (conj (@lem2971464 _31796 _31794 _31795 h1) (@lem2971356 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971467 (x : real) (y : real) : term502 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2971468 (_31796 : int) (_31794 : int) (_31795 : int) : term612 _31796 _31794 _31795.
Proof. exact (@lem2971467 (term608 _31794 _31795 _31796) (term346 _31794 _31795)). Qed.
Lemma lem2971469 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term613 _31796 _31794 _31795.
Proof. exact (@lem2971468 _31796 _31794 _31795 (@lem2971465 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971470 (_31794 : int) (_31796 : int) (_31795 : int) : (term614 _31796 _31794 _31795) = (term615 _31794 _31796 _31795).
Proof. exact (@lem1982753 (term257 _31794) (real_of_int _31794) (term160 _31795 _31796) (term345 _31795)). Qed.
Lemma lem2971471 (_31794 : int) : (term562 _31794) = (term509 _31794).
Proof. exact (@lem1982713 term232 (real_of_int _31794)). Qed.
Lemma lem2971473 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971474 : term169 = term288.
Proof. exact (@lem2971473 term86). Qed.
Lemma lem2971476 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971477 : term232 = term233.
Proof. exact (@lem2971476 term86). Qed.
Lemma lem2971478 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971479 : term510 = term511.
Proof. exact (MK_COMB (@lem2971478) (@lem2971477)). Qed.
Lemma lem2971480 : term512 = term513.
Proof. exact (MK_COMB (@lem2971479) (@lem2971474)). Qed.
Lemma lem2971481 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2971483 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971484 : term305 = term306.
Proof. exact (@lem2971483 (NUMERAL 0) term86). Qed.
Lemma lem2971485 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971486 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971487 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971486 h1) (fun h1 : term306 = True => @lem2971485)). Qed.
Lemma lem2971488 : term306 = True.
Proof. exact (EQ_MP (@lem2971487) (@lem2971485)). Qed.
Lemma lem2971489 : term305 = True.
Proof. exact (TRANS (@lem2971484) (@lem2971488)). Qed.
Lemma lem2971490 : True = term305.
Proof. exact (SYM (@lem2971489)). Qed.
Lemma lem2971491 : term305.
Proof. exact (EQ_MP (@lem2971490) (@lem0)). Qed.
Lemma lem2971492 : term515.
Proof. exact (@lem2971481 (@lem2971491)). Qed.
Lemma lem2971494 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971495 : term305 = term306.
Proof. exact (@lem2971494 (NUMERAL 0) term86). Qed.
Lemma lem2971496 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971497 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971498 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971497 h1) (fun h1 : term306 = True => @lem2971496)). Qed.
Lemma lem2971499 : term306 = True.
Proof. exact (EQ_MP (@lem2971498) (@lem2971496)). Qed.
Lemma lem2971500 : term305 = True.
Proof. exact (TRANS (@lem2971495) (@lem2971499)). Qed.
Lemma lem2971501 : True = term305.
Proof. exact (SYM (@lem2971500)). Qed.
Lemma lem2971502 : term305.
Proof. exact (EQ_MP (@lem2971501) (@lem0)). Qed.
Lemma lem2971503 : term516.
Proof. exact (@lem2971492 (@lem2971502)). Qed.
Lemma lem2971505 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971506 : term305 = term306.
Proof. exact (@lem2971505 (NUMERAL 0) term86). Qed.
Lemma lem2971507 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971508 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971509 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971508 h1) (fun h1 : term306 = True => @lem2971507)). Qed.
Lemma lem2971510 : term306 = True.
Proof. exact (EQ_MP (@lem2971509) (@lem2971507)). Qed.
Lemma lem2971511 : term305 = True.
Proof. exact (TRANS (@lem2971506) (@lem2971510)). Qed.
Lemma lem2971512 : True = term305.
Proof. exact (SYM (@lem2971511)). Qed.
Lemma lem2971513 : term305.
Proof. exact (EQ_MP (@lem2971512) (@lem0)). Qed.
Lemma lem2971514 : term517.
Proof. exact (@lem2971503 (@lem2971513)). Qed.
Lemma lem2971516 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971517 : term241 = term242.
Proof. exact (@lem2971516 term86 term86). Qed.
Lemma lem2971518 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971519 : term244 = term86.
Proof. exact (EQ_MP (@lem2971518) (@lem940073)). Qed.
Lemma lem2971520 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971521 : term242 = term169.
Proof. exact (MK_COMB (@lem2971520) (@lem2971519)). Qed.
Lemma lem2971522 : term241 = term169.
Proof. exact (TRANS (@lem2971517) (@lem2971521)). Qed.
Lemma lem2971524 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2971525 : term289 = term292.
Proof. exact (@lem2971524 term86 term86). Qed.
Lemma lem2971526 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971527 : term244 = term86.
Proof. exact (EQ_MP (@lem2971526) (@lem940073)). Qed.
Lemma lem2971528 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971529 : term242 = term169.
Proof. exact (MK_COMB (@lem2971528) (@lem2971527)). Qed.
Lemma lem2971530 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2971531 : term292 = term232.
Proof. exact (MK_COMB (@lem2971530) (@lem2971529)). Qed.
Lemma lem2971532 : term289 = term232.
Proof. exact (TRANS (@lem2971525) (@lem2971531)). Qed.
Lemma lem2971533 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971534 : term518 = term510.
Proof. exact (MK_COMB (@lem2971533) (@lem2971532)). Qed.
Lemma lem2971535 : term519 = term512.
Proof. exact (MK_COMB (@lem2971534) (@lem2971522)). Qed.
Lemma lem2971537 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2971538 : term512 = term140.
Proof. exact (@lem2971537 term86). Qed.
Lemma lem2971539 : term519 = term140.
Proof. exact (TRANS (@lem2971535) (@lem2971538)). Qed.
Lemma lem2971540 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971541 : term521 = term371.
Proof. exact (MK_COMB (@lem2971540) (@lem2971539)). Qed.
Lemma lem2971542 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2971543 : term522 = term373.
Proof. exact (MK_COMB (@lem2971541) (@lem2971542)). Qed.
Lemma lem2971545 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971546 : term373 = term140.
Proof. exact (@lem2971545 term86). Qed.
Lemma lem2971547 : term522 = term140.
Proof. exact (TRANS (@lem2971543) (@lem2971546)). Qed.
Lemma lem2971549 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971550 : term241 = term242.
Proof. exact (@lem2971549 term86 term86). Qed.
Lemma lem2971551 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971552 : term244 = term86.
Proof. exact (EQ_MP (@lem2971551) (@lem940073)). Qed.
Lemma lem2971553 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971554 : term242 = term169.
Proof. exact (MK_COMB (@lem2971553) (@lem2971552)). Qed.
Lemma lem2971555 : term241 = term169.
Proof. exact (TRANS (@lem2971550) (@lem2971554)). Qed.
Lemma lem2971556 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2971557 : term375 = term373.
Proof. exact (MK_COMB (@lem2971556) (@lem2971555)). Qed.
Lemma lem2971559 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971560 : term373 = term140.
Proof. exact (@lem2971559 term86). Qed.
Lemma lem2971561 : term375 = term140.
Proof. exact (TRANS (@lem2971557) (@lem2971560)). Qed.
Lemma lem2971562 : term140 = term375.
Proof. exact (SYM (@lem2971561)). Qed.
Lemma lem2971563 : term522 = term375.
Proof. exact (TRANS (@lem2971547) (@lem2971562)). Qed.
Lemma lem2971564 : term513 = term229.
Proof. exact (@lem2971514 (@lem2971563)). Qed.
Lemma lem2971565 : term512 = term229.
Proof. exact (TRANS (@lem2971480) (@lem2971564)). Qed.
Lemma lem2971567 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2971568 : term229 = term140.
Proof. exact (@lem2971567 term140). Qed.
Lemma lem2971569 : term512 = term140.
Proof. exact (TRANS (@lem2971565) (@lem2971568)). Qed.
Lemma lem2971570 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971571 : term523 = term371.
Proof. exact (MK_COMB (@lem2971570) (@lem2971569)). Qed.
Lemma lem2971572 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2971573 (_31794 : int) : (term509 _31794) = (term524 _31794).
Proof. exact (MK_COMB (@lem2971571) (@lem2971572 _31794)). Qed.
Lemma lem2971574 (_31794 : int) : (term562 _31794) = (term524 _31794).
Proof. exact (TRANS (@lem2971471 _31794) (@lem2971573 _31794)). Qed.
Lemma lem2971575 (_31794 : int) : (term524 _31794) = term140.
Proof. exact (@lem1982719 (real_of_int _31794)). Qed.
Lemma lem2971576 (_31794 : int) : (term562 _31794) = term140.
Proof. exact (TRANS (@lem2971574 _31794) (@lem2971575 _31794)). Qed.
Lemma lem2971577 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971578 (_31794 : int) : (term563 _31794) = term526.
Proof. exact (MK_COMB (@lem2971577) (@lem2971576 _31794)). Qed.
Lemma lem2971579 (_31795 : int) (_31796 : int) : (term616 _31796 _31795) = (term617 _31795 _31796).
Proof. exact (@lem1982753 (term157 _31795) (term276 _31795) (real_of_int _31796) term232). Qed.
Lemma lem2971580 (_31795 : int) : (term618 _31795) = (term619 _31795).
Proof. exact (@lem1982711 term154 term270 (real_of_int _31795)). Qed.
Lemma lem2971582 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971583 : term270 = term273.
Proof. exact (@lem2971582 term2). Qed.
Lemma lem2971585 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971586 : term154 = term260.
Proof. exact (@lem2971585 term2). Qed.
Lemma lem2971587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971588 : term297 = term300.
Proof. exact (MK_COMB (@lem2971587) (@lem2971586)). Qed.
Lemma lem2971589 : term620 = term621.
Proof. exact (MK_COMB (@lem2971588) (@lem2971583)). Qed.
Lemma lem2971590 : term622.
Proof. exact (@lem1981473 term154 term169 term270 term169 term140 term169). Qed.
Lemma lem2971592 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971593 : term305 = term306.
Proof. exact (@lem2971592 (NUMERAL 0) term86). Qed.
Lemma lem2971594 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971595 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971596 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971595 h1) (fun h1 : term306 = True => @lem2971594)). Qed.
Lemma lem2971597 : term306 = True.
Proof. exact (EQ_MP (@lem2971596) (@lem2971594)). Qed.
Lemma lem2971598 : term305 = True.
Proof. exact (TRANS (@lem2971593) (@lem2971597)). Qed.
Lemma lem2971599 : True = term305.
Proof. exact (SYM (@lem2971598)). Qed.
Lemma lem2971600 : term305.
Proof. exact (EQ_MP (@lem2971599) (@lem0)). Qed.
Lemma lem2971601 : term623.
Proof. exact (@lem2971590 (@lem2971600)). Qed.
Lemma lem2971603 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971604 : term305 = term306.
Proof. exact (@lem2971603 (NUMERAL 0) term86). Qed.
Lemma lem2971605 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971606 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971607 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971606 h1) (fun h1 : term306 = True => @lem2971605)). Qed.
Lemma lem2971608 : term306 = True.
Proof. exact (EQ_MP (@lem2971607) (@lem2971605)). Qed.
Lemma lem2971609 : term305 = True.
Proof. exact (TRANS (@lem2971604) (@lem2971608)). Qed.
Lemma lem2971610 : True = term305.
Proof. exact (SYM (@lem2971609)). Qed.
Lemma lem2971611 : term305.
Proof. exact (EQ_MP (@lem2971610) (@lem0)). Qed.
Lemma lem2971612 : term624.
Proof. exact (@lem2971601 (@lem2971611)). Qed.
Lemma lem2971614 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971615 : term305 = term306.
Proof. exact (@lem2971614 (NUMERAL 0) term86). Qed.
Lemma lem2971616 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971617 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971618 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971617 h1) (fun h1 : term306 = True => @lem2971616)). Qed.
Lemma lem2971619 : term306 = True.
Proof. exact (EQ_MP (@lem2971618) (@lem2971616)). Qed.
Lemma lem2971620 : term305 = True.
Proof. exact (TRANS (@lem2971615) (@lem2971619)). Qed.
Lemma lem2971621 : True = term305.
Proof. exact (SYM (@lem2971620)). Qed.
Lemma lem2971622 : term305.
Proof. exact (EQ_MP (@lem2971621) (@lem0)). Qed.
Lemma lem2971623 : term625.
Proof. exact (@lem2971612 (@lem2971622)). Qed.
Lemma lem2971625 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2971626 : term539 = term540.
Proof. exact (@lem2971625 term2 term86). Qed.
Lemma lem2971627 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2971628 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2971629 : term314 = term2.
Proof. exact (EQ_MP (@lem2971628) (@lem2971627)). Qed.
Lemma lem2971630 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971631 : term312 = term154.
Proof. exact (MK_COMB (@lem2971630) (@lem2971629)). Qed.
Lemma lem2971632 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2971633 : term540 = term270.
Proof. exact (MK_COMB (@lem2971632) (@lem2971631)). Qed.
Lemma lem2971634 : term539 = term270.
Proof. exact (TRANS (@lem2971626) (@lem2971633)). Qed.
Lemma lem2971636 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971637 : term311 = term312.
Proof. exact (@lem2971636 term2 term86). Qed.
Lemma lem2971638 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2971639 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2971640 : term314 = term2.
Proof. exact (EQ_MP (@lem2971639) (@lem2971638)). Qed.
Lemma lem2971641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971642 : term312 = term154.
Proof. exact (MK_COMB (@lem2971641) (@lem2971640)). Qed.
Lemma lem2971643 : term311 = term154.
Proof. exact (TRANS (@lem2971637) (@lem2971642)). Qed.
Lemma lem2971644 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971645 : term315 = term297.
Proof. exact (MK_COMB (@lem2971644) (@lem2971643)). Qed.
Lemma lem2971646 : term626 = term620.
Proof. exact (MK_COMB (@lem2971645) (@lem2971634)). Qed.
Lemma lem2971648 (m : nat) : (term369 m) = term140.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2971649 : term620 = term140.
Proof. exact (@lem2971648 term2). Qed.
Lemma lem2971650 : term626 = term140.
Proof. exact (TRANS (@lem2971646) (@lem2971649)). Qed.
Lemma lem2971651 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971652 : term627 = term371.
Proof. exact (MK_COMB (@lem2971651) (@lem2971650)). Qed.
Lemma lem2971653 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2971654 : term628 = term373.
Proof. exact (MK_COMB (@lem2971652) (@lem2971653)). Qed.
Lemma lem2971656 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971657 : term373 = term140.
Proof. exact (@lem2971656 term86). Qed.
Lemma lem2971658 : term628 = term140.
Proof. exact (TRANS (@lem2971654) (@lem2971657)). Qed.
Lemma lem2971660 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971661 : term241 = term242.
Proof. exact (@lem2971660 term86 term86). Qed.
Lemma lem2971662 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971663 : term244 = term86.
Proof. exact (EQ_MP (@lem2971662) (@lem940073)). Qed.
Lemma lem2971664 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971665 : term242 = term169.
Proof. exact (MK_COMB (@lem2971664) (@lem2971663)). Qed.
Lemma lem2971666 : term241 = term169.
Proof. exact (TRANS (@lem2971661) (@lem2971665)). Qed.
Lemma lem2971667 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2971668 : term375 = term373.
Proof. exact (MK_COMB (@lem2971667) (@lem2971666)). Qed.
Lemma lem2971670 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971671 : term373 = term140.
Proof. exact (@lem2971670 term86). Qed.
Lemma lem2971672 : term375 = term140.
Proof. exact (TRANS (@lem2971668) (@lem2971671)). Qed.
Lemma lem2971673 : term140 = term375.
Proof. exact (SYM (@lem2971672)). Qed.
Lemma lem2971674 : term628 = term375.
Proof. exact (TRANS (@lem2971658) (@lem2971673)). Qed.
Lemma lem2971675 : term621 = term229.
Proof. exact (@lem2971623 (@lem2971674)). Qed.
Lemma lem2971676 : term620 = term229.
Proof. exact (TRANS (@lem2971589) (@lem2971675)). Qed.
Lemma lem2971678 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2971679 : term229 = term140.
Proof. exact (@lem2971678 term140). Qed.
Lemma lem2971680 : term620 = term140.
Proof. exact (TRANS (@lem2971676) (@lem2971679)). Qed.
Lemma lem2971681 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971682 : term629 = term371.
Proof. exact (MK_COMB (@lem2971681) (@lem2971680)). Qed.
Lemma lem2971683 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2971684 (_31795 : int) : (term619 _31795) = (term524 _31795).
Proof. exact (MK_COMB (@lem2971682) (@lem2971683 _31795)). Qed.
Lemma lem2971685 (_31795 : int) : (term618 _31795) = (term524 _31795).
Proof. exact (TRANS (@lem2971580 _31795) (@lem2971684 _31795)). Qed.
Lemma lem2971686 (_31795 : int) : (term524 _31795) = term140.
Proof. exact (@lem1982719 (real_of_int _31795)). Qed.
Lemma lem2971687 (_31795 : int) : (term618 _31795) = term140.
Proof. exact (TRANS (@lem2971685 _31795) (@lem2971686 _31795)). Qed.
Lemma lem2971688 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971689 (_31795 : int) : (term630 _31795) = term526.
Proof. exact (MK_COMB (@lem2971688) (@lem2971687 _31795)). Qed.
Lemma lem2971690 (_31796 : int) : (term631 _31796) = (term631 _31796).
Proof. exact (eq_refl (term631 _31796)). Qed.
Lemma lem2971691 (_31795 : int) (_31796 : int) : (term617 _31795 _31796) = (term632 _31796).
Proof. exact (MK_COMB (@lem2971689 _31795) (@lem2971690 _31796)). Qed.
Lemma lem2971692 (_31795 : int) (_31796 : int) : (term616 _31796 _31795) = (term632 _31796).
Proof. exact (TRANS (@lem2971579 _31795 _31796) (@lem2971691 _31795 _31796)). Qed.
Lemma lem2971693 (_31796 : int) : (term632 _31796) = (term631 _31796).
Proof. exact (@lem1982721 (term631 _31796)). Qed.
Lemma lem2971694 (_31795 : int) (_31796 : int) : (term616 _31796 _31795) = (term631 _31796).
Proof. exact (TRANS (@lem2971692 _31795 _31796) (@lem2971693 _31796)). Qed.
Lemma lem2971695 (_31794 : int) (_31795 : int) (_31796 : int) : (term615 _31794 _31796 _31795) = (term632 _31796).
Proof. exact (MK_COMB (@lem2971578 _31794) (@lem2971694 _31795 _31796)). Qed.
Lemma lem2971696 (_31794 : int) (_31795 : int) (_31796 : int) : (term614 _31796 _31794 _31795) = (term632 _31796).
Proof. exact (TRANS (@lem2971470 _31794 _31796 _31795) (@lem2971695 _31794 _31795 _31796)). Qed.
Lemma lem2971697 (_31796 : int) : (term632 _31796) = (term631 _31796).
Proof. exact (@lem1982721 (term631 _31796)). Qed.
Lemma lem2971698 (_31794 : int) (_31795 : int) (_31796 : int) : (term614 _31796 _31794 _31795) = (term631 _31796).
Proof. exact (TRANS (@lem2971696 _31794 _31795 _31796) (@lem2971697 _31796)). Qed.
Lemma lem2971699 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2971700 (_31794 : int) (_31795 : int) (_31796 : int) : (term633 _31796 _31794 _31795) = (term634 _31796).
Proof. exact (MK_COMB (@lem2971699) (@lem2971698 _31794 _31795 _31796)). Qed.
Lemma lem2971701 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2971702 (_31794 : int) (_31795 : int) (_31796 : int) : (term613 _31796 _31794 _31795) = (term635 _31796).
Proof. exact (MK_COMB (@lem2971700 _31794 _31795 _31796) (@lem2971701)). Qed.
Lemma lem2971703 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term635 _31796.
Proof. exact (EQ_MP (@lem2971702 _31794 _31795 _31796) (@lem2971469 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971705 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2971706 : term476 = term305.
Proof. exact (@lem2971705 term140 term169). Qed.
Lemma lem2971708 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971709 : term169 = term288.
Proof. exact (@lem2971708 term86). Qed.
Lemma lem2971711 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971712 : term140 = term229.
Proof. exact (@lem2971711 (NUMERAL 0)). Qed.
Lemma lem2971713 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2971714 : term477 = term478.
Proof. exact (MK_COMB (@lem2971713) (@lem2971712)). Qed.
Lemma lem2971715 : term305 = term479.
Proof. exact (MK_COMB (@lem2971714) (@lem2971709)). Qed.
Lemma lem2971716 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2971718 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971719 : term305 = term306.
Proof. exact (@lem2971718 (NUMERAL 0) term86). Qed.
Lemma lem2971720 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971721 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971722 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971721 h1) (fun h1 : term306 = True => @lem2971720)). Qed.
Lemma lem2971723 : term306 = True.
Proof. exact (EQ_MP (@lem2971722) (@lem2971720)). Qed.
Lemma lem2971724 : term305 = True.
Proof. exact (TRANS (@lem2971719) (@lem2971723)). Qed.
Lemma lem2971725 : True = term305.
Proof. exact (SYM (@lem2971724)). Qed.
Lemma lem2971726 : term305.
Proof. exact (EQ_MP (@lem2971725) (@lem0)). Qed.
Lemma lem2971727 : term481.
Proof. exact (@lem2971716 (@lem2971726)). Qed.
Lemma lem2971729 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971730 : term305 = term306.
Proof. exact (@lem2971729 (NUMERAL 0) term86). Qed.
Lemma lem2971731 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971732 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971733 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971732 h1) (fun h1 : term306 = True => @lem2971731)). Qed.
Lemma lem2971734 : term306 = True.
Proof. exact (EQ_MP (@lem2971733) (@lem2971731)). Qed.
Lemma lem2971735 : term305 = True.
Proof. exact (TRANS (@lem2971730) (@lem2971734)). Qed.
Lemma lem2971736 : True = term305.
Proof. exact (SYM (@lem2971735)). Qed.
Lemma lem2971737 : term305.
Proof. exact (EQ_MP (@lem2971736) (@lem0)). Qed.
Lemma lem2971738 : term479 = term482.
Proof. exact (@lem2971727 (@lem2971737)). Qed.
Lemma lem2971740 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971741 : term241 = term242.
Proof. exact (@lem2971740 term86 term86). Qed.
Lemma lem2971742 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971743 : term244 = term86.
Proof. exact (EQ_MP (@lem2971742) (@lem940073)). Qed.
Lemma lem2971744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971745 : term242 = term169.
Proof. exact (MK_COMB (@lem2971744) (@lem2971743)). Qed.
Lemma lem2971746 : term241 = term169.
Proof. exact (TRANS (@lem2971741) (@lem2971745)). Qed.
Lemma lem2971748 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971749 : term373 = term140.
Proof. exact (@lem2971748 term86). Qed.
Lemma lem2971750 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2971751 : term483 = term477.
Proof. exact (MK_COMB (@lem2971750) (@lem2971749)). Qed.
Lemma lem2971752 : term482 = term305.
Proof. exact (MK_COMB (@lem2971751) (@lem2971746)). Qed.
Lemma lem2971754 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971755 : term305 = term306.
Proof. exact (@lem2971754 (NUMERAL 0) term86). Qed.
Lemma lem2971756 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971757 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971758 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971757 h1) (fun h1 : term306 = True => @lem2971756)). Qed.
Lemma lem2971759 : term306 = True.
Proof. exact (EQ_MP (@lem2971758) (@lem2971756)). Qed.
Lemma lem2971760 : term305 = True.
Proof. exact (TRANS (@lem2971755) (@lem2971759)). Qed.
Lemma lem2971761 : term482 = True.
Proof. exact (TRANS (@lem2971752) (@lem2971760)). Qed.
Lemma lem2971762 : term479 = True.
Proof. exact (TRANS (@lem2971738) (@lem2971761)). Qed.
Lemma lem2971763 : term305 = True.
Proof. exact (TRANS (@lem2971715) (@lem2971762)). Qed.
Lemma lem2971764 : term476 = True.
Proof. exact (TRANS (@lem2971706) (@lem2971763)). Qed.
Lemma lem2971765 : True = term476.
Proof. exact (SYM (@lem2971764)). Qed.
Lemma lem2971766 : term476.
Proof. exact (EQ_MP (@lem2971765) (@lem0)). Qed.
Lemma lem2971767 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term636 _31796.
Proof. exact (conj (@lem2971766) (@lem2971703 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971769 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2971770 (_31796 : int) : term637 _31796.
Proof. exact (@lem2971769 term169 (term631 _31796)). Qed.
Lemma lem2971771 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term638 _31796.
Proof. exact (@lem2971770 _31796 (@lem2971767 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971772 (_31796 : int) : (term639 _31796) = (term631 _31796).
Proof. exact (@lem1982733 (term631 _31796)). Qed.
Lemma lem2971773 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2971774 (_31796 : int) : (term640 _31796) = (term634 _31796).
Proof. exact (MK_COMB (@lem2971773) (@lem2971772 _31796)). Qed.
Lemma lem2971775 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2971776 (_31796 : int) : (term638 _31796) = (term635 _31796).
Proof. exact (MK_COMB (@lem2971774 _31796) (@lem2971775)). Qed.
Lemma lem2971777 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term635 _31796.
Proof. exact (EQ_MP (@lem2971776 _31796) (@lem2971771 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971779 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2971780 : term476 = term305.
Proof. exact (@lem2971779 term140 term169). Qed.
Lemma lem2971782 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971783 : term169 = term288.
Proof. exact (@lem2971782 term86). Qed.
Lemma lem2971785 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971786 : term140 = term229.
Proof. exact (@lem2971785 (NUMERAL 0)). Qed.
Lemma lem2971787 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2971788 : term477 = term478.
Proof. exact (MK_COMB (@lem2971787) (@lem2971786)). Qed.
Lemma lem2971789 : term305 = term479.
Proof. exact (MK_COMB (@lem2971788) (@lem2971783)). Qed.
Lemma lem2971790 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2971792 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971793 : term305 = term306.
Proof. exact (@lem2971792 (NUMERAL 0) term86). Qed.
Lemma lem2971794 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971795 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971796 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971795 h1) (fun h1 : term306 = True => @lem2971794)). Qed.
Lemma lem2971797 : term306 = True.
Proof. exact (EQ_MP (@lem2971796) (@lem2971794)). Qed.
Lemma lem2971798 : term305 = True.
Proof. exact (TRANS (@lem2971793) (@lem2971797)). Qed.
Lemma lem2971799 : True = term305.
Proof. exact (SYM (@lem2971798)). Qed.
Lemma lem2971800 : term305.
Proof. exact (EQ_MP (@lem2971799) (@lem0)). Qed.
Lemma lem2971801 : term481.
Proof. exact (@lem2971790 (@lem2971800)). Qed.
Lemma lem2971803 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971804 : term305 = term306.
Proof. exact (@lem2971803 (NUMERAL 0) term86). Qed.
Lemma lem2971805 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971806 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971807 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971806 h1) (fun h1 : term306 = True => @lem2971805)). Qed.
Lemma lem2971808 : term306 = True.
Proof. exact (EQ_MP (@lem2971807) (@lem2971805)). Qed.
Lemma lem2971809 : term305 = True.
Proof. exact (TRANS (@lem2971804) (@lem2971808)). Qed.
Lemma lem2971810 : True = term305.
Proof. exact (SYM (@lem2971809)). Qed.
Lemma lem2971811 : term305.
Proof. exact (EQ_MP (@lem2971810) (@lem0)). Qed.
Lemma lem2971812 : term479 = term482.
Proof. exact (@lem2971801 (@lem2971811)). Qed.
Lemma lem2971814 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971815 : term241 = term242.
Proof. exact (@lem2971814 term86 term86). Qed.
Lemma lem2971816 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971817 : term244 = term86.
Proof. exact (EQ_MP (@lem2971816) (@lem940073)). Qed.
Lemma lem2971818 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971819 : term242 = term169.
Proof. exact (MK_COMB (@lem2971818) (@lem2971817)). Qed.
Lemma lem2971820 : term241 = term169.
Proof. exact (TRANS (@lem2971815) (@lem2971819)). Qed.
Lemma lem2971822 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971823 : term373 = term140.
Proof. exact (@lem2971822 term86). Qed.
Lemma lem2971824 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2971825 : term483 = term477.
Proof. exact (MK_COMB (@lem2971824) (@lem2971823)). Qed.
Lemma lem2971826 : term482 = term305.
Proof. exact (MK_COMB (@lem2971825) (@lem2971820)). Qed.
Lemma lem2971828 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971829 : term305 = term306.
Proof. exact (@lem2971828 (NUMERAL 0) term86). Qed.
Lemma lem2971830 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971831 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971832 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971831 h1) (fun h1 : term306 = True => @lem2971830)). Qed.
Lemma lem2971833 : term306 = True.
Proof. exact (EQ_MP (@lem2971832) (@lem2971830)). Qed.
Lemma lem2971834 : term305 = True.
Proof. exact (TRANS (@lem2971829) (@lem2971833)). Qed.
Lemma lem2971835 : term482 = True.
Proof. exact (TRANS (@lem2971826) (@lem2971834)). Qed.
Lemma lem2971836 : term479 = True.
Proof. exact (TRANS (@lem2971812) (@lem2971835)). Qed.
Lemma lem2971837 : term305 = True.
Proof. exact (TRANS (@lem2971789) (@lem2971836)). Qed.
Lemma lem2971838 : term476 = True.
Proof. exact (TRANS (@lem2971780) (@lem2971837)). Qed.
Lemma lem2971839 : True = term476.
Proof. exact (SYM (@lem2971838)). Qed.
Lemma lem2971840 : term476.
Proof. exact (EQ_MP (@lem2971839) (@lem0)). Qed.
Lemma lem2971841 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term641 _31794 _31795.
Proof. exact (conj (@lem2971840) (@lem2971281 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971843 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2971844 (_31794 : int) (_31795 : int) : term642 _31794 _31795.
Proof. exact (@lem2971843 term169 (term377 _31794 _31795)). Qed.
Lemma lem2971845 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term643 _31794 _31795.
Proof. exact (@lem2971844 _31794 _31795 (@lem2971841 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971846 (_31794 : int) (_31795 : int) : (term644 _31794 _31795) = (term377 _31794 _31795).
Proof. exact (@lem1982733 (term377 _31794 _31795)). Qed.
Lemma lem2971847 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2971848 (_31794 : int) (_31795 : int) : (term645 _31794 _31795) = (term379 _31794 _31795).
Proof. exact (MK_COMB (@lem2971847) (@lem2971846 _31794 _31795)). Qed.
Lemma lem2971849 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2971850 (_31794 : int) (_31795 : int) : (term643 _31794 _31795) = (term380 _31794 _31795).
Proof. exact (MK_COMB (@lem2971848 _31794 _31795) (@lem2971849)). Qed.
Lemma lem2971851 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term380 _31794 _31795.
Proof. exact (EQ_MP (@lem2971850 _31794 _31795) (@lem2971845 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971853 (y : real) : term495 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2971854 (_31794 : int) (_31795 : int) (_31796 : int) : term496 _31794 _31795 _31796.
Proof. exact (@lem2971853 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2971855 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term497 _31794 _31795 _31796.
Proof. exact (@lem2971854 _31794 _31795 _31796 (@lem2971280 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971856 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term498 _31794 _31795 _31796.
Proof. exact (@lem2971855 _31796 _31794 _31795 h1 term169). Qed.
Lemma lem2971857 (_31794 : int) (_31795 : int) (_31796 : int) : (term498 _31794 _31795 _31796) = ((term499 _31794 _31795 _31796) = term140).
Proof. exact (eq_refl (term498 _31794 _31795 _31796)). Qed.
Lemma lem2971858 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : (term499 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2971857 _31794 _31795 _31796) (@lem2971856 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971859 (_31794 : int) (_31795 : int) (_31796 : int) : (term499 _31794 _31795 _31796) = (term280 _31794 _31795 _31796).
Proof. exact (@lem1982733 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2971860 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2971861 (_31794 : int) (_31795 : int) (_31796 : int) : (term500 _31794 _31795 _31796) = (term282 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2971860) (@lem2971859 _31794 _31795 _31796)). Qed.
Lemma lem2971862 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2971863 (_31794 : int) (_31795 : int) (_31796 : int) : ((term499 _31794 _31795 _31796) = term140) = ((term280 _31794 _31795 _31796) = term140).
Proof. exact (MK_COMB (@lem2971861 _31794 _31795 _31796) (@lem2971862)). Qed.
Lemma lem2971864 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : (term280 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2971863 _31794 _31795 _31796) (@lem2971858 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971865 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term646 _31796 _31794 _31795.
Proof. exact (conj (@lem2971864 _31796 _31794 _31795 h1) (@lem2971851 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971867 (x : real) (y : real) : term502 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2971868 (_31796 : int) (_31794 : int) (_31795 : int) : term647 _31796 _31794 _31795.
Proof. exact (@lem2971867 (term280 _31794 _31795 _31796) (term377 _31794 _31795)). Qed.
Lemma lem2971869 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term648 _31796 _31794 _31795.
Proof. exact (@lem2971868 _31796 _31794 _31795 (@lem2971865 _31796 _31794 _31795 h1)). Qed.
Lemma lem2971870 (_31794 : int) (_31796 : int) (_31795 : int) : (term649 _31796 _31794 _31795) = (term650 _31794 _31796 _31795).
Proof. exact (@lem1982753 (real_of_int _31794) (term257 _31794) (term279 _31795 _31796) (term157 _31795)). Qed.
Lemma lem2971871 (_31794 : int) : (term508 _31794) = (term509 _31794).
Proof. exact (@lem1982715 term232 (real_of_int _31794)). Qed.
Lemma lem2971873 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971874 : term169 = term288.
Proof. exact (@lem2971873 term86). Qed.
Lemma lem2971876 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971877 : term232 = term233.
Proof. exact (@lem2971876 term86). Qed.
Lemma lem2971878 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971879 : term510 = term511.
Proof. exact (MK_COMB (@lem2971878) (@lem2971877)). Qed.
Lemma lem2971880 : term512 = term513.
Proof. exact (MK_COMB (@lem2971879) (@lem2971874)). Qed.
Lemma lem2971881 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2971883 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971884 : term305 = term306.
Proof. exact (@lem2971883 (NUMERAL 0) term86). Qed.
Lemma lem2971885 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971886 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971887 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971886 h1) (fun h1 : term306 = True => @lem2971885)). Qed.
Lemma lem2971888 : term306 = True.
Proof. exact (EQ_MP (@lem2971887) (@lem2971885)). Qed.
Lemma lem2971889 : term305 = True.
Proof. exact (TRANS (@lem2971884) (@lem2971888)). Qed.
Lemma lem2971890 : True = term305.
Proof. exact (SYM (@lem2971889)). Qed.
Lemma lem2971891 : term305.
Proof. exact (EQ_MP (@lem2971890) (@lem0)). Qed.
Lemma lem2971892 : term515.
Proof. exact (@lem2971881 (@lem2971891)). Qed.
Lemma lem2971894 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971895 : term305 = term306.
Proof. exact (@lem2971894 (NUMERAL 0) term86). Qed.
Lemma lem2971896 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971897 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971898 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971897 h1) (fun h1 : term306 = True => @lem2971896)). Qed.
Lemma lem2971899 : term306 = True.
Proof. exact (EQ_MP (@lem2971898) (@lem2971896)). Qed.
Lemma lem2971900 : term305 = True.
Proof. exact (TRANS (@lem2971895) (@lem2971899)). Qed.
Lemma lem2971901 : True = term305.
Proof. exact (SYM (@lem2971900)). Qed.
Lemma lem2971902 : term305.
Proof. exact (EQ_MP (@lem2971901) (@lem0)). Qed.
Lemma lem2971903 : term516.
Proof. exact (@lem2971892 (@lem2971902)). Qed.
Lemma lem2971905 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971906 : term305 = term306.
Proof. exact (@lem2971905 (NUMERAL 0) term86). Qed.
Lemma lem2971907 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971908 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971909 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971908 h1) (fun h1 : term306 = True => @lem2971907)). Qed.
Lemma lem2971910 : term306 = True.
Proof. exact (EQ_MP (@lem2971909) (@lem2971907)). Qed.
Lemma lem2971911 : term305 = True.
Proof. exact (TRANS (@lem2971906) (@lem2971910)). Qed.
Lemma lem2971912 : True = term305.
Proof. exact (SYM (@lem2971911)). Qed.
Lemma lem2971913 : term305.
Proof. exact (EQ_MP (@lem2971912) (@lem0)). Qed.
Lemma lem2971914 : term517.
Proof. exact (@lem2971903 (@lem2971913)). Qed.
Lemma lem2971916 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971917 : term241 = term242.
Proof. exact (@lem2971916 term86 term86). Qed.
Lemma lem2971918 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971919 : term244 = term86.
Proof. exact (EQ_MP (@lem2971918) (@lem940073)). Qed.
Lemma lem2971920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971921 : term242 = term169.
Proof. exact (MK_COMB (@lem2971920) (@lem2971919)). Qed.
Lemma lem2971922 : term241 = term169.
Proof. exact (TRANS (@lem2971917) (@lem2971921)). Qed.
Lemma lem2971924 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2971925 : term289 = term292.
Proof. exact (@lem2971924 term86 term86). Qed.
Lemma lem2971926 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971927 : term244 = term86.
Proof. exact (EQ_MP (@lem2971926) (@lem940073)). Qed.
Lemma lem2971928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971929 : term242 = term169.
Proof. exact (MK_COMB (@lem2971928) (@lem2971927)). Qed.
Lemma lem2971930 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2971931 : term292 = term232.
Proof. exact (MK_COMB (@lem2971930) (@lem2971929)). Qed.
Lemma lem2971932 : term289 = term232.
Proof. exact (TRANS (@lem2971925) (@lem2971931)). Qed.
Lemma lem2971933 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971934 : term518 = term510.
Proof. exact (MK_COMB (@lem2971933) (@lem2971932)). Qed.
Lemma lem2971935 : term519 = term512.
Proof. exact (MK_COMB (@lem2971934) (@lem2971922)). Qed.
Lemma lem2971937 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2971938 : term512 = term140.
Proof. exact (@lem2971937 term86). Qed.
Lemma lem2971939 : term519 = term140.
Proof. exact (TRANS (@lem2971935) (@lem2971938)). Qed.
Lemma lem2971940 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971941 : term521 = term371.
Proof. exact (MK_COMB (@lem2971940) (@lem2971939)). Qed.
Lemma lem2971942 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2971943 : term522 = term373.
Proof. exact (MK_COMB (@lem2971941) (@lem2971942)). Qed.
Lemma lem2971945 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971946 : term373 = term140.
Proof. exact (@lem2971945 term86). Qed.
Lemma lem2971947 : term522 = term140.
Proof. exact (TRANS (@lem2971943) (@lem2971946)). Qed.
Lemma lem2971949 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2971950 : term241 = term242.
Proof. exact (@lem2971949 term86 term86). Qed.
Lemma lem2971951 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2971952 : term244 = term86.
Proof. exact (EQ_MP (@lem2971951) (@lem940073)). Qed.
Lemma lem2971953 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2971954 : term242 = term169.
Proof. exact (MK_COMB (@lem2971953) (@lem2971952)). Qed.
Lemma lem2971955 : term241 = term169.
Proof. exact (TRANS (@lem2971950) (@lem2971954)). Qed.
Lemma lem2971956 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2971957 : term375 = term373.
Proof. exact (MK_COMB (@lem2971956) (@lem2971955)). Qed.
Lemma lem2971959 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2971960 : term373 = term140.
Proof. exact (@lem2971959 term86). Qed.
Lemma lem2971961 : term375 = term140.
Proof. exact (TRANS (@lem2971957) (@lem2971960)). Qed.
Lemma lem2971962 : term140 = term375.
Proof. exact (SYM (@lem2971961)). Qed.
Lemma lem2971963 : term522 = term375.
Proof. exact (TRANS (@lem2971947) (@lem2971962)). Qed.
Lemma lem2971964 : term513 = term229.
Proof. exact (@lem2971914 (@lem2971963)). Qed.
Lemma lem2971965 : term512 = term229.
Proof. exact (TRANS (@lem2971880) (@lem2971964)). Qed.
Lemma lem2971967 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2971968 : term229 = term140.
Proof. exact (@lem2971967 term140). Qed.
Lemma lem2971969 : term512 = term140.
Proof. exact (TRANS (@lem2971965) (@lem2971968)). Qed.
Lemma lem2971970 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2971971 : term523 = term371.
Proof. exact (MK_COMB (@lem2971970) (@lem2971969)). Qed.
Lemma lem2971972 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2971973 (_31794 : int) : (term509 _31794) = (term524 _31794).
Proof. exact (MK_COMB (@lem2971971) (@lem2971972 _31794)). Qed.
Lemma lem2971974 (_31794 : int) : (term508 _31794) = (term524 _31794).
Proof. exact (TRANS (@lem2971871 _31794) (@lem2971973 _31794)). Qed.
Lemma lem2971975 (_31794 : int) : (term524 _31794) = term140.
Proof. exact (@lem1982719 (real_of_int _31794)). Qed.
Lemma lem2971976 (_31794 : int) : (term508 _31794) = term140.
Proof. exact (TRANS (@lem2971974 _31794) (@lem2971975 _31794)). Qed.
Lemma lem2971977 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971978 (_31794 : int) : (term525 _31794) = term526.
Proof. exact (MK_COMB (@lem2971977) (@lem2971976 _31794)). Qed.
Lemma lem2971979 (_31795 : int) (_31796 : int) : (term651 _31796 _31795) = (term652 _31795 _31796).
Proof. exact (@lem1982759 (term276 _31795) (term157 _31795) (term257 _31796)). Qed.
Lemma lem2971980 (_31795 : int) : (term529 _31795) = (term530 _31795).
Proof. exact (@lem1982711 term270 term154 (real_of_int _31795)). Qed.
Lemma lem2971982 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2971983 : term154 = term260.
Proof. exact (@lem2971982 term2). Qed.
Lemma lem2971985 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2971986 : term270 = term273.
Proof. exact (@lem2971985 term2). Qed.
Lemma lem2971987 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2971988 : term531 = term532.
Proof. exact (MK_COMB (@lem2971987) (@lem2971986)). Qed.
Lemma lem2971989 : term533 = term534.
Proof. exact (MK_COMB (@lem2971988) (@lem2971983)). Qed.
Lemma lem2971990 : term535.
Proof. exact (@lem1981473 term270 term169 term154 term169 term140 term169). Qed.
Lemma lem2971992 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2971993 : term305 = term306.
Proof. exact (@lem2971992 (NUMERAL 0) term86). Qed.
Lemma lem2971994 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2971995 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2971996 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2971995 h1) (fun h1 : term306 = True => @lem2971994)). Qed.
Lemma lem2971997 : term306 = True.
Proof. exact (EQ_MP (@lem2971996) (@lem2971994)). Qed.
Lemma lem2971998 : term305 = True.
Proof. exact (TRANS (@lem2971993) (@lem2971997)). Qed.
Lemma lem2971999 : True = term305.
Proof. exact (SYM (@lem2971998)). Qed.
Lemma lem2972000 : term305.
Proof. exact (EQ_MP (@lem2971999) (@lem0)). Qed.
Lemma lem2972001 : term536.
Proof. exact (@lem2971990 (@lem2972000)). Qed.
Lemma lem2972003 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972004 : term305 = term306.
Proof. exact (@lem2972003 (NUMERAL 0) term86). Qed.
Lemma lem2972005 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972006 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972007 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972006 h1) (fun h1 : term306 = True => @lem2972005)). Qed.
Lemma lem2972008 : term306 = True.
Proof. exact (EQ_MP (@lem2972007) (@lem2972005)). Qed.
Lemma lem2972009 : term305 = True.
Proof. exact (TRANS (@lem2972004) (@lem2972008)). Qed.
Lemma lem2972010 : True = term305.
Proof. exact (SYM (@lem2972009)). Qed.
Lemma lem2972011 : term305.
Proof. exact (EQ_MP (@lem2972010) (@lem0)). Qed.
Lemma lem2972012 : term537.
Proof. exact (@lem2972001 (@lem2972011)). Qed.
Lemma lem2972014 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972015 : term305 = term306.
Proof. exact (@lem2972014 (NUMERAL 0) term86). Qed.
Lemma lem2972016 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972017 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972018 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972017 h1) (fun h1 : term306 = True => @lem2972016)). Qed.
Lemma lem2972019 : term306 = True.
Proof. exact (EQ_MP (@lem2972018) (@lem2972016)). Qed.
Lemma lem2972020 : term305 = True.
Proof. exact (TRANS (@lem2972015) (@lem2972019)). Qed.
Lemma lem2972021 : True = term305.
Proof. exact (SYM (@lem2972020)). Qed.
Lemma lem2972022 : term305.
Proof. exact (EQ_MP (@lem2972021) (@lem0)). Qed.
Lemma lem2972023 : term538.
Proof. exact (@lem2972012 (@lem2972022)). Qed.
Lemma lem2972025 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972026 : term311 = term312.
Proof. exact (@lem2972025 term2 term86). Qed.
Lemma lem2972027 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2972028 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2972029 : term314 = term2.
Proof. exact (EQ_MP (@lem2972028) (@lem2972027)). Qed.
Lemma lem2972030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972031 : term312 = term154.
Proof. exact (MK_COMB (@lem2972030) (@lem2972029)). Qed.
Lemma lem2972032 : term311 = term154.
Proof. exact (TRANS (@lem2972026) (@lem2972031)). Qed.
Lemma lem2972034 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2972035 : term539 = term540.
Proof. exact (@lem2972034 term2 term86). Qed.
Lemma lem2972036 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2972037 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2972038 : term314 = term2.
Proof. exact (EQ_MP (@lem2972037) (@lem2972036)). Qed.
Lemma lem2972039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972040 : term312 = term154.
Proof. exact (MK_COMB (@lem2972039) (@lem2972038)). Qed.
Lemma lem2972041 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2972042 : term540 = term270.
Proof. exact (MK_COMB (@lem2972041) (@lem2972040)). Qed.
Lemma lem2972043 : term539 = term270.
Proof. exact (TRANS (@lem2972035) (@lem2972042)). Qed.
Lemma lem2972044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972045 : term541 = term531.
Proof. exact (MK_COMB (@lem2972044) (@lem2972043)). Qed.
Lemma lem2972046 : term542 = term533.
Proof. exact (MK_COMB (@lem2972045) (@lem2972032)). Qed.
Lemma lem2972048 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2972049 : term533 = term140.
Proof. exact (@lem2972048 term2). Qed.
Lemma lem2972050 : term542 = term140.
Proof. exact (TRANS (@lem2972046) (@lem2972049)). Qed.
Lemma lem2972051 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972052 : term543 = term371.
Proof. exact (MK_COMB (@lem2972051) (@lem2972050)). Qed.
Lemma lem2972053 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2972054 : term544 = term373.
Proof. exact (MK_COMB (@lem2972052) (@lem2972053)). Qed.
Lemma lem2972056 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972057 : term373 = term140.
Proof. exact (@lem2972056 term86). Qed.
Lemma lem2972058 : term544 = term140.
Proof. exact (TRANS (@lem2972054) (@lem2972057)). Qed.
Lemma lem2972060 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972061 : term241 = term242.
Proof. exact (@lem2972060 term86 term86). Qed.
Lemma lem2972062 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972063 : term244 = term86.
Proof. exact (EQ_MP (@lem2972062) (@lem940073)). Qed.
Lemma lem2972064 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972065 : term242 = term169.
Proof. exact (MK_COMB (@lem2972064) (@lem2972063)). Qed.
Lemma lem2972066 : term241 = term169.
Proof. exact (TRANS (@lem2972061) (@lem2972065)). Qed.
Lemma lem2972067 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2972068 : term375 = term373.
Proof. exact (MK_COMB (@lem2972067) (@lem2972066)). Qed.
Lemma lem2972070 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972071 : term373 = term140.
Proof. exact (@lem2972070 term86). Qed.
Lemma lem2972072 : term375 = term140.
Proof. exact (TRANS (@lem2972068) (@lem2972071)). Qed.
Lemma lem2972073 : term140 = term375.
Proof. exact (SYM (@lem2972072)). Qed.
Lemma lem2972074 : term544 = term375.
Proof. exact (TRANS (@lem2972058) (@lem2972073)). Qed.
Lemma lem2972075 : term534 = term229.
Proof. exact (@lem2972023 (@lem2972074)). Qed.
Lemma lem2972076 : term533 = term229.
Proof. exact (TRANS (@lem2971989) (@lem2972075)). Qed.
Lemma lem2972078 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2972079 : term229 = term140.
Proof. exact (@lem2972078 term140). Qed.
Lemma lem2972080 : term533 = term140.
Proof. exact (TRANS (@lem2972076) (@lem2972079)). Qed.
Lemma lem2972081 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972082 : term545 = term371.
Proof. exact (MK_COMB (@lem2972081) (@lem2972080)). Qed.
Lemma lem2972083 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2972084 (_31795 : int) : (term530 _31795) = (term524 _31795).
Proof. exact (MK_COMB (@lem2972082) (@lem2972083 _31795)). Qed.
Lemma lem2972085 (_31795 : int) : (term529 _31795) = (term524 _31795).
Proof. exact (TRANS (@lem2971980 _31795) (@lem2972084 _31795)). Qed.
Lemma lem2972086 (_31795 : int) : (term524 _31795) = term140.
Proof. exact (@lem1982719 (real_of_int _31795)). Qed.
Lemma lem2972087 (_31795 : int) : (term529 _31795) = term140.
Proof. exact (TRANS (@lem2972085 _31795) (@lem2972086 _31795)). Qed.
Lemma lem2972088 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972089 (_31795 : int) : (term546 _31795) = term526.
Proof. exact (MK_COMB (@lem2972088) (@lem2972087 _31795)). Qed.
Lemma lem2972090 (_31796 : int) : (term257 _31796) = (term257 _31796).
Proof. exact (eq_refl (term257 _31796)). Qed.
Lemma lem2972091 (_31795 : int) (_31796 : int) : (term652 _31795 _31796) = (term653 _31796).
Proof. exact (MK_COMB (@lem2972089 _31795) (@lem2972090 _31796)). Qed.
Lemma lem2972092 (_31795 : int) (_31796 : int) : (term651 _31796 _31795) = (term653 _31796).
Proof. exact (TRANS (@lem2971979 _31795 _31796) (@lem2972091 _31795 _31796)). Qed.
Lemma lem2972093 (_31796 : int) : (term653 _31796) = (term257 _31796).
Proof. exact (@lem1982721 (term257 _31796)). Qed.
Lemma lem2972094 (_31795 : int) (_31796 : int) : (term651 _31796 _31795) = (term257 _31796).
Proof. exact (TRANS (@lem2972092 _31795 _31796) (@lem2972093 _31796)). Qed.
Lemma lem2972095 (_31794 : int) (_31795 : int) (_31796 : int) : (term650 _31794 _31796 _31795) = (term653 _31796).
Proof. exact (MK_COMB (@lem2971978 _31794) (@lem2972094 _31795 _31796)). Qed.
Lemma lem2972096 (_31794 : int) (_31795 : int) (_31796 : int) : (term649 _31796 _31794 _31795) = (term653 _31796).
Proof. exact (TRANS (@lem2971870 _31794 _31796 _31795) (@lem2972095 _31794 _31795 _31796)). Qed.
Lemma lem2972097 (_31796 : int) : (term653 _31796) = (term257 _31796).
Proof. exact (@lem1982721 (term257 _31796)). Qed.
Lemma lem2972098 (_31794 : int) (_31795 : int) (_31796 : int) : (term649 _31796 _31794 _31795) = (term257 _31796).
Proof. exact (TRANS (@lem2972096 _31794 _31795 _31796) (@lem2972097 _31796)). Qed.
Lemma lem2972099 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2972100 (_31794 : int) (_31795 : int) (_31796 : int) : (term654 _31796 _31794 _31795) = (term655 _31796).
Proof. exact (MK_COMB (@lem2972099) (@lem2972098 _31794 _31795 _31796)). Qed.
Lemma lem2972101 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972102 (_31794 : int) (_31795 : int) (_31796 : int) : (term648 _31796 _31794 _31795) = (term656 _31796).
Proof. exact (MK_COMB (@lem2972100 _31794 _31795 _31796) (@lem2972101)). Qed.
Lemma lem2972103 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term656 _31796.
Proof. exact (EQ_MP (@lem2972102 _31794 _31795 _31796) (@lem2971869 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972105 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2972106 : term476 = term305.
Proof. exact (@lem2972105 term140 term169). Qed.
Lemma lem2972108 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972109 : term169 = term288.
Proof. exact (@lem2972108 term86). Qed.
Lemma lem2972111 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972112 : term140 = term229.
Proof. exact (@lem2972111 (NUMERAL 0)). Qed.
Lemma lem2972113 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2972114 : term477 = term478.
Proof. exact (MK_COMB (@lem2972113) (@lem2972112)). Qed.
Lemma lem2972115 : term305 = term479.
Proof. exact (MK_COMB (@lem2972114) (@lem2972109)). Qed.
Lemma lem2972116 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2972118 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972119 : term305 = term306.
Proof. exact (@lem2972118 (NUMERAL 0) term86). Qed.
Lemma lem2972120 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972121 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972122 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972121 h1) (fun h1 : term306 = True => @lem2972120)). Qed.
Lemma lem2972123 : term306 = True.
Proof. exact (EQ_MP (@lem2972122) (@lem2972120)). Qed.
Lemma lem2972124 : term305 = True.
Proof. exact (TRANS (@lem2972119) (@lem2972123)). Qed.
Lemma lem2972125 : True = term305.
Proof. exact (SYM (@lem2972124)). Qed.
Lemma lem2972126 : term305.
Proof. exact (EQ_MP (@lem2972125) (@lem0)). Qed.
Lemma lem2972127 : term481.
Proof. exact (@lem2972116 (@lem2972126)). Qed.
Lemma lem2972129 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972130 : term305 = term306.
Proof. exact (@lem2972129 (NUMERAL 0) term86). Qed.
Lemma lem2972131 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972132 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972133 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972132 h1) (fun h1 : term306 = True => @lem2972131)). Qed.
Lemma lem2972134 : term306 = True.
Proof. exact (EQ_MP (@lem2972133) (@lem2972131)). Qed.
Lemma lem2972135 : term305 = True.
Proof. exact (TRANS (@lem2972130) (@lem2972134)). Qed.
Lemma lem2972136 : True = term305.
Proof. exact (SYM (@lem2972135)). Qed.
Lemma lem2972137 : term305.
Proof. exact (EQ_MP (@lem2972136) (@lem0)). Qed.
Lemma lem2972138 : term479 = term482.
Proof. exact (@lem2972127 (@lem2972137)). Qed.
Lemma lem2972140 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972141 : term241 = term242.
Proof. exact (@lem2972140 term86 term86). Qed.
Lemma lem2972142 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972143 : term244 = term86.
Proof. exact (EQ_MP (@lem2972142) (@lem940073)). Qed.
Lemma lem2972144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972145 : term242 = term169.
Proof. exact (MK_COMB (@lem2972144) (@lem2972143)). Qed.
Lemma lem2972146 : term241 = term169.
Proof. exact (TRANS (@lem2972141) (@lem2972145)). Qed.
Lemma lem2972148 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972149 : term373 = term140.
Proof. exact (@lem2972148 term86). Qed.
Lemma lem2972150 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2972151 : term483 = term477.
Proof. exact (MK_COMB (@lem2972150) (@lem2972149)). Qed.
Lemma lem2972152 : term482 = term305.
Proof. exact (MK_COMB (@lem2972151) (@lem2972146)). Qed.
Lemma lem2972154 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972155 : term305 = term306.
Proof. exact (@lem2972154 (NUMERAL 0) term86). Qed.
Lemma lem2972156 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972157 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972158 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972157 h1) (fun h1 : term306 = True => @lem2972156)). Qed.
Lemma lem2972159 : term306 = True.
Proof. exact (EQ_MP (@lem2972158) (@lem2972156)). Qed.
Lemma lem2972160 : term305 = True.
Proof. exact (TRANS (@lem2972155) (@lem2972159)). Qed.
Lemma lem2972161 : term482 = True.
Proof. exact (TRANS (@lem2972152) (@lem2972160)). Qed.
Lemma lem2972162 : term479 = True.
Proof. exact (TRANS (@lem2972138) (@lem2972161)). Qed.
Lemma lem2972163 : term305 = True.
Proof. exact (TRANS (@lem2972115) (@lem2972162)). Qed.
Lemma lem2972164 : term476 = True.
Proof. exact (TRANS (@lem2972106) (@lem2972163)). Qed.
Lemma lem2972165 : True = term476.
Proof. exact (SYM (@lem2972164)). Qed.
Lemma lem2972166 : term476.
Proof. exact (EQ_MP (@lem2972165) (@lem0)). Qed.
Lemma lem2972167 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term657 _31796.
Proof. exact (conj (@lem2972166) (@lem2972103 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972169 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2972170 (_31796 : int) : term658 _31796.
Proof. exact (@lem2972169 term169 (term257 _31796)). Qed.
Lemma lem2972171 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term659 _31796.
Proof. exact (@lem2972170 _31796 (@lem2972167 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972172 (_31796 : int) : (term660 _31796) = (term257 _31796).
Proof. exact (@lem1982733 (term257 _31796)). Qed.
Lemma lem2972173 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2972174 (_31796 : int) : (term661 _31796) = (term655 _31796).
Proof. exact (MK_COMB (@lem2972173) (@lem2972172 _31796)). Qed.
Lemma lem2972175 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972176 (_31796 : int) : (term659 _31796) = (term656 _31796).
Proof. exact (MK_COMB (@lem2972174 _31796) (@lem2972175)). Qed.
Lemma lem2972177 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term656 _31796.
Proof. exact (EQ_MP (@lem2972176 _31796) (@lem2972171 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972178 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term662 _31796.
Proof. exact (conj (@lem2972177 _31796 _31794 _31795 h1) (@lem2971777 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972180 (x : real) (y : real) : term557 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2972181 (_31796 : int) : term663 _31796.
Proof. exact (@lem2972180 (term257 _31796) (term631 _31796)). Qed.
Lemma lem2972182 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term664 _31796.
Proof. exact (@lem2972181 _31796 (@lem2972178 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972183 (_31796 : int) : (term665 _31796) = (term561 _31796).
Proof. exact (@lem1982763 (term257 _31796) (real_of_int _31796) term232). Qed.
Lemma lem2972184 (_31796 : int) : (term562 _31796) = (term509 _31796).
Proof. exact (@lem1982713 term232 (real_of_int _31796)). Qed.
Lemma lem2972186 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972187 : term169 = term288.
Proof. exact (@lem2972186 term86). Qed.
Lemma lem2972189 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972190 : term232 = term233.
Proof. exact (@lem2972189 term86). Qed.
Lemma lem2972191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972192 : term510 = term511.
Proof. exact (MK_COMB (@lem2972191) (@lem2972190)). Qed.
Lemma lem2972193 : term512 = term513.
Proof. exact (MK_COMB (@lem2972192) (@lem2972187)). Qed.
Lemma lem2972194 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2972196 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972197 : term305 = term306.
Proof. exact (@lem2972196 (NUMERAL 0) term86). Qed.
Lemma lem2972198 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972199 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972200 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972199 h1) (fun h1 : term306 = True => @lem2972198)). Qed.
Lemma lem2972201 : term306 = True.
Proof. exact (EQ_MP (@lem2972200) (@lem2972198)). Qed.
Lemma lem2972202 : term305 = True.
Proof. exact (TRANS (@lem2972197) (@lem2972201)). Qed.
Lemma lem2972203 : True = term305.
Proof. exact (SYM (@lem2972202)). Qed.
Lemma lem2972204 : term305.
Proof. exact (EQ_MP (@lem2972203) (@lem0)). Qed.
Lemma lem2972205 : term515.
Proof. exact (@lem2972194 (@lem2972204)). Qed.
Lemma lem2972207 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972208 : term305 = term306.
Proof. exact (@lem2972207 (NUMERAL 0) term86). Qed.
Lemma lem2972209 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972210 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972211 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972210 h1) (fun h1 : term306 = True => @lem2972209)). Qed.
Lemma lem2972212 : term306 = True.
Proof. exact (EQ_MP (@lem2972211) (@lem2972209)). Qed.
Lemma lem2972213 : term305 = True.
Proof. exact (TRANS (@lem2972208) (@lem2972212)). Qed.
Lemma lem2972214 : True = term305.
Proof. exact (SYM (@lem2972213)). Qed.
Lemma lem2972215 : term305.
Proof. exact (EQ_MP (@lem2972214) (@lem0)). Qed.
Lemma lem2972216 : term516.
Proof. exact (@lem2972205 (@lem2972215)). Qed.
Lemma lem2972218 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972219 : term305 = term306.
Proof. exact (@lem2972218 (NUMERAL 0) term86). Qed.
Lemma lem2972220 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972221 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972222 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972221 h1) (fun h1 : term306 = True => @lem2972220)). Qed.
Lemma lem2972223 : term306 = True.
Proof. exact (EQ_MP (@lem2972222) (@lem2972220)). Qed.
Lemma lem2972224 : term305 = True.
Proof. exact (TRANS (@lem2972219) (@lem2972223)). Qed.
Lemma lem2972225 : True = term305.
Proof. exact (SYM (@lem2972224)). Qed.
Lemma lem2972226 : term305.
Proof. exact (EQ_MP (@lem2972225) (@lem0)). Qed.
Lemma lem2972227 : term517.
Proof. exact (@lem2972216 (@lem2972226)). Qed.
Lemma lem2972229 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972230 : term241 = term242.
Proof. exact (@lem2972229 term86 term86). Qed.
Lemma lem2972231 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972232 : term244 = term86.
Proof. exact (EQ_MP (@lem2972231) (@lem940073)). Qed.
Lemma lem2972233 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972234 : term242 = term169.
Proof. exact (MK_COMB (@lem2972233) (@lem2972232)). Qed.
Lemma lem2972235 : term241 = term169.
Proof. exact (TRANS (@lem2972230) (@lem2972234)). Qed.
Lemma lem2972237 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2972238 : term289 = term292.
Proof. exact (@lem2972237 term86 term86). Qed.
Lemma lem2972239 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972240 : term244 = term86.
Proof. exact (EQ_MP (@lem2972239) (@lem940073)). Qed.
Lemma lem2972241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972242 : term242 = term169.
Proof. exact (MK_COMB (@lem2972241) (@lem2972240)). Qed.
Lemma lem2972243 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2972244 : term292 = term232.
Proof. exact (MK_COMB (@lem2972243) (@lem2972242)). Qed.
Lemma lem2972245 : term289 = term232.
Proof. exact (TRANS (@lem2972238) (@lem2972244)). Qed.
Lemma lem2972246 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972247 : term518 = term510.
Proof. exact (MK_COMB (@lem2972246) (@lem2972245)). Qed.
Lemma lem2972248 : term519 = term512.
Proof. exact (MK_COMB (@lem2972247) (@lem2972235)). Qed.
Lemma lem2972250 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2972251 : term512 = term140.
Proof. exact (@lem2972250 term86). Qed.
Lemma lem2972252 : term519 = term140.
Proof. exact (TRANS (@lem2972248) (@lem2972251)). Qed.
Lemma lem2972253 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972254 : term521 = term371.
Proof. exact (MK_COMB (@lem2972253) (@lem2972252)). Qed.
Lemma lem2972255 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2972256 : term522 = term373.
Proof. exact (MK_COMB (@lem2972254) (@lem2972255)). Qed.
Lemma lem2972258 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972259 : term373 = term140.
Proof. exact (@lem2972258 term86). Qed.
Lemma lem2972260 : term522 = term140.
Proof. exact (TRANS (@lem2972256) (@lem2972259)). Qed.
Lemma lem2972262 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972263 : term241 = term242.
Proof. exact (@lem2972262 term86 term86). Qed.
Lemma lem2972264 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972265 : term244 = term86.
Proof. exact (EQ_MP (@lem2972264) (@lem940073)). Qed.
Lemma lem2972266 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972267 : term242 = term169.
Proof. exact (MK_COMB (@lem2972266) (@lem2972265)). Qed.
Lemma lem2972268 : term241 = term169.
Proof. exact (TRANS (@lem2972263) (@lem2972267)). Qed.
Lemma lem2972269 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2972270 : term375 = term373.
Proof. exact (MK_COMB (@lem2972269) (@lem2972268)). Qed.
Lemma lem2972272 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972273 : term373 = term140.
Proof. exact (@lem2972272 term86). Qed.
Lemma lem2972274 : term375 = term140.
Proof. exact (TRANS (@lem2972270) (@lem2972273)). Qed.
Lemma lem2972275 : term140 = term375.
Proof. exact (SYM (@lem2972274)). Qed.
Lemma lem2972276 : term522 = term375.
Proof. exact (TRANS (@lem2972260) (@lem2972275)). Qed.
Lemma lem2972277 : term513 = term229.
Proof. exact (@lem2972227 (@lem2972276)). Qed.
Lemma lem2972278 : term512 = term229.
Proof. exact (TRANS (@lem2972193) (@lem2972277)). Qed.
Lemma lem2972280 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2972281 : term229 = term140.
Proof. exact (@lem2972280 term140). Qed.
Lemma lem2972282 : term512 = term140.
Proof. exact (TRANS (@lem2972278) (@lem2972281)). Qed.
Lemma lem2972283 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972284 : term523 = term371.
Proof. exact (MK_COMB (@lem2972283) (@lem2972282)). Qed.
Lemma lem2972285 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2972286 (_31796 : int) : (term509 _31796) = (term524 _31796).
Proof. exact (MK_COMB (@lem2972284) (@lem2972285 _31796)). Qed.
Lemma lem2972287 (_31796 : int) : (term562 _31796) = (term524 _31796).
Proof. exact (TRANS (@lem2972184 _31796) (@lem2972286 _31796)). Qed.
Lemma lem2972288 (_31796 : int) : (term524 _31796) = term140.
Proof. exact (@lem1982719 (real_of_int _31796)). Qed.
Lemma lem2972289 (_31796 : int) : (term562 _31796) = term140.
Proof. exact (TRANS (@lem2972287 _31796) (@lem2972288 _31796)). Qed.
Lemma lem2972290 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972291 (_31796 : int) : (term563 _31796) = term526.
Proof. exact (MK_COMB (@lem2972290) (@lem2972289 _31796)). Qed.
Lemma lem2972292 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem2972293 (_31796 : int) : (term561 _31796) = term564.
Proof. exact (MK_COMB (@lem2972291 _31796) (@lem2972292)). Qed.
Lemma lem2972294 (_31796 : int) : (term665 _31796) = term564.
Proof. exact (TRANS (@lem2972183 _31796) (@lem2972293 _31796)). Qed.
Lemma lem2972295 : term564 = term232.
Proof. exact (@lem1982721 term232). Qed.
Lemma lem2972296 (_31796 : int) : (term665 _31796) = term232.
Proof. exact (TRANS (@lem2972294 _31796) (@lem2972295)). Qed.
Lemma lem2972297 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2972298 (_31796 : int) : (term666 _31796) = term566.
Proof. exact (MK_COMB (@lem2972297) (@lem2972296 _31796)). Qed.
Lemma lem2972299 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972300 (_31796 : int) : (term664 _31796) = term567.
Proof. exact (MK_COMB (@lem2972298 _31796) (@lem2972299)). Qed.
Lemma lem2972301 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : term567.
Proof. exact (EQ_MP (@lem2972300 _31796) (@lem2972182 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972303 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2972304 : term567 = term568.
Proof. exact (@lem2972303 term140 term232). Qed.
Lemma lem2972306 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972307 : term232 = term233.
Proof. exact (@lem2972306 term86). Qed.
Lemma lem2972309 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972310 : term140 = term229.
Proof. exact (@lem2972309 (NUMERAL 0)). Qed.
Lemma lem2972311 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2972312 : term142 = term569.
Proof. exact (MK_COMB (@lem2972311) (@lem2972310)). Qed.
Lemma lem2972313 : term568 = term570.
Proof. exact (MK_COMB (@lem2972312) (@lem2972307)). Qed.
Lemma lem2972314 : term571.
Proof. exact (@lem1980026 term140 term169 term232 term169). Qed.
Lemma lem2972316 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972317 : term305 = term306.
Proof. exact (@lem2972316 (NUMERAL 0) term86). Qed.
Lemma lem2972318 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972319 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972320 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972319 h1) (fun h1 : term306 = True => @lem2972318)). Qed.
Lemma lem2972321 : term306 = True.
Proof. exact (EQ_MP (@lem2972320) (@lem2972318)). Qed.
Lemma lem2972322 : term305 = True.
Proof. exact (TRANS (@lem2972317) (@lem2972321)). Qed.
Lemma lem2972323 : True = term305.
Proof. exact (SYM (@lem2972322)). Qed.
Lemma lem2972324 : term305.
Proof. exact (EQ_MP (@lem2972323) (@lem0)). Qed.
Lemma lem2972325 : term572.
Proof. exact (@lem2972314 (@lem2972324)). Qed.
Lemma lem2972327 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972328 : term305 = term306.
Proof. exact (@lem2972327 (NUMERAL 0) term86). Qed.
Lemma lem2972329 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972330 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972331 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972330 h1) (fun h1 : term306 = True => @lem2972329)). Qed.
Lemma lem2972332 : term306 = True.
Proof. exact (EQ_MP (@lem2972331) (@lem2972329)). Qed.
Lemma lem2972333 : term305 = True.
Proof. exact (TRANS (@lem2972328) (@lem2972332)). Qed.
Lemma lem2972334 : True = term305.
Proof. exact (SYM (@lem2972333)). Qed.
Lemma lem2972335 : term305.
Proof. exact (EQ_MP (@lem2972334) (@lem0)). Qed.
Lemma lem2972336 : term570 = term573.
Proof. exact (@lem2972325 (@lem2972335)). Qed.
Lemma lem2972338 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2972339 : term289 = term292.
Proof. exact (@lem2972338 term86 term86). Qed.
Lemma lem2972340 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972341 : term244 = term86.
Proof. exact (EQ_MP (@lem2972340) (@lem940073)). Qed.
Lemma lem2972342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972343 : term242 = term169.
Proof. exact (MK_COMB (@lem2972342) (@lem2972341)). Qed.
Lemma lem2972344 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2972345 : term292 = term232.
Proof. exact (MK_COMB (@lem2972344) (@lem2972343)). Qed.
Lemma lem2972346 : term289 = term232.
Proof. exact (TRANS (@lem2972339) (@lem2972345)). Qed.
Lemma lem2972348 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972349 : term373 = term140.
Proof. exact (@lem2972348 term86). Qed.
Lemma lem2972350 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2972351 : term574 = term142.
Proof. exact (MK_COMB (@lem2972350) (@lem2972349)). Qed.
Lemma lem2972352 : term573 = term568.
Proof. exact (MK_COMB (@lem2972351) (@lem2972346)). Qed.
Lemma lem2972354 (m : nat) (n : nat) : (term575 m n) = (term576 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2972355 : term568 = term577.
Proof. exact (@lem2972354 (NUMERAL 0) term86). Qed.
Lemma lem2972356 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972357 (h1 : term307 = (BIT1 0)) : (term86 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2972358 : (term307 = (BIT1 0)) = ((term86 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972357 h1) (fun h1 : (term86 = (NUMERAL 0)) = False => @lem2972356)). Qed.
Lemma lem2972359 : (term86 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2972358) (@lem2972356)). Qed.
Lemma lem2972360 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2972361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2972362 : term578 = (and True).
Proof. exact (MK_COMB (@lem2972361) (@lem2972360)). Qed.
Lemma lem2972363 : term577 = (True /\ False).
Proof. exact (MK_COMB (@lem2972362) (@lem2972359)). Qed.
Lemma lem2972365 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2972366 : term577 = False.
Proof. exact (TRANS (@lem2972363) (@lem2972365)). Qed.
Lemma lem2972367 : term568 = False.
Proof. exact (TRANS (@lem2972355) (@lem2972366)). Qed.
Lemma lem2972368 : term573 = False.
Proof. exact (TRANS (@lem2972352) (@lem2972367)). Qed.
Lemma lem2972369 : term570 = False.
Proof. exact (TRANS (@lem2972336) (@lem2972368)). Qed.
Lemma lem2972370 : term568 = False.
Proof. exact (TRANS (@lem2972313) (@lem2972369)). Qed.
Lemma lem2972371 : term567 = False.
Proof. exact (TRANS (@lem2972304) (@lem2972370)). Qed.
Lemma lem2972372 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term579 _31796 _31794 _31795) : False.
Proof. exact (EQ_MP (@lem2972371) (@lem2972301 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972373 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term469 _31796 _31794 _31795) : False.
Proof. exact (or_elim (@lem2970587 _31796 _31794 _31795 h1) (fun h0 : term475 _31796 _31794 _31795 => @lem2971269 _31796 _31794 _31795 h0) (fun h0 : term579 _31796 _31794 _31795 => @lem2972372 _31796 _31794 _31795 h0)). Qed.
Lemma lem2972374 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term465 _31796 _31794 _31795) : term465 _31796 _31794 _31795.
Proof. exact (h1). Qed.
Lemma lem2972375 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term667 _31796 _31794 _31795.
Proof. exact (h1). Qed.
Lemma lem2972376 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term466 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2972375 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972378 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term453 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2972376 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972380 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term440 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2972378 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972382 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term427 _31794 _31795.
Proof. exact (proj2 (@lem2972380 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972383 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term331 _31794 _31795 _31796.
Proof. exact (proj1 (@lem2972380 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972385 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : (term280 _31794 _31795 _31796) = term140.
Proof. exact (proj1 (@lem2972383 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972386 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term404 _31794 _31795.
Proof. exact (proj2 (@lem2972382 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972387 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term339 _31794 _31795.
Proof. exact (proj1 (@lem2972382 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972389 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2972390 : term476 = term305.
Proof. exact (@lem2972389 term140 term169). Qed.
Lemma lem2972392 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972393 : term169 = term288.
Proof. exact (@lem2972392 term86). Qed.
Lemma lem2972395 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972396 : term140 = term229.
Proof. exact (@lem2972395 (NUMERAL 0)). Qed.
Lemma lem2972397 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2972398 : term477 = term478.
Proof. exact (MK_COMB (@lem2972397) (@lem2972396)). Qed.
Lemma lem2972399 : term305 = term479.
Proof. exact (MK_COMB (@lem2972398) (@lem2972393)). Qed.
Lemma lem2972400 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2972402 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972403 : term305 = term306.
Proof. exact (@lem2972402 (NUMERAL 0) term86). Qed.
Lemma lem2972404 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972405 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972406 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972405 h1) (fun h1 : term306 = True => @lem2972404)). Qed.
Lemma lem2972407 : term306 = True.
Proof. exact (EQ_MP (@lem2972406) (@lem2972404)). Qed.
Lemma lem2972408 : term305 = True.
Proof. exact (TRANS (@lem2972403) (@lem2972407)). Qed.
Lemma lem2972409 : True = term305.
Proof. exact (SYM (@lem2972408)). Qed.
Lemma lem2972410 : term305.
Proof. exact (EQ_MP (@lem2972409) (@lem0)). Qed.
Lemma lem2972411 : term481.
Proof. exact (@lem2972400 (@lem2972410)). Qed.
Lemma lem2972413 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972414 : term305 = term306.
Proof. exact (@lem2972413 (NUMERAL 0) term86). Qed.
Lemma lem2972415 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972416 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972417 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972416 h1) (fun h1 : term306 = True => @lem2972415)). Qed.
Lemma lem2972418 : term306 = True.
Proof. exact (EQ_MP (@lem2972417) (@lem2972415)). Qed.
Lemma lem2972419 : term305 = True.
Proof. exact (TRANS (@lem2972414) (@lem2972418)). Qed.
Lemma lem2972420 : True = term305.
Proof. exact (SYM (@lem2972419)). Qed.
Lemma lem2972421 : term305.
Proof. exact (EQ_MP (@lem2972420) (@lem0)). Qed.
Lemma lem2972422 : term479 = term482.
Proof. exact (@lem2972411 (@lem2972421)). Qed.
Lemma lem2972424 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972425 : term241 = term242.
Proof. exact (@lem2972424 term86 term86). Qed.
Lemma lem2972426 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972427 : term244 = term86.
Proof. exact (EQ_MP (@lem2972426) (@lem940073)). Qed.
Lemma lem2972428 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972429 : term242 = term169.
Proof. exact (MK_COMB (@lem2972428) (@lem2972427)). Qed.
Lemma lem2972430 : term241 = term169.
Proof. exact (TRANS (@lem2972425) (@lem2972429)). Qed.
Lemma lem2972432 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972433 : term373 = term140.
Proof. exact (@lem2972432 term86). Qed.
Lemma lem2972434 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2972435 : term483 = term477.
Proof. exact (MK_COMB (@lem2972434) (@lem2972433)). Qed.
Lemma lem2972436 : term482 = term305.
Proof. exact (MK_COMB (@lem2972435) (@lem2972430)). Qed.
Lemma lem2972438 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972439 : term305 = term306.
Proof. exact (@lem2972438 (NUMERAL 0) term86). Qed.
Lemma lem2972440 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972441 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972442 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972441 h1) (fun h1 : term306 = True => @lem2972440)). Qed.
Lemma lem2972443 : term306 = True.
Proof. exact (EQ_MP (@lem2972442) (@lem2972440)). Qed.
Lemma lem2972444 : term305 = True.
Proof. exact (TRANS (@lem2972439) (@lem2972443)). Qed.
Lemma lem2972445 : term482 = True.
Proof. exact (TRANS (@lem2972436) (@lem2972444)). Qed.
Lemma lem2972446 : term479 = True.
Proof. exact (TRANS (@lem2972422) (@lem2972445)). Qed.
Lemma lem2972447 : term305 = True.
Proof. exact (TRANS (@lem2972399) (@lem2972446)). Qed.
Lemma lem2972448 : term476 = True.
Proof. exact (TRANS (@lem2972390) (@lem2972447)). Qed.
Lemma lem2972449 : True = term476.
Proof. exact (SYM (@lem2972448)). Qed.
Lemma lem2972450 : term476.
Proof. exact (EQ_MP (@lem2972449) (@lem0)). Qed.
Lemma lem2972451 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term668 _31794 _31795.
Proof. exact (conj (@lem2972450) (@lem2972386 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972453 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2972454 (_31794 : int) (_31795 : int) : term669 _31794 _31795.
Proof. exact (@lem2972453 term169 (term401 _31794 _31795)). Qed.
Lemma lem2972455 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term670 _31794 _31795.
Proof. exact (@lem2972454 _31794 _31795 (@lem2972451 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972456 (_31794 : int) (_31795 : int) : (term671 _31794 _31795) = (term401 _31794 _31795).
Proof. exact (@lem1982733 (term401 _31794 _31795)). Qed.
Lemma lem2972457 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2972458 (_31794 : int) (_31795 : int) : (term672 _31794 _31795) = (term403 _31794 _31795).
Proof. exact (MK_COMB (@lem2972457) (@lem2972456 _31794 _31795)). Qed.
Lemma lem2972459 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972460 (_31794 : int) (_31795 : int) : (term670 _31794 _31795) = (term404 _31794 _31795).
Proof. exact (MK_COMB (@lem2972458 _31794 _31795) (@lem2972459)). Qed.
Lemma lem2972461 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term404 _31794 _31795.
Proof. exact (EQ_MP (@lem2972460 _31794 _31795) (@lem2972455 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972463 (y : real) : term495 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2972464 (_31794 : int) (_31795 : int) (_31796 : int) : term496 _31794 _31795 _31796.
Proof. exact (@lem2972463 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2972465 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term497 _31794 _31795 _31796.
Proof. exact (@lem2972464 _31794 _31795 _31796 (@lem2972385 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972466 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term585 _31794 _31795 _31796.
Proof. exact (@lem2972465 _31796 _31794 _31795 h1 term232). Qed.
Lemma lem2972467 (_31794 : int) (_31795 : int) (_31796 : int) : (term585 _31794 _31795 _31796) = ((term586 _31794 _31795 _31796) = term140).
Proof. exact (eq_refl (term585 _31794 _31795 _31796)). Qed.
Lemma lem2972468 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : (term586 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2972467 _31794 _31795 _31796) (@lem2972466 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972469 (_31794 : int) (_31795 : int) (_31796 : int) : (term586 _31794 _31795 _31796) = (term587 _31794 _31795 _31796).
Proof. exact (@lem1982781 (real_of_int _31794) term232 (term279 _31795 _31796)). Qed.
Lemma lem2972470 (_31795 : int) (_31796 : int) : (term588 _31795 _31796) = (term589 _31795 _31796).
Proof. exact (@lem1982781 (term276 _31795) term232 (term257 _31796)). Qed.
Lemma lem2972471 (_31796 : int) : (term590 _31796) = (term591 _31796).
Proof. exact (@lem1982749 term232 term232 (real_of_int _31796)). Qed.
Lemma lem2972473 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972474 : term232 = term233.
Proof. exact (@lem2972473 term86). Qed.
Lemma lem2972476 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972477 : term232 = term233.
Proof. exact (@lem2972476 term86). Qed.
Lemma lem2972478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972479 : term234 = term235.
Proof. exact (MK_COMB (@lem2972478) (@lem2972477)). Qed.
Lemma lem2972480 : term592 = term593.
Proof. exact (MK_COMB (@lem2972479) (@lem2972474)). Qed.
Lemma lem2972481 : term593 = term594.
Proof. exact (@lem1981613 term232 term232 term169 term169). Qed.
Lemma lem2972483 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972484 : term241 = term242.
Proof. exact (@lem2972483 term86 term86). Qed.
Lemma lem2972485 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972486 : term244 = term86.
Proof. exact (EQ_MP (@lem2972485) (@lem940073)). Qed.
Lemma lem2972487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972488 : term242 = term169.
Proof. exact (MK_COMB (@lem2972487) (@lem2972486)). Qed.
Lemma lem2972489 : term241 = term169.
Proof. exact (TRANS (@lem2972484) (@lem2972488)). Qed.
Lemma lem2972491 (m : nat) (n : nat) : (term595 m n) = (term240 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2972492 : term592 = term242.
Proof. exact (@lem2972491 term86 term86). Qed.
Lemma lem2972493 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972494 : term244 = term86.
Proof. exact (EQ_MP (@lem2972493) (@lem940073)). Qed.
Lemma lem2972495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972496 : term242 = term169.
Proof. exact (MK_COMB (@lem2972495) (@lem2972494)). Qed.
Lemma lem2972497 : term592 = term169.
Proof. exact (TRANS (@lem2972492) (@lem2972496)). Qed.
Lemma lem2972498 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2972499 : term596 = term597.
Proof. exact (MK_COMB (@lem2972498) (@lem2972497)). Qed.
Lemma lem2972500 : term594 = term288.
Proof. exact (MK_COMB (@lem2972499) (@lem2972489)). Qed.
Lemma lem2972501 : term593 = term288.
Proof. exact (TRANS (@lem2972481) (@lem2972500)). Qed.
Lemma lem2972502 : term592 = term288.
Proof. exact (TRANS (@lem2972480) (@lem2972501)). Qed.
Lemma lem2972504 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2972505 : term288 = term169.
Proof. exact (@lem2972504 term169). Qed.
Lemma lem2972506 : term592 = term169.
Proof. exact (TRANS (@lem2972502) (@lem2972505)). Qed.
Lemma lem2972507 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972508 : term598 = term323.
Proof. exact (MK_COMB (@lem2972507) (@lem2972506)). Qed.
Lemma lem2972509 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2972510 (_31796 : int) : (term591 _31796) = (term488 _31796).
Proof. exact (MK_COMB (@lem2972508) (@lem2972509 _31796)). Qed.
Lemma lem2972511 (_31796 : int) : (term590 _31796) = (term488 _31796).
Proof. exact (TRANS (@lem2972471 _31796) (@lem2972510 _31796)). Qed.
Lemma lem2972512 (_31796 : int) : (term488 _31796) = (real_of_int _31796).
Proof. exact (@lem1982709 (real_of_int _31796)). Qed.
Lemma lem2972513 (_31796 : int) : (term590 _31796) = (real_of_int _31796).
Proof. exact (TRANS (@lem2972511 _31796) (@lem2972512 _31796)). Qed.
Lemma lem2972514 (_31795 : int) : (term599 _31795) = (term600 _31795).
Proof. exact (@lem1982749 term232 term270 (real_of_int _31795)). Qed.
Lemma lem2972516 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972517 : term270 = term273.
Proof. exact (@lem2972516 term2). Qed.
Lemma lem2972519 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972520 : term232 = term233.
Proof. exact (@lem2972519 term86). Qed.
Lemma lem2972521 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972522 : term234 = term235.
Proof. exact (MK_COMB (@lem2972521) (@lem2972520)). Qed.
Lemma lem2972523 : term601 = term602.
Proof. exact (MK_COMB (@lem2972522) (@lem2972517)). Qed.
Lemma lem2972524 : term602 = term603.
Proof. exact (@lem1981613 term232 term270 term169 term169). Qed.
Lemma lem2972526 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972527 : term241 = term242.
Proof. exact (@lem2972526 term86 term86). Qed.
Lemma lem2972528 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972529 : term244 = term86.
Proof. exact (EQ_MP (@lem2972528) (@lem940073)). Qed.
Lemma lem2972530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972531 : term242 = term169.
Proof. exact (MK_COMB (@lem2972530) (@lem2972529)). Qed.
Lemma lem2972532 : term241 = term169.
Proof. exact (TRANS (@lem2972527) (@lem2972531)). Qed.
Lemma lem2972534 (m : nat) (n : nat) : (term595 m n) = (term240 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2972535 : term601 = term269.
Proof. exact (@lem2972534 term86 term2). Qed.
Lemma lem2972536 : term267 = term27.
Proof. exact (@lem996238 term27). Qed.
Lemma lem2972537 : (term267 = term27) = (term268 = term2).
Proof. exact (@lem1007663 (BIT1 0) term27 term27). Qed.
Lemma lem2972538 : term268 = term2.
Proof. exact (EQ_MP (@lem2972537) (@lem2972536)). Qed.
Lemma lem2972539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972540 : term269 = term154.
Proof. exact (MK_COMB (@lem2972539) (@lem2972538)). Qed.
Lemma lem2972541 : term601 = term154.
Proof. exact (TRANS (@lem2972535) (@lem2972540)). Qed.
Lemma lem2972542 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2972543 : term604 = term605.
Proof. exact (MK_COMB (@lem2972542) (@lem2972541)). Qed.
Lemma lem2972544 : term603 = term260.
Proof. exact (MK_COMB (@lem2972543) (@lem2972532)). Qed.
Lemma lem2972545 : term602 = term260.
Proof. exact (TRANS (@lem2972524) (@lem2972544)). Qed.
Lemma lem2972546 : term601 = term260.
Proof. exact (TRANS (@lem2972523) (@lem2972545)). Qed.
Lemma lem2972548 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2972549 : term260 = term154.
Proof. exact (@lem2972548 term154). Qed.
Lemma lem2972550 : term601 = term154.
Proof. exact (TRANS (@lem2972546) (@lem2972549)). Qed.
Lemma lem2972551 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972552 : term606 = term156.
Proof. exact (MK_COMB (@lem2972551) (@lem2972550)). Qed.
Lemma lem2972553 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2972554 (_31795 : int) : (term600 _31795) = (term157 _31795).
Proof. exact (MK_COMB (@lem2972552) (@lem2972553 _31795)). Qed.
Lemma lem2972555 (_31795 : int) : (term599 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2972514 _31795) (@lem2972554 _31795)). Qed.
Lemma lem2972556 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972557 (_31795 : int) : (term607 _31795) = (term159 _31795).
Proof. exact (MK_COMB (@lem2972556) (@lem2972555 _31795)). Qed.
Lemma lem2972558 (_31795 : int) (_31796 : int) : (term589 _31795 _31796) = (term160 _31795 _31796).
Proof. exact (MK_COMB (@lem2972557 _31795) (@lem2972513 _31796)). Qed.
Lemma lem2972559 (_31795 : int) (_31796 : int) : (term588 _31795 _31796) = (term160 _31795 _31796).
Proof. exact (TRANS (@lem2972470 _31795 _31796) (@lem2972558 _31795 _31796)). Qed.
Lemma lem2972562 (_31794 : int) : (term295 _31794) = (term295 _31794).
Proof. exact (eq_refl (term295 _31794)). Qed.
Lemma lem2972563 (_31794 : int) (_31795 : int) (_31796 : int) : (term587 _31794 _31795 _31796) = (term608 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2972562 _31794) (@lem2972559 _31795 _31796)). Qed.
Lemma lem2972564 (_31794 : int) (_31795 : int) (_31796 : int) : (term586 _31794 _31795 _31796) = (term608 _31794 _31795 _31796).
Proof. exact (TRANS (@lem2972469 _31794 _31795 _31796) (@lem2972563 _31794 _31795 _31796)). Qed.
Lemma lem2972565 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2972566 (_31794 : int) (_31795 : int) (_31796 : int) : (term609 _31794 _31795 _31796) = (term610 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2972565) (@lem2972564 _31794 _31795 _31796)). Qed.
Lemma lem2972567 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972568 (_31794 : int) (_31795 : int) (_31796 : int) : ((term586 _31794 _31795 _31796) = term140) = ((term608 _31794 _31795 _31796) = term140).
Proof. exact (MK_COMB (@lem2972566 _31794 _31795 _31796) (@lem2972567)). Qed.
Lemma lem2972569 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : (term608 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2972568 _31794 _31795 _31796) (@lem2972468 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972570 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term673 _31796 _31794 _31795.
Proof. exact (conj (@lem2972569 _31796 _31794 _31795 h1) (@lem2972461 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972572 (x : real) (y : real) : term502 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2972573 (_31796 : int) (_31794 : int) (_31795 : int) : term674 _31796 _31794 _31795.
Proof. exact (@lem2972572 (term608 _31794 _31795 _31796) (term401 _31794 _31795)). Qed.
Lemma lem2972574 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term675 _31796 _31794 _31795.
Proof. exact (@lem2972573 _31796 _31794 _31795 (@lem2972570 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972575 (_31794 : int) (_31796 : int) (_31795 : int) : (term676 _31796 _31794 _31795) = (term677 _31794 _31796 _31795).
Proof. exact (@lem1982753 (term257 _31794) (real_of_int _31794) (term160 _31795 _31796) (term400 _31795)). Qed.
Lemma lem2972576 (_31794 : int) : (term562 _31794) = (term509 _31794).
Proof. exact (@lem1982713 term232 (real_of_int _31794)). Qed.
Lemma lem2972578 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972579 : term169 = term288.
Proof. exact (@lem2972578 term86). Qed.
Lemma lem2972581 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972582 : term232 = term233.
Proof. exact (@lem2972581 term86). Qed.
Lemma lem2972583 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972584 : term510 = term511.
Proof. exact (MK_COMB (@lem2972583) (@lem2972582)). Qed.
Lemma lem2972585 : term512 = term513.
Proof. exact (MK_COMB (@lem2972584) (@lem2972579)). Qed.
Lemma lem2972586 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2972588 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972589 : term305 = term306.
Proof. exact (@lem2972588 (NUMERAL 0) term86). Qed.
Lemma lem2972590 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972591 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972592 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972591 h1) (fun h1 : term306 = True => @lem2972590)). Qed.
Lemma lem2972593 : term306 = True.
Proof. exact (EQ_MP (@lem2972592) (@lem2972590)). Qed.
Lemma lem2972594 : term305 = True.
Proof. exact (TRANS (@lem2972589) (@lem2972593)). Qed.
Lemma lem2972595 : True = term305.
Proof. exact (SYM (@lem2972594)). Qed.
Lemma lem2972596 : term305.
Proof. exact (EQ_MP (@lem2972595) (@lem0)). Qed.
Lemma lem2972597 : term515.
Proof. exact (@lem2972586 (@lem2972596)). Qed.
Lemma lem2972599 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972600 : term305 = term306.
Proof. exact (@lem2972599 (NUMERAL 0) term86). Qed.
Lemma lem2972601 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972602 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972603 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972602 h1) (fun h1 : term306 = True => @lem2972601)). Qed.
Lemma lem2972604 : term306 = True.
Proof. exact (EQ_MP (@lem2972603) (@lem2972601)). Qed.
Lemma lem2972605 : term305 = True.
Proof. exact (TRANS (@lem2972600) (@lem2972604)). Qed.
Lemma lem2972606 : True = term305.
Proof. exact (SYM (@lem2972605)). Qed.
Lemma lem2972607 : term305.
Proof. exact (EQ_MP (@lem2972606) (@lem0)). Qed.
Lemma lem2972608 : term516.
Proof. exact (@lem2972597 (@lem2972607)). Qed.
Lemma lem2972610 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972611 : term305 = term306.
Proof. exact (@lem2972610 (NUMERAL 0) term86). Qed.
Lemma lem2972612 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972613 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972614 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972613 h1) (fun h1 : term306 = True => @lem2972612)). Qed.
Lemma lem2972615 : term306 = True.
Proof. exact (EQ_MP (@lem2972614) (@lem2972612)). Qed.
Lemma lem2972616 : term305 = True.
Proof. exact (TRANS (@lem2972611) (@lem2972615)). Qed.
Lemma lem2972617 : True = term305.
Proof. exact (SYM (@lem2972616)). Qed.
Lemma lem2972618 : term305.
Proof. exact (EQ_MP (@lem2972617) (@lem0)). Qed.
Lemma lem2972619 : term517.
Proof. exact (@lem2972608 (@lem2972618)). Qed.
Lemma lem2972621 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972622 : term241 = term242.
Proof. exact (@lem2972621 term86 term86). Qed.
Lemma lem2972623 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972624 : term244 = term86.
Proof. exact (EQ_MP (@lem2972623) (@lem940073)). Qed.
Lemma lem2972625 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972626 : term242 = term169.
Proof. exact (MK_COMB (@lem2972625) (@lem2972624)). Qed.
Lemma lem2972627 : term241 = term169.
Proof. exact (TRANS (@lem2972622) (@lem2972626)). Qed.
Lemma lem2972629 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2972630 : term289 = term292.
Proof. exact (@lem2972629 term86 term86). Qed.
Lemma lem2972631 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972632 : term244 = term86.
Proof. exact (EQ_MP (@lem2972631) (@lem940073)). Qed.
Lemma lem2972633 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972634 : term242 = term169.
Proof. exact (MK_COMB (@lem2972633) (@lem2972632)). Qed.
Lemma lem2972635 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2972636 : term292 = term232.
Proof. exact (MK_COMB (@lem2972635) (@lem2972634)). Qed.
Lemma lem2972637 : term289 = term232.
Proof. exact (TRANS (@lem2972630) (@lem2972636)). Qed.
Lemma lem2972638 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972639 : term518 = term510.
Proof. exact (MK_COMB (@lem2972638) (@lem2972637)). Qed.
Lemma lem2972640 : term519 = term512.
Proof. exact (MK_COMB (@lem2972639) (@lem2972627)). Qed.
Lemma lem2972642 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2972643 : term512 = term140.
Proof. exact (@lem2972642 term86). Qed.
Lemma lem2972644 : term519 = term140.
Proof. exact (TRANS (@lem2972640) (@lem2972643)). Qed.
Lemma lem2972645 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972646 : term521 = term371.
Proof. exact (MK_COMB (@lem2972645) (@lem2972644)). Qed.
Lemma lem2972647 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2972648 : term522 = term373.
Proof. exact (MK_COMB (@lem2972646) (@lem2972647)). Qed.
Lemma lem2972650 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972651 : term373 = term140.
Proof. exact (@lem2972650 term86). Qed.
Lemma lem2972652 : term522 = term140.
Proof. exact (TRANS (@lem2972648) (@lem2972651)). Qed.
Lemma lem2972654 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972655 : term241 = term242.
Proof. exact (@lem2972654 term86 term86). Qed.
Lemma lem2972656 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972657 : term244 = term86.
Proof. exact (EQ_MP (@lem2972656) (@lem940073)). Qed.
Lemma lem2972658 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972659 : term242 = term169.
Proof. exact (MK_COMB (@lem2972658) (@lem2972657)). Qed.
Lemma lem2972660 : term241 = term169.
Proof. exact (TRANS (@lem2972655) (@lem2972659)). Qed.
Lemma lem2972661 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2972662 : term375 = term373.
Proof. exact (MK_COMB (@lem2972661) (@lem2972660)). Qed.
Lemma lem2972664 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972665 : term373 = term140.
Proof. exact (@lem2972664 term86). Qed.
Lemma lem2972666 : term375 = term140.
Proof. exact (TRANS (@lem2972662) (@lem2972665)). Qed.
Lemma lem2972667 : term140 = term375.
Proof. exact (SYM (@lem2972666)). Qed.
Lemma lem2972668 : term522 = term375.
Proof. exact (TRANS (@lem2972652) (@lem2972667)). Qed.
Lemma lem2972669 : term513 = term229.
Proof. exact (@lem2972619 (@lem2972668)). Qed.
Lemma lem2972670 : term512 = term229.
Proof. exact (TRANS (@lem2972585) (@lem2972669)). Qed.
Lemma lem2972672 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2972673 : term229 = term140.
Proof. exact (@lem2972672 term140). Qed.
Lemma lem2972674 : term512 = term140.
Proof. exact (TRANS (@lem2972670) (@lem2972673)). Qed.
Lemma lem2972675 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972676 : term523 = term371.
Proof. exact (MK_COMB (@lem2972675) (@lem2972674)). Qed.
Lemma lem2972677 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2972678 (_31794 : int) : (term509 _31794) = (term524 _31794).
Proof. exact (MK_COMB (@lem2972676) (@lem2972677 _31794)). Qed.
Lemma lem2972679 (_31794 : int) : (term562 _31794) = (term524 _31794).
Proof. exact (TRANS (@lem2972576 _31794) (@lem2972678 _31794)). Qed.
Lemma lem2972680 (_31794 : int) : (term524 _31794) = term140.
Proof. exact (@lem1982719 (real_of_int _31794)). Qed.
Lemma lem2972681 (_31794 : int) : (term562 _31794) = term140.
Proof. exact (TRANS (@lem2972679 _31794) (@lem2972680 _31794)). Qed.
Lemma lem2972682 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972683 (_31794 : int) : (term563 _31794) = term526.
Proof. exact (MK_COMB (@lem2972682) (@lem2972681 _31794)). Qed.
Lemma lem2972684 (_31795 : int) (_31796 : int) : (term678 _31796 _31795) = (term679 _31795 _31796).
Proof. exact (@lem1982753 (term157 _31795) (term276 _31795) (real_of_int _31796) term270). Qed.
Lemma lem2972685 (_31795 : int) : (term618 _31795) = (term619 _31795).
Proof. exact (@lem1982711 term154 term270 (real_of_int _31795)). Qed.
Lemma lem2972687 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972688 : term270 = term273.
Proof. exact (@lem2972687 term2). Qed.
Lemma lem2972690 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972691 : term154 = term260.
Proof. exact (@lem2972690 term2). Qed.
Lemma lem2972692 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972693 : term297 = term300.
Proof. exact (MK_COMB (@lem2972692) (@lem2972691)). Qed.
Lemma lem2972694 : term620 = term621.
Proof. exact (MK_COMB (@lem2972693) (@lem2972688)). Qed.
Lemma lem2972695 : term622.
Proof. exact (@lem1981473 term154 term169 term270 term169 term140 term169). Qed.
Lemma lem2972697 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972698 : term305 = term306.
Proof. exact (@lem2972697 (NUMERAL 0) term86). Qed.
Lemma lem2972699 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972700 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972701 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972700 h1) (fun h1 : term306 = True => @lem2972699)). Qed.
Lemma lem2972702 : term306 = True.
Proof. exact (EQ_MP (@lem2972701) (@lem2972699)). Qed.
Lemma lem2972703 : term305 = True.
Proof. exact (TRANS (@lem2972698) (@lem2972702)). Qed.
Lemma lem2972704 : True = term305.
Proof. exact (SYM (@lem2972703)). Qed.
Lemma lem2972705 : term305.
Proof. exact (EQ_MP (@lem2972704) (@lem0)). Qed.
Lemma lem2972706 : term623.
Proof. exact (@lem2972695 (@lem2972705)). Qed.
Lemma lem2972708 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972709 : term305 = term306.
Proof. exact (@lem2972708 (NUMERAL 0) term86). Qed.
Lemma lem2972710 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972711 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972712 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972711 h1) (fun h1 : term306 = True => @lem2972710)). Qed.
Lemma lem2972713 : term306 = True.
Proof. exact (EQ_MP (@lem2972712) (@lem2972710)). Qed.
Lemma lem2972714 : term305 = True.
Proof. exact (TRANS (@lem2972709) (@lem2972713)). Qed.
Lemma lem2972715 : True = term305.
Proof. exact (SYM (@lem2972714)). Qed.
Lemma lem2972716 : term305.
Proof. exact (EQ_MP (@lem2972715) (@lem0)). Qed.
Lemma lem2972717 : term624.
Proof. exact (@lem2972706 (@lem2972716)). Qed.
Lemma lem2972719 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972720 : term305 = term306.
Proof. exact (@lem2972719 (NUMERAL 0) term86). Qed.
Lemma lem2972721 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972722 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972723 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972722 h1) (fun h1 : term306 = True => @lem2972721)). Qed.
Lemma lem2972724 : term306 = True.
Proof. exact (EQ_MP (@lem2972723) (@lem2972721)). Qed.
Lemma lem2972725 : term305 = True.
Proof. exact (TRANS (@lem2972720) (@lem2972724)). Qed.
Lemma lem2972726 : True = term305.
Proof. exact (SYM (@lem2972725)). Qed.
Lemma lem2972727 : term305.
Proof. exact (EQ_MP (@lem2972726) (@lem0)). Qed.
Lemma lem2972728 : term625.
Proof. exact (@lem2972717 (@lem2972727)). Qed.
Lemma lem2972730 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2972731 : term539 = term540.
Proof. exact (@lem2972730 term2 term86). Qed.
Lemma lem2972732 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2972733 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2972734 : term314 = term2.
Proof. exact (EQ_MP (@lem2972733) (@lem2972732)). Qed.
Lemma lem2972735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972736 : term312 = term154.
Proof. exact (MK_COMB (@lem2972735) (@lem2972734)). Qed.
Lemma lem2972737 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2972738 : term540 = term270.
Proof. exact (MK_COMB (@lem2972737) (@lem2972736)). Qed.
Lemma lem2972739 : term539 = term270.
Proof. exact (TRANS (@lem2972731) (@lem2972738)). Qed.
Lemma lem2972741 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972742 : term311 = term312.
Proof. exact (@lem2972741 term2 term86). Qed.
Lemma lem2972743 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2972744 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2972745 : term314 = term2.
Proof. exact (EQ_MP (@lem2972744) (@lem2972743)). Qed.
Lemma lem2972746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972747 : term312 = term154.
Proof. exact (MK_COMB (@lem2972746) (@lem2972745)). Qed.
Lemma lem2972748 : term311 = term154.
Proof. exact (TRANS (@lem2972742) (@lem2972747)). Qed.
Lemma lem2972749 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972750 : term315 = term297.
Proof. exact (MK_COMB (@lem2972749) (@lem2972748)). Qed.
Lemma lem2972751 : term626 = term620.
Proof. exact (MK_COMB (@lem2972750) (@lem2972739)). Qed.
Lemma lem2972753 (m : nat) : (term369 m) = term140.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2972754 : term620 = term140.
Proof. exact (@lem2972753 term2). Qed.
Lemma lem2972755 : term626 = term140.
Proof. exact (TRANS (@lem2972751) (@lem2972754)). Qed.
Lemma lem2972756 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972757 : term627 = term371.
Proof. exact (MK_COMB (@lem2972756) (@lem2972755)). Qed.
Lemma lem2972758 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2972759 : term628 = term373.
Proof. exact (MK_COMB (@lem2972757) (@lem2972758)). Qed.
Lemma lem2972761 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972762 : term373 = term140.
Proof. exact (@lem2972761 term86). Qed.
Lemma lem2972763 : term628 = term140.
Proof. exact (TRANS (@lem2972759) (@lem2972762)). Qed.
Lemma lem2972765 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972766 : term241 = term242.
Proof. exact (@lem2972765 term86 term86). Qed.
Lemma lem2972767 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972768 : term244 = term86.
Proof. exact (EQ_MP (@lem2972767) (@lem940073)). Qed.
Lemma lem2972769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972770 : term242 = term169.
Proof. exact (MK_COMB (@lem2972769) (@lem2972768)). Qed.
Lemma lem2972771 : term241 = term169.
Proof. exact (TRANS (@lem2972766) (@lem2972770)). Qed.
Lemma lem2972772 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2972773 : term375 = term373.
Proof. exact (MK_COMB (@lem2972772) (@lem2972771)). Qed.
Lemma lem2972775 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972776 : term373 = term140.
Proof. exact (@lem2972775 term86). Qed.
Lemma lem2972777 : term375 = term140.
Proof. exact (TRANS (@lem2972773) (@lem2972776)). Qed.
Lemma lem2972778 : term140 = term375.
Proof. exact (SYM (@lem2972777)). Qed.
Lemma lem2972779 : term628 = term375.
Proof. exact (TRANS (@lem2972763) (@lem2972778)). Qed.
Lemma lem2972780 : term621 = term229.
Proof. exact (@lem2972728 (@lem2972779)). Qed.
Lemma lem2972781 : term620 = term229.
Proof. exact (TRANS (@lem2972694) (@lem2972780)). Qed.
Lemma lem2972783 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2972784 : term229 = term140.
Proof. exact (@lem2972783 term140). Qed.
Lemma lem2972785 : term620 = term140.
Proof. exact (TRANS (@lem2972781) (@lem2972784)). Qed.
Lemma lem2972786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2972787 : term629 = term371.
Proof. exact (MK_COMB (@lem2972786) (@lem2972785)). Qed.
Lemma lem2972788 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2972789 (_31795 : int) : (term619 _31795) = (term524 _31795).
Proof. exact (MK_COMB (@lem2972787) (@lem2972788 _31795)). Qed.
Lemma lem2972790 (_31795 : int) : (term618 _31795) = (term524 _31795).
Proof. exact (TRANS (@lem2972685 _31795) (@lem2972789 _31795)). Qed.
Lemma lem2972791 (_31795 : int) : (term524 _31795) = term140.
Proof. exact (@lem1982719 (real_of_int _31795)). Qed.
Lemma lem2972792 (_31795 : int) : (term618 _31795) = term140.
Proof. exact (TRANS (@lem2972790 _31795) (@lem2972791 _31795)). Qed.
Lemma lem2972793 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972794 (_31795 : int) : (term630 _31795) = term526.
Proof. exact (MK_COMB (@lem2972793) (@lem2972792 _31795)). Qed.
Lemma lem2972795 (_31796 : int) : (term680 _31796) = (term680 _31796).
Proof. exact (eq_refl (term680 _31796)). Qed.
Lemma lem2972796 (_31795 : int) (_31796 : int) : (term679 _31795 _31796) = (term681 _31796).
Proof. exact (MK_COMB (@lem2972794 _31795) (@lem2972795 _31796)). Qed.
Lemma lem2972797 (_31795 : int) (_31796 : int) : (term678 _31796 _31795) = (term681 _31796).
Proof. exact (TRANS (@lem2972684 _31795 _31796) (@lem2972796 _31795 _31796)). Qed.
Lemma lem2972798 (_31796 : int) : (term681 _31796) = (term680 _31796).
Proof. exact (@lem1982721 (term680 _31796)). Qed.
Lemma lem2972799 (_31795 : int) (_31796 : int) : (term678 _31796 _31795) = (term680 _31796).
Proof. exact (TRANS (@lem2972797 _31795 _31796) (@lem2972798 _31796)). Qed.
Lemma lem2972800 (_31794 : int) (_31795 : int) (_31796 : int) : (term677 _31794 _31796 _31795) = (term681 _31796).
Proof. exact (MK_COMB (@lem2972683 _31794) (@lem2972799 _31795 _31796)). Qed.
Lemma lem2972801 (_31794 : int) (_31795 : int) (_31796 : int) : (term676 _31796 _31794 _31795) = (term681 _31796).
Proof. exact (TRANS (@lem2972575 _31794 _31796 _31795) (@lem2972800 _31794 _31795 _31796)). Qed.
Lemma lem2972802 (_31796 : int) : (term681 _31796) = (term680 _31796).
Proof. exact (@lem1982721 (term680 _31796)). Qed.
Lemma lem2972803 (_31794 : int) (_31795 : int) (_31796 : int) : (term676 _31796 _31794 _31795) = (term680 _31796).
Proof. exact (TRANS (@lem2972801 _31794 _31795 _31796) (@lem2972802 _31796)). Qed.
Lemma lem2972804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2972805 (_31794 : int) (_31795 : int) (_31796 : int) : (term682 _31796 _31794 _31795) = (term683 _31796).
Proof. exact (MK_COMB (@lem2972804) (@lem2972803 _31794 _31795 _31796)). Qed.
Lemma lem2972806 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972807 (_31794 : int) (_31795 : int) (_31796 : int) : (term675 _31796 _31794 _31795) = (term684 _31796).
Proof. exact (MK_COMB (@lem2972805 _31794 _31795 _31796) (@lem2972806)). Qed.
Lemma lem2972808 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term684 _31796.
Proof. exact (EQ_MP (@lem2972807 _31794 _31795 _31796) (@lem2972574 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972810 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2972811 : term476 = term305.
Proof. exact (@lem2972810 term140 term169). Qed.
Lemma lem2972813 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972814 : term169 = term288.
Proof. exact (@lem2972813 term86). Qed.
Lemma lem2972816 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972817 : term140 = term229.
Proof. exact (@lem2972816 (NUMERAL 0)). Qed.
Lemma lem2972818 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2972819 : term477 = term478.
Proof. exact (MK_COMB (@lem2972818) (@lem2972817)). Qed.
Lemma lem2972820 : term305 = term479.
Proof. exact (MK_COMB (@lem2972819) (@lem2972814)). Qed.
Lemma lem2972821 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2972823 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972824 : term305 = term306.
Proof. exact (@lem2972823 (NUMERAL 0) term86). Qed.
Lemma lem2972825 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972826 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972827 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972826 h1) (fun h1 : term306 = True => @lem2972825)). Qed.
Lemma lem2972828 : term306 = True.
Proof. exact (EQ_MP (@lem2972827) (@lem2972825)). Qed.
Lemma lem2972829 : term305 = True.
Proof. exact (TRANS (@lem2972824) (@lem2972828)). Qed.
Lemma lem2972830 : True = term305.
Proof. exact (SYM (@lem2972829)). Qed.
Lemma lem2972831 : term305.
Proof. exact (EQ_MP (@lem2972830) (@lem0)). Qed.
Lemma lem2972832 : term481.
Proof. exact (@lem2972821 (@lem2972831)). Qed.
Lemma lem2972834 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972835 : term305 = term306.
Proof. exact (@lem2972834 (NUMERAL 0) term86). Qed.
Lemma lem2972836 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972837 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972838 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972837 h1) (fun h1 : term306 = True => @lem2972836)). Qed.
Lemma lem2972839 : term306 = True.
Proof. exact (EQ_MP (@lem2972838) (@lem2972836)). Qed.
Lemma lem2972840 : term305 = True.
Proof. exact (TRANS (@lem2972835) (@lem2972839)). Qed.
Lemma lem2972841 : True = term305.
Proof. exact (SYM (@lem2972840)). Qed.
Lemma lem2972842 : term305.
Proof. exact (EQ_MP (@lem2972841) (@lem0)). Qed.
Lemma lem2972843 : term479 = term482.
Proof. exact (@lem2972832 (@lem2972842)). Qed.
Lemma lem2972845 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972846 : term241 = term242.
Proof. exact (@lem2972845 term86 term86). Qed.
Lemma lem2972847 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972848 : term244 = term86.
Proof. exact (EQ_MP (@lem2972847) (@lem940073)). Qed.
Lemma lem2972849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972850 : term242 = term169.
Proof. exact (MK_COMB (@lem2972849) (@lem2972848)). Qed.
Lemma lem2972851 : term241 = term169.
Proof. exact (TRANS (@lem2972846) (@lem2972850)). Qed.
Lemma lem2972853 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972854 : term373 = term140.
Proof. exact (@lem2972853 term86). Qed.
Lemma lem2972855 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2972856 : term483 = term477.
Proof. exact (MK_COMB (@lem2972855) (@lem2972854)). Qed.
Lemma lem2972857 : term482 = term305.
Proof. exact (MK_COMB (@lem2972856) (@lem2972851)). Qed.
Lemma lem2972859 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972860 : term305 = term306.
Proof. exact (@lem2972859 (NUMERAL 0) term86). Qed.
Lemma lem2972861 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972862 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972863 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972862 h1) (fun h1 : term306 = True => @lem2972861)). Qed.
Lemma lem2972864 : term306 = True.
Proof. exact (EQ_MP (@lem2972863) (@lem2972861)). Qed.
Lemma lem2972865 : term305 = True.
Proof. exact (TRANS (@lem2972860) (@lem2972864)). Qed.
Lemma lem2972866 : term482 = True.
Proof. exact (TRANS (@lem2972857) (@lem2972865)). Qed.
Lemma lem2972867 : term479 = True.
Proof. exact (TRANS (@lem2972843) (@lem2972866)). Qed.
Lemma lem2972868 : term305 = True.
Proof. exact (TRANS (@lem2972820) (@lem2972867)). Qed.
Lemma lem2972869 : term476 = True.
Proof. exact (TRANS (@lem2972811) (@lem2972868)). Qed.
Lemma lem2972870 : True = term476.
Proof. exact (SYM (@lem2972869)). Qed.
Lemma lem2972871 : term476.
Proof. exact (EQ_MP (@lem2972870) (@lem0)). Qed.
Lemma lem2972872 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term685 _31796.
Proof. exact (conj (@lem2972871) (@lem2972808 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972874 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2972875 (_31796 : int) : term686 _31796.
Proof. exact (@lem2972874 term169 (term680 _31796)). Qed.
Lemma lem2972876 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term687 _31796.
Proof. exact (@lem2972875 _31796 (@lem2972872 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972877 (_31796 : int) : (term688 _31796) = (term680 _31796).
Proof. exact (@lem1982733 (term680 _31796)). Qed.
Lemma lem2972878 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2972879 (_31796 : int) : (term689 _31796) = (term683 _31796).
Proof. exact (MK_COMB (@lem2972878) (@lem2972877 _31796)). Qed.
Lemma lem2972880 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972881 (_31796 : int) : (term687 _31796) = (term684 _31796).
Proof. exact (MK_COMB (@lem2972879 _31796) (@lem2972880)). Qed.
Lemma lem2972882 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term684 _31796.
Proof. exact (EQ_MP (@lem2972881 _31796) (@lem2972876 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972884 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2972885 : term476 = term305.
Proof. exact (@lem2972884 term140 term169). Qed.
Lemma lem2972887 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972888 : term169 = term288.
Proof. exact (@lem2972887 term86). Qed.
Lemma lem2972890 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972891 : term140 = term229.
Proof. exact (@lem2972890 (NUMERAL 0)). Qed.
Lemma lem2972892 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2972893 : term477 = term478.
Proof. exact (MK_COMB (@lem2972892) (@lem2972891)). Qed.
Lemma lem2972894 : term305 = term479.
Proof. exact (MK_COMB (@lem2972893) (@lem2972888)). Qed.
Lemma lem2972895 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2972897 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972898 : term305 = term306.
Proof. exact (@lem2972897 (NUMERAL 0) term86). Qed.
Lemma lem2972899 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972900 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972901 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972900 h1) (fun h1 : term306 = True => @lem2972899)). Qed.
Lemma lem2972902 : term306 = True.
Proof. exact (EQ_MP (@lem2972901) (@lem2972899)). Qed.
Lemma lem2972903 : term305 = True.
Proof. exact (TRANS (@lem2972898) (@lem2972902)). Qed.
Lemma lem2972904 : True = term305.
Proof. exact (SYM (@lem2972903)). Qed.
Lemma lem2972905 : term305.
Proof. exact (EQ_MP (@lem2972904) (@lem0)). Qed.
Lemma lem2972906 : term481.
Proof. exact (@lem2972895 (@lem2972905)). Qed.
Lemma lem2972908 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972909 : term305 = term306.
Proof. exact (@lem2972908 (NUMERAL 0) term86). Qed.
Lemma lem2972910 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972911 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972912 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972911 h1) (fun h1 : term306 = True => @lem2972910)). Qed.
Lemma lem2972913 : term306 = True.
Proof. exact (EQ_MP (@lem2972912) (@lem2972910)). Qed.
Lemma lem2972914 : term305 = True.
Proof. exact (TRANS (@lem2972909) (@lem2972913)). Qed.
Lemma lem2972915 : True = term305.
Proof. exact (SYM (@lem2972914)). Qed.
Lemma lem2972916 : term305.
Proof. exact (EQ_MP (@lem2972915) (@lem0)). Qed.
Lemma lem2972917 : term479 = term482.
Proof. exact (@lem2972906 (@lem2972916)). Qed.
Lemma lem2972919 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2972920 : term241 = term242.
Proof. exact (@lem2972919 term86 term86). Qed.
Lemma lem2972921 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2972922 : term244 = term86.
Proof. exact (EQ_MP (@lem2972921) (@lem940073)). Qed.
Lemma lem2972923 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2972924 : term242 = term169.
Proof. exact (MK_COMB (@lem2972923) (@lem2972922)). Qed.
Lemma lem2972925 : term241 = term169.
Proof. exact (TRANS (@lem2972920) (@lem2972924)). Qed.
Lemma lem2972927 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2972928 : term373 = term140.
Proof. exact (@lem2972927 term86). Qed.
Lemma lem2972929 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2972930 : term483 = term477.
Proof. exact (MK_COMB (@lem2972929) (@lem2972928)). Qed.
Lemma lem2972931 : term482 = term305.
Proof. exact (MK_COMB (@lem2972930) (@lem2972925)). Qed.
Lemma lem2972933 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972934 : term305 = term306.
Proof. exact (@lem2972933 (NUMERAL 0) term86). Qed.
Lemma lem2972935 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972936 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972937 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972936 h1) (fun h1 : term306 = True => @lem2972935)). Qed.
Lemma lem2972938 : term306 = True.
Proof. exact (EQ_MP (@lem2972937) (@lem2972935)). Qed.
Lemma lem2972939 : term305 = True.
Proof. exact (TRANS (@lem2972934) (@lem2972938)). Qed.
Lemma lem2972940 : term482 = True.
Proof. exact (TRANS (@lem2972931) (@lem2972939)). Qed.
Lemma lem2972941 : term479 = True.
Proof. exact (TRANS (@lem2972917) (@lem2972940)). Qed.
Lemma lem2972942 : term305 = True.
Proof. exact (TRANS (@lem2972894) (@lem2972941)). Qed.
Lemma lem2972943 : term476 = True.
Proof. exact (TRANS (@lem2972885) (@lem2972942)). Qed.
Lemma lem2972944 : True = term476.
Proof. exact (SYM (@lem2972943)). Qed.
Lemma lem2972945 : term476.
Proof. exact (EQ_MP (@lem2972944) (@lem0)). Qed.
Lemma lem2972946 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term490 _31794 _31795.
Proof. exact (conj (@lem2972945) (@lem2972387 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972948 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2972949 (_31794 : int) (_31795 : int) : term491 _31794 _31795.
Proof. exact (@lem2972948 term169 (term336 _31794 _31795)). Qed.
Lemma lem2972950 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term492 _31794 _31795.
Proof. exact (@lem2972949 _31794 _31795 (@lem2972946 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972951 (_31794 : int) (_31795 : int) : (term493 _31794 _31795) = (term336 _31794 _31795).
Proof. exact (@lem1982733 (term336 _31794 _31795)). Qed.
Lemma lem2972952 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2972953 (_31794 : int) (_31795 : int) : (term494 _31794 _31795) = (term338 _31794 _31795).
Proof. exact (MK_COMB (@lem2972952) (@lem2972951 _31794 _31795)). Qed.
Lemma lem2972954 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972955 (_31794 : int) (_31795 : int) : (term492 _31794 _31795) = (term339 _31794 _31795).
Proof. exact (MK_COMB (@lem2972953 _31794 _31795) (@lem2972954)). Qed.
Lemma lem2972956 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term339 _31794 _31795.
Proof. exact (EQ_MP (@lem2972955 _31794 _31795) (@lem2972950 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972958 (y : real) : term495 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2972959 (_31794 : int) (_31795 : int) (_31796 : int) : term496 _31794 _31795 _31796.
Proof. exact (@lem2972958 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2972960 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term497 _31794 _31795 _31796.
Proof. exact (@lem2972959 _31794 _31795 _31796 (@lem2972385 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972961 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term498 _31794 _31795 _31796.
Proof. exact (@lem2972960 _31796 _31794 _31795 h1 term169). Qed.
Lemma lem2972962 (_31794 : int) (_31795 : int) (_31796 : int) : (term498 _31794 _31795 _31796) = ((term499 _31794 _31795 _31796) = term140).
Proof. exact (eq_refl (term498 _31794 _31795 _31796)). Qed.
Lemma lem2972963 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : (term499 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2972962 _31794 _31795 _31796) (@lem2972961 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972964 (_31794 : int) (_31795 : int) (_31796 : int) : (term499 _31794 _31795 _31796) = (term280 _31794 _31795 _31796).
Proof. exact (@lem1982733 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2972965 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2972966 (_31794 : int) (_31795 : int) (_31796 : int) : (term500 _31794 _31795 _31796) = (term282 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2972965) (@lem2972964 _31794 _31795 _31796)). Qed.
Lemma lem2972967 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2972968 (_31794 : int) (_31795 : int) (_31796 : int) : ((term499 _31794 _31795 _31796) = term140) = ((term280 _31794 _31795 _31796) = term140).
Proof. exact (MK_COMB (@lem2972966 _31794 _31795 _31796) (@lem2972967)). Qed.
Lemma lem2972969 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : (term280 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2972968 _31794 _31795 _31796) (@lem2972963 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972970 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term501 _31796 _31794 _31795.
Proof. exact (conj (@lem2972969 _31796 _31794 _31795 h1) (@lem2972956 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972972 (x : real) (y : real) : term502 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2972973 (_31796 : int) (_31794 : int) (_31795 : int) : term503 _31796 _31794 _31795.
Proof. exact (@lem2972972 (term280 _31794 _31795 _31796) (term336 _31794 _31795)). Qed.
Lemma lem2972974 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term504 _31796 _31794 _31795.
Proof. exact (@lem2972973 _31796 _31794 _31795 (@lem2972970 _31796 _31794 _31795 h1)). Qed.
Lemma lem2972975 (_31794 : int) (_31796 : int) (_31795 : int) : (term505 _31796 _31794 _31795) = (term506 _31794 _31796 _31795).
Proof. exact (@lem1982753 (real_of_int _31794) (term257 _31794) (term279 _31795 _31796) (term507 _31795)). Qed.
Lemma lem2972976 (_31794 : int) : (term508 _31794) = (term509 _31794).
Proof. exact (@lem1982715 term232 (real_of_int _31794)). Qed.
Lemma lem2972978 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2972979 : term169 = term288.
Proof. exact (@lem2972978 term86). Qed.
Lemma lem2972981 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2972982 : term232 = term233.
Proof. exact (@lem2972981 term86). Qed.
Lemma lem2972983 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2972984 : term510 = term511.
Proof. exact (MK_COMB (@lem2972983) (@lem2972982)). Qed.
Lemma lem2972985 : term512 = term513.
Proof. exact (MK_COMB (@lem2972984) (@lem2972979)). Qed.
Lemma lem2972986 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2972988 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2972989 : term305 = term306.
Proof. exact (@lem2972988 (NUMERAL 0) term86). Qed.
Lemma lem2972990 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2972991 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2972992 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2972991 h1) (fun h1 : term306 = True => @lem2972990)). Qed.
Lemma lem2972993 : term306 = True.
Proof. exact (EQ_MP (@lem2972992) (@lem2972990)). Qed.
Lemma lem2972994 : term305 = True.
Proof. exact (TRANS (@lem2972989) (@lem2972993)). Qed.
Lemma lem2972995 : True = term305.
Proof. exact (SYM (@lem2972994)). Qed.
Lemma lem2972996 : term305.
Proof. exact (EQ_MP (@lem2972995) (@lem0)). Qed.
Lemma lem2972997 : term515.
Proof. exact (@lem2972986 (@lem2972996)). Qed.
Lemma lem2972999 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973000 : term305 = term306.
Proof. exact (@lem2972999 (NUMERAL 0) term86). Qed.
Lemma lem2973001 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973002 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973003 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973002 h1) (fun h1 : term306 = True => @lem2973001)). Qed.
Lemma lem2973004 : term306 = True.
Proof. exact (EQ_MP (@lem2973003) (@lem2973001)). Qed.
Lemma lem2973005 : term305 = True.
Proof. exact (TRANS (@lem2973000) (@lem2973004)). Qed.
Lemma lem2973006 : True = term305.
Proof. exact (SYM (@lem2973005)). Qed.
Lemma lem2973007 : term305.
Proof. exact (EQ_MP (@lem2973006) (@lem0)). Qed.
Lemma lem2973008 : term516.
Proof. exact (@lem2972997 (@lem2973007)). Qed.
Lemma lem2973010 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973011 : term305 = term306.
Proof. exact (@lem2973010 (NUMERAL 0) term86). Qed.
Lemma lem2973012 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973013 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973014 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973013 h1) (fun h1 : term306 = True => @lem2973012)). Qed.
Lemma lem2973015 : term306 = True.
Proof. exact (EQ_MP (@lem2973014) (@lem2973012)). Qed.
Lemma lem2973016 : term305 = True.
Proof. exact (TRANS (@lem2973011) (@lem2973015)). Qed.
Lemma lem2973017 : True = term305.
Proof. exact (SYM (@lem2973016)). Qed.
Lemma lem2973018 : term305.
Proof. exact (EQ_MP (@lem2973017) (@lem0)). Qed.
Lemma lem2973019 : term517.
Proof. exact (@lem2973008 (@lem2973018)). Qed.
Lemma lem2973021 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973022 : term241 = term242.
Proof. exact (@lem2973021 term86 term86). Qed.
Lemma lem2973023 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973024 : term244 = term86.
Proof. exact (EQ_MP (@lem2973023) (@lem940073)). Qed.
Lemma lem2973025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973026 : term242 = term169.
Proof. exact (MK_COMB (@lem2973025) (@lem2973024)). Qed.
Lemma lem2973027 : term241 = term169.
Proof. exact (TRANS (@lem2973022) (@lem2973026)). Qed.
Lemma lem2973029 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973030 : term289 = term292.
Proof. exact (@lem2973029 term86 term86). Qed.
Lemma lem2973031 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973032 : term244 = term86.
Proof. exact (EQ_MP (@lem2973031) (@lem940073)). Qed.
Lemma lem2973033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973034 : term242 = term169.
Proof. exact (MK_COMB (@lem2973033) (@lem2973032)). Qed.
Lemma lem2973035 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973036 : term292 = term232.
Proof. exact (MK_COMB (@lem2973035) (@lem2973034)). Qed.
Lemma lem2973037 : term289 = term232.
Proof. exact (TRANS (@lem2973030) (@lem2973036)). Qed.
Lemma lem2973038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973039 : term518 = term510.
Proof. exact (MK_COMB (@lem2973038) (@lem2973037)). Qed.
Lemma lem2973040 : term519 = term512.
Proof. exact (MK_COMB (@lem2973039) (@lem2973027)). Qed.
Lemma lem2973042 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2973043 : term512 = term140.
Proof. exact (@lem2973042 term86). Qed.
Lemma lem2973044 : term519 = term140.
Proof. exact (TRANS (@lem2973040) (@lem2973043)). Qed.
Lemma lem2973045 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973046 : term521 = term371.
Proof. exact (MK_COMB (@lem2973045) (@lem2973044)). Qed.
Lemma lem2973047 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2973048 : term522 = term373.
Proof. exact (MK_COMB (@lem2973046) (@lem2973047)). Qed.
Lemma lem2973050 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973051 : term373 = term140.
Proof. exact (@lem2973050 term86). Qed.
Lemma lem2973052 : term522 = term140.
Proof. exact (TRANS (@lem2973048) (@lem2973051)). Qed.
Lemma lem2973054 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973055 : term241 = term242.
Proof. exact (@lem2973054 term86 term86). Qed.
Lemma lem2973056 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973057 : term244 = term86.
Proof. exact (EQ_MP (@lem2973056) (@lem940073)). Qed.
Lemma lem2973058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973059 : term242 = term169.
Proof. exact (MK_COMB (@lem2973058) (@lem2973057)). Qed.
Lemma lem2973060 : term241 = term169.
Proof. exact (TRANS (@lem2973055) (@lem2973059)). Qed.
Lemma lem2973061 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2973062 : term375 = term373.
Proof. exact (MK_COMB (@lem2973061) (@lem2973060)). Qed.
Lemma lem2973064 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973065 : term373 = term140.
Proof. exact (@lem2973064 term86). Qed.
Lemma lem2973066 : term375 = term140.
Proof. exact (TRANS (@lem2973062) (@lem2973065)). Qed.
Lemma lem2973067 : term140 = term375.
Proof. exact (SYM (@lem2973066)). Qed.
Lemma lem2973068 : term522 = term375.
Proof. exact (TRANS (@lem2973052) (@lem2973067)). Qed.
Lemma lem2973069 : term513 = term229.
Proof. exact (@lem2973019 (@lem2973068)). Qed.
Lemma lem2973070 : term512 = term229.
Proof. exact (TRANS (@lem2972985) (@lem2973069)). Qed.
Lemma lem2973072 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2973073 : term229 = term140.
Proof. exact (@lem2973072 term140). Qed.
Lemma lem2973074 : term512 = term140.
Proof. exact (TRANS (@lem2973070) (@lem2973073)). Qed.
Lemma lem2973075 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973076 : term523 = term371.
Proof. exact (MK_COMB (@lem2973075) (@lem2973074)). Qed.
Lemma lem2973077 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2973078 (_31794 : int) : (term509 _31794) = (term524 _31794).
Proof. exact (MK_COMB (@lem2973076) (@lem2973077 _31794)). Qed.
Lemma lem2973079 (_31794 : int) : (term508 _31794) = (term524 _31794).
Proof. exact (TRANS (@lem2972976 _31794) (@lem2973078 _31794)). Qed.
Lemma lem2973080 (_31794 : int) : (term524 _31794) = term140.
Proof. exact (@lem1982719 (real_of_int _31794)). Qed.
Lemma lem2973081 (_31794 : int) : (term508 _31794) = term140.
Proof. exact (TRANS (@lem2973079 _31794) (@lem2973080 _31794)). Qed.
Lemma lem2973082 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973083 (_31794 : int) : (term525 _31794) = term526.
Proof. exact (MK_COMB (@lem2973082) (@lem2973081 _31794)). Qed.
Lemma lem2973084 (_31795 : int) (_31796 : int) : (term527 _31796 _31795) = (term528 _31795 _31796).
Proof. exact (@lem1982753 (term276 _31795) (term157 _31795) (term257 _31796) term232). Qed.
Lemma lem2973085 (_31795 : int) : (term529 _31795) = (term530 _31795).
Proof. exact (@lem1982711 term270 term154 (real_of_int _31795)). Qed.
Lemma lem2973087 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973088 : term154 = term260.
Proof. exact (@lem2973087 term2). Qed.
Lemma lem2973090 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973091 : term270 = term273.
Proof. exact (@lem2973090 term2). Qed.
Lemma lem2973092 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973093 : term531 = term532.
Proof. exact (MK_COMB (@lem2973092) (@lem2973091)). Qed.
Lemma lem2973094 : term533 = term534.
Proof. exact (MK_COMB (@lem2973093) (@lem2973088)). Qed.
Lemma lem2973095 : term535.
Proof. exact (@lem1981473 term270 term169 term154 term169 term140 term169). Qed.
Lemma lem2973097 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973098 : term305 = term306.
Proof. exact (@lem2973097 (NUMERAL 0) term86). Qed.
Lemma lem2973099 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973100 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973101 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973100 h1) (fun h1 : term306 = True => @lem2973099)). Qed.
Lemma lem2973102 : term306 = True.
Proof. exact (EQ_MP (@lem2973101) (@lem2973099)). Qed.
Lemma lem2973103 : term305 = True.
Proof. exact (TRANS (@lem2973098) (@lem2973102)). Qed.
Lemma lem2973104 : True = term305.
Proof. exact (SYM (@lem2973103)). Qed.
Lemma lem2973105 : term305.
Proof. exact (EQ_MP (@lem2973104) (@lem0)). Qed.
Lemma lem2973106 : term536.
Proof. exact (@lem2973095 (@lem2973105)). Qed.
Lemma lem2973108 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973109 : term305 = term306.
Proof. exact (@lem2973108 (NUMERAL 0) term86). Qed.
Lemma lem2973110 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973111 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973112 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973111 h1) (fun h1 : term306 = True => @lem2973110)). Qed.
Lemma lem2973113 : term306 = True.
Proof. exact (EQ_MP (@lem2973112) (@lem2973110)). Qed.
Lemma lem2973114 : term305 = True.
Proof. exact (TRANS (@lem2973109) (@lem2973113)). Qed.
Lemma lem2973115 : True = term305.
Proof. exact (SYM (@lem2973114)). Qed.
Lemma lem2973116 : term305.
Proof. exact (EQ_MP (@lem2973115) (@lem0)). Qed.
Lemma lem2973117 : term537.
Proof. exact (@lem2973106 (@lem2973116)). Qed.
Lemma lem2973119 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973120 : term305 = term306.
Proof. exact (@lem2973119 (NUMERAL 0) term86). Qed.
Lemma lem2973121 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973122 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973123 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973122 h1) (fun h1 : term306 = True => @lem2973121)). Qed.
Lemma lem2973124 : term306 = True.
Proof. exact (EQ_MP (@lem2973123) (@lem2973121)). Qed.
Lemma lem2973125 : term305 = True.
Proof. exact (TRANS (@lem2973120) (@lem2973124)). Qed.
Lemma lem2973126 : True = term305.
Proof. exact (SYM (@lem2973125)). Qed.
Lemma lem2973127 : term305.
Proof. exact (EQ_MP (@lem2973126) (@lem0)). Qed.
Lemma lem2973128 : term538.
Proof. exact (@lem2973117 (@lem2973127)). Qed.
Lemma lem2973130 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973131 : term311 = term312.
Proof. exact (@lem2973130 term2 term86). Qed.
Lemma lem2973132 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2973133 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2973134 : term314 = term2.
Proof. exact (EQ_MP (@lem2973133) (@lem2973132)). Qed.
Lemma lem2973135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973136 : term312 = term154.
Proof. exact (MK_COMB (@lem2973135) (@lem2973134)). Qed.
Lemma lem2973137 : term311 = term154.
Proof. exact (TRANS (@lem2973131) (@lem2973136)). Qed.
Lemma lem2973139 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973140 : term539 = term540.
Proof. exact (@lem2973139 term2 term86). Qed.
Lemma lem2973141 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2973142 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2973143 : term314 = term2.
Proof. exact (EQ_MP (@lem2973142) (@lem2973141)). Qed.
Lemma lem2973144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973145 : term312 = term154.
Proof. exact (MK_COMB (@lem2973144) (@lem2973143)). Qed.
Lemma lem2973146 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973147 : term540 = term270.
Proof. exact (MK_COMB (@lem2973146) (@lem2973145)). Qed.
Lemma lem2973148 : term539 = term270.
Proof. exact (TRANS (@lem2973140) (@lem2973147)). Qed.
Lemma lem2973149 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973150 : term541 = term531.
Proof. exact (MK_COMB (@lem2973149) (@lem2973148)). Qed.
Lemma lem2973151 : term542 = term533.
Proof. exact (MK_COMB (@lem2973150) (@lem2973137)). Qed.
Lemma lem2973153 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2973154 : term533 = term140.
Proof. exact (@lem2973153 term2). Qed.
Lemma lem2973155 : term542 = term140.
Proof. exact (TRANS (@lem2973151) (@lem2973154)). Qed.
Lemma lem2973156 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973157 : term543 = term371.
Proof. exact (MK_COMB (@lem2973156) (@lem2973155)). Qed.
Lemma lem2973158 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2973159 : term544 = term373.
Proof. exact (MK_COMB (@lem2973157) (@lem2973158)). Qed.
Lemma lem2973161 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973162 : term373 = term140.
Proof. exact (@lem2973161 term86). Qed.
Lemma lem2973163 : term544 = term140.
Proof. exact (TRANS (@lem2973159) (@lem2973162)). Qed.
Lemma lem2973165 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973166 : term241 = term242.
Proof. exact (@lem2973165 term86 term86). Qed.
Lemma lem2973167 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973168 : term244 = term86.
Proof. exact (EQ_MP (@lem2973167) (@lem940073)). Qed.
Lemma lem2973169 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973170 : term242 = term169.
Proof. exact (MK_COMB (@lem2973169) (@lem2973168)). Qed.
Lemma lem2973171 : term241 = term169.
Proof. exact (TRANS (@lem2973166) (@lem2973170)). Qed.
Lemma lem2973172 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2973173 : term375 = term373.
Proof. exact (MK_COMB (@lem2973172) (@lem2973171)). Qed.
Lemma lem2973175 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973176 : term373 = term140.
Proof. exact (@lem2973175 term86). Qed.
Lemma lem2973177 : term375 = term140.
Proof. exact (TRANS (@lem2973173) (@lem2973176)). Qed.
Lemma lem2973178 : term140 = term375.
Proof. exact (SYM (@lem2973177)). Qed.
Lemma lem2973179 : term544 = term375.
Proof. exact (TRANS (@lem2973163) (@lem2973178)). Qed.
Lemma lem2973180 : term534 = term229.
Proof. exact (@lem2973128 (@lem2973179)). Qed.
Lemma lem2973181 : term533 = term229.
Proof. exact (TRANS (@lem2973094) (@lem2973180)). Qed.
Lemma lem2973183 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2973184 : term229 = term140.
Proof. exact (@lem2973183 term140). Qed.
Lemma lem2973185 : term533 = term140.
Proof. exact (TRANS (@lem2973181) (@lem2973184)). Qed.
Lemma lem2973186 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973187 : term545 = term371.
Proof. exact (MK_COMB (@lem2973186) (@lem2973185)). Qed.
Lemma lem2973188 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2973189 (_31795 : int) : (term530 _31795) = (term524 _31795).
Proof. exact (MK_COMB (@lem2973187) (@lem2973188 _31795)). Qed.
Lemma lem2973190 (_31795 : int) : (term529 _31795) = (term524 _31795).
Proof. exact (TRANS (@lem2973085 _31795) (@lem2973189 _31795)). Qed.
Lemma lem2973191 (_31795 : int) : (term524 _31795) = term140.
Proof. exact (@lem1982719 (real_of_int _31795)). Qed.
Lemma lem2973192 (_31795 : int) : (term529 _31795) = term140.
Proof. exact (TRANS (@lem2973190 _31795) (@lem2973191 _31795)). Qed.
Lemma lem2973193 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973194 (_31795 : int) : (term546 _31795) = term526.
Proof. exact (MK_COMB (@lem2973193) (@lem2973192 _31795)). Qed.
Lemma lem2973195 (_31796 : int) : (term296 _31796) = (term296 _31796).
Proof. exact (eq_refl (term296 _31796)). Qed.
Lemma lem2973196 (_31795 : int) (_31796 : int) : (term528 _31795 _31796) = (term547 _31796).
Proof. exact (MK_COMB (@lem2973194 _31795) (@lem2973195 _31796)). Qed.
Lemma lem2973197 (_31795 : int) (_31796 : int) : (term527 _31796 _31795) = (term547 _31796).
Proof. exact (TRANS (@lem2973084 _31795 _31796) (@lem2973196 _31795 _31796)). Qed.
Lemma lem2973198 (_31796 : int) : (term547 _31796) = (term296 _31796).
Proof. exact (@lem1982721 (term296 _31796)). Qed.
Lemma lem2973199 (_31795 : int) (_31796 : int) : (term527 _31796 _31795) = (term296 _31796).
Proof. exact (TRANS (@lem2973197 _31795 _31796) (@lem2973198 _31796)). Qed.
Lemma lem2973200 (_31794 : int) (_31795 : int) (_31796 : int) : (term506 _31794 _31796 _31795) = (term547 _31796).
Proof. exact (MK_COMB (@lem2973083 _31794) (@lem2973199 _31795 _31796)). Qed.
Lemma lem2973201 (_31794 : int) (_31795 : int) (_31796 : int) : (term505 _31796 _31794 _31795) = (term547 _31796).
Proof. exact (TRANS (@lem2972975 _31794 _31796 _31795) (@lem2973200 _31794 _31795 _31796)). Qed.
Lemma lem2973202 (_31796 : int) : (term547 _31796) = (term296 _31796).
Proof. exact (@lem1982721 (term296 _31796)). Qed.
Lemma lem2973203 (_31794 : int) (_31795 : int) (_31796 : int) : (term505 _31796 _31794 _31795) = (term296 _31796).
Proof. exact (TRANS (@lem2973201 _31794 _31795 _31796) (@lem2973202 _31796)). Qed.
Lemma lem2973204 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2973205 (_31794 : int) (_31795 : int) (_31796 : int) : (term548 _31796 _31794 _31795) = (term549 _31796).
Proof. exact (MK_COMB (@lem2973204) (@lem2973203 _31794 _31795 _31796)). Qed.
Lemma lem2973206 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2973207 (_31794 : int) (_31795 : int) (_31796 : int) : (term504 _31796 _31794 _31795) = (term550 _31796).
Proof. exact (MK_COMB (@lem2973205 _31794 _31795 _31796) (@lem2973206)). Qed.
Lemma lem2973208 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term550 _31796.
Proof. exact (EQ_MP (@lem2973207 _31794 _31795 _31796) (@lem2972974 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973210 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2973211 : term476 = term305.
Proof. exact (@lem2973210 term140 term169). Qed.
Lemma lem2973213 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973214 : term169 = term288.
Proof. exact (@lem2973213 term86). Qed.
Lemma lem2973216 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973217 : term140 = term229.
Proof. exact (@lem2973216 (NUMERAL 0)). Qed.
Lemma lem2973218 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2973219 : term477 = term478.
Proof. exact (MK_COMB (@lem2973218) (@lem2973217)). Qed.
Lemma lem2973220 : term305 = term479.
Proof. exact (MK_COMB (@lem2973219) (@lem2973214)). Qed.
Lemma lem2973221 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2973223 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973224 : term305 = term306.
Proof. exact (@lem2973223 (NUMERAL 0) term86). Qed.
Lemma lem2973225 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973226 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973227 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973226 h1) (fun h1 : term306 = True => @lem2973225)). Qed.
Lemma lem2973228 : term306 = True.
Proof. exact (EQ_MP (@lem2973227) (@lem2973225)). Qed.
Lemma lem2973229 : term305 = True.
Proof. exact (TRANS (@lem2973224) (@lem2973228)). Qed.
Lemma lem2973230 : True = term305.
Proof. exact (SYM (@lem2973229)). Qed.
Lemma lem2973231 : term305.
Proof. exact (EQ_MP (@lem2973230) (@lem0)). Qed.
Lemma lem2973232 : term481.
Proof. exact (@lem2973221 (@lem2973231)). Qed.
Lemma lem2973234 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973235 : term305 = term306.
Proof. exact (@lem2973234 (NUMERAL 0) term86). Qed.
Lemma lem2973236 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973237 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973238 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973237 h1) (fun h1 : term306 = True => @lem2973236)). Qed.
Lemma lem2973239 : term306 = True.
Proof. exact (EQ_MP (@lem2973238) (@lem2973236)). Qed.
Lemma lem2973240 : term305 = True.
Proof. exact (TRANS (@lem2973235) (@lem2973239)). Qed.
Lemma lem2973241 : True = term305.
Proof. exact (SYM (@lem2973240)). Qed.
Lemma lem2973242 : term305.
Proof. exact (EQ_MP (@lem2973241) (@lem0)). Qed.
Lemma lem2973243 : term479 = term482.
Proof. exact (@lem2973232 (@lem2973242)). Qed.
Lemma lem2973245 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973246 : term241 = term242.
Proof. exact (@lem2973245 term86 term86). Qed.
Lemma lem2973247 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973248 : term244 = term86.
Proof. exact (EQ_MP (@lem2973247) (@lem940073)). Qed.
Lemma lem2973249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973250 : term242 = term169.
Proof. exact (MK_COMB (@lem2973249) (@lem2973248)). Qed.
Lemma lem2973251 : term241 = term169.
Proof. exact (TRANS (@lem2973246) (@lem2973250)). Qed.
Lemma lem2973253 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973254 : term373 = term140.
Proof. exact (@lem2973253 term86). Qed.
Lemma lem2973255 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2973256 : term483 = term477.
Proof. exact (MK_COMB (@lem2973255) (@lem2973254)). Qed.
Lemma lem2973257 : term482 = term305.
Proof. exact (MK_COMB (@lem2973256) (@lem2973251)). Qed.
Lemma lem2973259 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973260 : term305 = term306.
Proof. exact (@lem2973259 (NUMERAL 0) term86). Qed.
Lemma lem2973261 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973262 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973263 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973262 h1) (fun h1 : term306 = True => @lem2973261)). Qed.
Lemma lem2973264 : term306 = True.
Proof. exact (EQ_MP (@lem2973263) (@lem2973261)). Qed.
Lemma lem2973265 : term305 = True.
Proof. exact (TRANS (@lem2973260) (@lem2973264)). Qed.
Lemma lem2973266 : term482 = True.
Proof. exact (TRANS (@lem2973257) (@lem2973265)). Qed.
Lemma lem2973267 : term479 = True.
Proof. exact (TRANS (@lem2973243) (@lem2973266)). Qed.
Lemma lem2973268 : term305 = True.
Proof. exact (TRANS (@lem2973220) (@lem2973267)). Qed.
Lemma lem2973269 : term476 = True.
Proof. exact (TRANS (@lem2973211) (@lem2973268)). Qed.
Lemma lem2973270 : True = term476.
Proof. exact (SYM (@lem2973269)). Qed.
Lemma lem2973271 : term476.
Proof. exact (EQ_MP (@lem2973270) (@lem0)). Qed.
Lemma lem2973272 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term551 _31796.
Proof. exact (conj (@lem2973271) (@lem2973208 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973274 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2973275 (_31796 : int) : term552 _31796.
Proof. exact (@lem2973274 term169 (term296 _31796)). Qed.
Lemma lem2973276 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term553 _31796.
Proof. exact (@lem2973275 _31796 (@lem2973272 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973277 (_31796 : int) : (term554 _31796) = (term296 _31796).
Proof. exact (@lem1982733 (term296 _31796)). Qed.
Lemma lem2973278 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2973279 (_31796 : int) : (term555 _31796) = (term549 _31796).
Proof. exact (MK_COMB (@lem2973278) (@lem2973277 _31796)). Qed.
Lemma lem2973280 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2973281 (_31796 : int) : (term553 _31796) = (term550 _31796).
Proof. exact (MK_COMB (@lem2973279 _31796) (@lem2973280)). Qed.
Lemma lem2973282 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term550 _31796.
Proof. exact (EQ_MP (@lem2973281 _31796) (@lem2973276 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973283 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term690 _31796.
Proof. exact (conj (@lem2973282 _31796 _31794 _31795 h1) (@lem2972882 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973285 (x : real) (y : real) : term557 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2973286 (_31796 : int) : term691 _31796.
Proof. exact (@lem2973285 (term296 _31796) (term680 _31796)). Qed.
Lemma lem2973287 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term692 _31796.
Proof. exact (@lem2973286 _31796 (@lem2973283 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973288 (_31796 : int) : (term693 _31796) = (term694 _31796).
Proof. exact (@lem1982753 (term257 _31796) (real_of_int _31796) term232 term270). Qed.
Lemma lem2973289 (_31796 : int) : (term562 _31796) = (term509 _31796).
Proof. exact (@lem1982713 term232 (real_of_int _31796)). Qed.
Lemma lem2973291 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973292 : term169 = term288.
Proof. exact (@lem2973291 term86). Qed.
Lemma lem2973294 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973295 : term232 = term233.
Proof. exact (@lem2973294 term86). Qed.
Lemma lem2973296 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973297 : term510 = term511.
Proof. exact (MK_COMB (@lem2973296) (@lem2973295)). Qed.
Lemma lem2973298 : term512 = term513.
Proof. exact (MK_COMB (@lem2973297) (@lem2973292)). Qed.
Lemma lem2973299 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2973301 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973302 : term305 = term306.
Proof. exact (@lem2973301 (NUMERAL 0) term86). Qed.
Lemma lem2973303 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973304 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973305 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973304 h1) (fun h1 : term306 = True => @lem2973303)). Qed.
Lemma lem2973306 : term306 = True.
Proof. exact (EQ_MP (@lem2973305) (@lem2973303)). Qed.
Lemma lem2973307 : term305 = True.
Proof. exact (TRANS (@lem2973302) (@lem2973306)). Qed.
Lemma lem2973308 : True = term305.
Proof. exact (SYM (@lem2973307)). Qed.
Lemma lem2973309 : term305.
Proof. exact (EQ_MP (@lem2973308) (@lem0)). Qed.
Lemma lem2973310 : term515.
Proof. exact (@lem2973299 (@lem2973309)). Qed.
Lemma lem2973312 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973313 : term305 = term306.
Proof. exact (@lem2973312 (NUMERAL 0) term86). Qed.
Lemma lem2973314 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973315 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973316 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973315 h1) (fun h1 : term306 = True => @lem2973314)). Qed.
Lemma lem2973317 : term306 = True.
Proof. exact (EQ_MP (@lem2973316) (@lem2973314)). Qed.
Lemma lem2973318 : term305 = True.
Proof. exact (TRANS (@lem2973313) (@lem2973317)). Qed.
Lemma lem2973319 : True = term305.
Proof. exact (SYM (@lem2973318)). Qed.
Lemma lem2973320 : term305.
Proof. exact (EQ_MP (@lem2973319) (@lem0)). Qed.
Lemma lem2973321 : term516.
Proof. exact (@lem2973310 (@lem2973320)). Qed.
Lemma lem2973323 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973324 : term305 = term306.
Proof. exact (@lem2973323 (NUMERAL 0) term86). Qed.
Lemma lem2973325 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973326 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973327 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973326 h1) (fun h1 : term306 = True => @lem2973325)). Qed.
Lemma lem2973328 : term306 = True.
Proof. exact (EQ_MP (@lem2973327) (@lem2973325)). Qed.
Lemma lem2973329 : term305 = True.
Proof. exact (TRANS (@lem2973324) (@lem2973328)). Qed.
Lemma lem2973330 : True = term305.
Proof. exact (SYM (@lem2973329)). Qed.
Lemma lem2973331 : term305.
Proof. exact (EQ_MP (@lem2973330) (@lem0)). Qed.
Lemma lem2973332 : term517.
Proof. exact (@lem2973321 (@lem2973331)). Qed.
Lemma lem2973334 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973335 : term241 = term242.
Proof. exact (@lem2973334 term86 term86). Qed.
Lemma lem2973336 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973337 : term244 = term86.
Proof. exact (EQ_MP (@lem2973336) (@lem940073)). Qed.
Lemma lem2973338 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973339 : term242 = term169.
Proof. exact (MK_COMB (@lem2973338) (@lem2973337)). Qed.
Lemma lem2973340 : term241 = term169.
Proof. exact (TRANS (@lem2973335) (@lem2973339)). Qed.
Lemma lem2973342 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973343 : term289 = term292.
Proof. exact (@lem2973342 term86 term86). Qed.
Lemma lem2973344 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973345 : term244 = term86.
Proof. exact (EQ_MP (@lem2973344) (@lem940073)). Qed.
Lemma lem2973346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973347 : term242 = term169.
Proof. exact (MK_COMB (@lem2973346) (@lem2973345)). Qed.
Lemma lem2973348 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973349 : term292 = term232.
Proof. exact (MK_COMB (@lem2973348) (@lem2973347)). Qed.
Lemma lem2973350 : term289 = term232.
Proof. exact (TRANS (@lem2973343) (@lem2973349)). Qed.
Lemma lem2973351 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973352 : term518 = term510.
Proof. exact (MK_COMB (@lem2973351) (@lem2973350)). Qed.
Lemma lem2973353 : term519 = term512.
Proof. exact (MK_COMB (@lem2973352) (@lem2973340)). Qed.
Lemma lem2973355 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2973356 : term512 = term140.
Proof. exact (@lem2973355 term86). Qed.
Lemma lem2973357 : term519 = term140.
Proof. exact (TRANS (@lem2973353) (@lem2973356)). Qed.
Lemma lem2973358 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973359 : term521 = term371.
Proof. exact (MK_COMB (@lem2973358) (@lem2973357)). Qed.
Lemma lem2973360 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2973361 : term522 = term373.
Proof. exact (MK_COMB (@lem2973359) (@lem2973360)). Qed.
Lemma lem2973363 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973364 : term373 = term140.
Proof. exact (@lem2973363 term86). Qed.
Lemma lem2973365 : term522 = term140.
Proof. exact (TRANS (@lem2973361) (@lem2973364)). Qed.
Lemma lem2973367 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973368 : term241 = term242.
Proof. exact (@lem2973367 term86 term86). Qed.
Lemma lem2973369 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973370 : term244 = term86.
Proof. exact (EQ_MP (@lem2973369) (@lem940073)). Qed.
Lemma lem2973371 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973372 : term242 = term169.
Proof. exact (MK_COMB (@lem2973371) (@lem2973370)). Qed.
Lemma lem2973373 : term241 = term169.
Proof. exact (TRANS (@lem2973368) (@lem2973372)). Qed.
Lemma lem2973374 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2973375 : term375 = term373.
Proof. exact (MK_COMB (@lem2973374) (@lem2973373)). Qed.
Lemma lem2973377 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973378 : term373 = term140.
Proof. exact (@lem2973377 term86). Qed.
Lemma lem2973379 : term375 = term140.
Proof. exact (TRANS (@lem2973375) (@lem2973378)). Qed.
Lemma lem2973380 : term140 = term375.
Proof. exact (SYM (@lem2973379)). Qed.
Lemma lem2973381 : term522 = term375.
Proof. exact (TRANS (@lem2973365) (@lem2973380)). Qed.
Lemma lem2973382 : term513 = term229.
Proof. exact (@lem2973332 (@lem2973381)). Qed.
Lemma lem2973383 : term512 = term229.
Proof. exact (TRANS (@lem2973298) (@lem2973382)). Qed.
Lemma lem2973385 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2973386 : term229 = term140.
Proof. exact (@lem2973385 term140). Qed.
Lemma lem2973387 : term512 = term140.
Proof. exact (TRANS (@lem2973383) (@lem2973386)). Qed.
Lemma lem2973388 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973389 : term523 = term371.
Proof. exact (MK_COMB (@lem2973388) (@lem2973387)). Qed.
Lemma lem2973390 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2973391 (_31796 : int) : (term509 _31796) = (term524 _31796).
Proof. exact (MK_COMB (@lem2973389) (@lem2973390 _31796)). Qed.
Lemma lem2973392 (_31796 : int) : (term562 _31796) = (term524 _31796).
Proof. exact (TRANS (@lem2973289 _31796) (@lem2973391 _31796)). Qed.
Lemma lem2973393 (_31796 : int) : (term524 _31796) = term140.
Proof. exact (@lem1982719 (real_of_int _31796)). Qed.
Lemma lem2973394 (_31796 : int) : (term562 _31796) = term140.
Proof. exact (TRANS (@lem2973392 _31796) (@lem2973393 _31796)). Qed.
Lemma lem2973395 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973396 (_31796 : int) : (term563 _31796) = term526.
Proof. exact (MK_COMB (@lem2973395) (@lem2973394 _31796)). Qed.
Lemma lem2973398 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973399 : term270 = term273.
Proof. exact (@lem2973398 term2). Qed.
Lemma lem2973401 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973402 : term232 = term233.
Proof. exact (@lem2973401 term86). Qed.
Lemma lem2973403 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973404 : term510 = term511.
Proof. exact (MK_COMB (@lem2973403) (@lem2973402)). Qed.
Lemma lem2973405 : term695 = term696.
Proof. exact (MK_COMB (@lem2973404) (@lem2973399)). Qed.
Lemma lem2973406 : term697.
Proof. exact (@lem1981473 term232 term169 term270 term169 term698 term169). Qed.
Lemma lem2973408 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973409 : term305 = term306.
Proof. exact (@lem2973408 (NUMERAL 0) term86). Qed.
Lemma lem2973410 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973411 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973412 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973411 h1) (fun h1 : term306 = True => @lem2973410)). Qed.
Lemma lem2973413 : term306 = True.
Proof. exact (EQ_MP (@lem2973412) (@lem2973410)). Qed.
Lemma lem2973414 : term305 = True.
Proof. exact (TRANS (@lem2973409) (@lem2973413)). Qed.
Lemma lem2973415 : True = term305.
Proof. exact (SYM (@lem2973414)). Qed.
Lemma lem2973416 : term305.
Proof. exact (EQ_MP (@lem2973415) (@lem0)). Qed.
Lemma lem2973417 : term699.
Proof. exact (@lem2973406 (@lem2973416)). Qed.
Lemma lem2973419 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973420 : term305 = term306.
Proof. exact (@lem2973419 (NUMERAL 0) term86). Qed.
Lemma lem2973421 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973422 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973423 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973422 h1) (fun h1 : term306 = True => @lem2973421)). Qed.
Lemma lem2973424 : term306 = True.
Proof. exact (EQ_MP (@lem2973423) (@lem2973421)). Qed.
Lemma lem2973425 : term305 = True.
Proof. exact (TRANS (@lem2973420) (@lem2973424)). Qed.
Lemma lem2973426 : True = term305.
Proof. exact (SYM (@lem2973425)). Qed.
Lemma lem2973427 : term305.
Proof. exact (EQ_MP (@lem2973426) (@lem0)). Qed.
Lemma lem2973428 : term700.
Proof. exact (@lem2973417 (@lem2973427)). Qed.
Lemma lem2973430 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973431 : term305 = term306.
Proof. exact (@lem2973430 (NUMERAL 0) term86). Qed.
Lemma lem2973432 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973433 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973434 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973433 h1) (fun h1 : term306 = True => @lem2973432)). Qed.
Lemma lem2973435 : term306 = True.
Proof. exact (EQ_MP (@lem2973434) (@lem2973432)). Qed.
Lemma lem2973436 : term305 = True.
Proof. exact (TRANS (@lem2973431) (@lem2973435)). Qed.
Lemma lem2973437 : True = term305.
Proof. exact (SYM (@lem2973436)). Qed.
Lemma lem2973438 : term305.
Proof. exact (EQ_MP (@lem2973437) (@lem0)). Qed.
Lemma lem2973439 : term701.
Proof. exact (@lem2973428 (@lem2973438)). Qed.
Lemma lem2973441 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973442 : term539 = term540.
Proof. exact (@lem2973441 term2 term86). Qed.
Lemma lem2973443 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2973444 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2973445 : term314 = term2.
Proof. exact (EQ_MP (@lem2973444) (@lem2973443)). Qed.
Lemma lem2973446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973447 : term312 = term154.
Proof. exact (MK_COMB (@lem2973446) (@lem2973445)). Qed.
Lemma lem2973448 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973449 : term540 = term270.
Proof. exact (MK_COMB (@lem2973448) (@lem2973447)). Qed.
Lemma lem2973450 : term539 = term270.
Proof. exact (TRANS (@lem2973442) (@lem2973449)). Qed.
Lemma lem2973452 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973453 : term289 = term292.
Proof. exact (@lem2973452 term86 term86). Qed.
Lemma lem2973454 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973455 : term244 = term86.
Proof. exact (EQ_MP (@lem2973454) (@lem940073)). Qed.
Lemma lem2973456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973457 : term242 = term169.
Proof. exact (MK_COMB (@lem2973456) (@lem2973455)). Qed.
Lemma lem2973458 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973459 : term292 = term232.
Proof. exact (MK_COMB (@lem2973458) (@lem2973457)). Qed.
Lemma lem2973460 : term289 = term232.
Proof. exact (TRANS (@lem2973453) (@lem2973459)). Qed.
Lemma lem2973461 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973462 : term518 = term510.
Proof. exact (MK_COMB (@lem2973461) (@lem2973460)). Qed.
Lemma lem2973463 : term702 = term695.
Proof. exact (MK_COMB (@lem2973462) (@lem2973450)). Qed.
Lemma lem2973464 : term695 = term703.
Proof. exact (@lem1367763 term86 term2). Qed.
Lemma lem2973465 : term704 = term705.
Proof. exact (@lem706887). Qed.
Lemma lem2973466 : (term704 = term705) = (term706 = term707).
Proof. exact (@lem1006570 (BIT1 0) term27 term705). Qed.
Lemma lem2973467 : term706 = term707.
Proof. exact (EQ_MP (@lem2973466) (@lem2973465)). Qed.
Lemma lem2973468 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973469 : term708 = term709.
Proof. exact (MK_COMB (@lem2973468) (@lem2973467)). Qed.
Lemma lem2973470 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973471 : term703 = term698.
Proof. exact (MK_COMB (@lem2973470) (@lem2973469)). Qed.
Lemma lem2973472 : term695 = term698.
Proof. exact (TRANS (@lem2973464) (@lem2973471)). Qed.
Lemma lem2973473 : term702 = term698.
Proof. exact (TRANS (@lem2973463) (@lem2973472)). Qed.
Lemma lem2973474 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973475 : term710 = term711.
Proof. exact (MK_COMB (@lem2973474) (@lem2973473)). Qed.
Lemma lem2973476 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2973477 : term712 = term713.
Proof. exact (MK_COMB (@lem2973475) (@lem2973476)). Qed.
Lemma lem2973479 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973480 : term713 = term714.
Proof. exact (@lem2973479 term707 term86). Qed.
Lemma lem2973481 : term715 = term705.
Proof. exact (@lem996237 term705). Qed.
Lemma lem2973482 : (term715 = term705) = (term716 = term707).
Proof. exact (@lem1007663 term705 (BIT1 0) term705). Qed.
Lemma lem2973483 : term716 = term707.
Proof. exact (EQ_MP (@lem2973482) (@lem2973481)). Qed.
Lemma lem2973484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973485 : term717 = term709.
Proof. exact (MK_COMB (@lem2973484) (@lem2973483)). Qed.
Lemma lem2973486 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973487 : term714 = term698.
Proof. exact (MK_COMB (@lem2973486) (@lem2973485)). Qed.
Lemma lem2973488 : term713 = term698.
Proof. exact (TRANS (@lem2973480) (@lem2973487)). Qed.
Lemma lem2973489 : term712 = term698.
Proof. exact (TRANS (@lem2973477) (@lem2973488)). Qed.
Lemma lem2973491 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973492 : term241 = term242.
Proof. exact (@lem2973491 term86 term86). Qed.
Lemma lem2973493 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973494 : term244 = term86.
Proof. exact (EQ_MP (@lem2973493) (@lem940073)). Qed.
Lemma lem2973495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973496 : term242 = term169.
Proof. exact (MK_COMB (@lem2973495) (@lem2973494)). Qed.
Lemma lem2973497 : term241 = term169.
Proof. exact (TRANS (@lem2973492) (@lem2973496)). Qed.
Lemma lem2973498 : term711 = term711.
Proof. exact (eq_refl term711). Qed.
Lemma lem2973499 : term718 = term713.
Proof. exact (MK_COMB (@lem2973498) (@lem2973497)). Qed.
Lemma lem2973501 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973502 : term713 = term714.
Proof. exact (@lem2973501 term707 term86). Qed.
Lemma lem2973503 : term715 = term705.
Proof. exact (@lem996237 term705). Qed.
Lemma lem2973504 : (term715 = term705) = (term716 = term707).
Proof. exact (@lem1007663 term705 (BIT1 0) term705). Qed.
Lemma lem2973505 : term716 = term707.
Proof. exact (EQ_MP (@lem2973504) (@lem2973503)). Qed.
Lemma lem2973506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973507 : term717 = term709.
Proof. exact (MK_COMB (@lem2973506) (@lem2973505)). Qed.
Lemma lem2973508 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973509 : term714 = term698.
Proof. exact (MK_COMB (@lem2973508) (@lem2973507)). Qed.
Lemma lem2973510 : term713 = term698.
Proof. exact (TRANS (@lem2973502) (@lem2973509)). Qed.
Lemma lem2973511 : term718 = term698.
Proof. exact (TRANS (@lem2973499) (@lem2973510)). Qed.
Lemma lem2973512 : term698 = term718.
Proof. exact (SYM (@lem2973511)). Qed.
Lemma lem2973513 : term712 = term718.
Proof. exact (TRANS (@lem2973489) (@lem2973512)). Qed.
Lemma lem2973514 : term696 = term719.
Proof. exact (@lem2973439 (@lem2973513)). Qed.
Lemma lem2973515 : term695 = term719.
Proof. exact (TRANS (@lem2973405) (@lem2973514)). Qed.
Lemma lem2973517 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2973518 : term719 = term698.
Proof. exact (@lem2973517 term698). Qed.
Lemma lem2973519 : term695 = term698.
Proof. exact (TRANS (@lem2973515) (@lem2973518)). Qed.
Lemma lem2973520 (_31796 : int) : (term694 _31796) = term720.
Proof. exact (MK_COMB (@lem2973396 _31796) (@lem2973519)). Qed.
Lemma lem2973521 (_31796 : int) : (term693 _31796) = term720.
Proof. exact (TRANS (@lem2973288 _31796) (@lem2973520 _31796)). Qed.
Lemma lem2973522 : term720 = term698.
Proof. exact (@lem1982721 term698). Qed.
Lemma lem2973523 (_31796 : int) : (term693 _31796) = term698.
Proof. exact (TRANS (@lem2973521 _31796) (@lem2973522)). Qed.
Lemma lem2973524 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2973525 (_31796 : int) : (term721 _31796) = term722.
Proof. exact (MK_COMB (@lem2973524) (@lem2973523 _31796)). Qed.
Lemma lem2973526 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2973527 (_31796 : int) : (term692 _31796) = term723.
Proof. exact (MK_COMB (@lem2973525 _31796) (@lem2973526)). Qed.
Lemma lem2973528 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : term723.
Proof. exact (EQ_MP (@lem2973527 _31796) (@lem2973287 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973530 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2973531 : term723 = term724.
Proof. exact (@lem2973530 term140 term698). Qed.
Lemma lem2973533 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973534 : term698 = term719.
Proof. exact (@lem2973533 term707). Qed.
Lemma lem2973536 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973537 : term140 = term229.
Proof. exact (@lem2973536 (NUMERAL 0)). Qed.
Lemma lem2973538 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2973539 : term142 = term569.
Proof. exact (MK_COMB (@lem2973538) (@lem2973537)). Qed.
Lemma lem2973540 : term724 = term725.
Proof. exact (MK_COMB (@lem2973539) (@lem2973534)). Qed.
Lemma lem2973541 : term726.
Proof. exact (@lem1980026 term140 term169 term698 term169). Qed.
Lemma lem2973543 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973544 : term305 = term306.
Proof. exact (@lem2973543 (NUMERAL 0) term86). Qed.
Lemma lem2973545 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973546 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973547 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973546 h1) (fun h1 : term306 = True => @lem2973545)). Qed.
Lemma lem2973548 : term306 = True.
Proof. exact (EQ_MP (@lem2973547) (@lem2973545)). Qed.
Lemma lem2973549 : term305 = True.
Proof. exact (TRANS (@lem2973544) (@lem2973548)). Qed.
Lemma lem2973550 : True = term305.
Proof. exact (SYM (@lem2973549)). Qed.
Lemma lem2973551 : term305.
Proof. exact (EQ_MP (@lem2973550) (@lem0)). Qed.
Lemma lem2973552 : term727.
Proof. exact (@lem2973541 (@lem2973551)). Qed.
Lemma lem2973554 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973555 : term305 = term306.
Proof. exact (@lem2973554 (NUMERAL 0) term86). Qed.
Lemma lem2973556 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973557 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973558 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973557 h1) (fun h1 : term306 = True => @lem2973556)). Qed.
Lemma lem2973559 : term306 = True.
Proof. exact (EQ_MP (@lem2973558) (@lem2973556)). Qed.
Lemma lem2973560 : term305 = True.
Proof. exact (TRANS (@lem2973555) (@lem2973559)). Qed.
Lemma lem2973561 : True = term305.
Proof. exact (SYM (@lem2973560)). Qed.
Lemma lem2973562 : term305.
Proof. exact (EQ_MP (@lem2973561) (@lem0)). Qed.
Lemma lem2973563 : term725 = term728.
Proof. exact (@lem2973552 (@lem2973562)). Qed.
Lemma lem2973565 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973566 : term713 = term714.
Proof. exact (@lem2973565 term707 term86). Qed.
Lemma lem2973567 : term715 = term705.
Proof. exact (@lem996237 term705). Qed.
Lemma lem2973568 : (term715 = term705) = (term716 = term707).
Proof. exact (@lem1007663 term705 (BIT1 0) term705). Qed.
Lemma lem2973569 : term716 = term707.
Proof. exact (EQ_MP (@lem2973568) (@lem2973567)). Qed.
Lemma lem2973570 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973571 : term717 = term709.
Proof. exact (MK_COMB (@lem2973570) (@lem2973569)). Qed.
Lemma lem2973572 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973573 : term714 = term698.
Proof. exact (MK_COMB (@lem2973572) (@lem2973571)). Qed.
Lemma lem2973574 : term713 = term698.
Proof. exact (TRANS (@lem2973566) (@lem2973573)). Qed.
Lemma lem2973576 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973577 : term373 = term140.
Proof. exact (@lem2973576 term86). Qed.
Lemma lem2973578 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2973579 : term574 = term142.
Proof. exact (MK_COMB (@lem2973578) (@lem2973577)). Qed.
Lemma lem2973580 : term728 = term724.
Proof. exact (MK_COMB (@lem2973579) (@lem2973574)). Qed.
Lemma lem2973582 (m : nat) (n : nat) : (term575 m n) = (term576 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2973583 : term724 = term729.
Proof. exact (@lem2973582 (NUMERAL 0) term707). Qed.
Lemma lem2973584 : term730 = term705.
Proof. exact (@lem912867). Qed.
Lemma lem2973585 (h1 : term730 = term705) : (term707 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 term27 0 term705 h1). Qed.
Lemma lem2973586 : (term730 = term705) = ((term707 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term730 = term705 => @lem2973585 h1) (fun h1 : (term707 = (NUMERAL 0)) = False => @lem2973584)). Qed.
Lemma lem2973587 : (term707 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2973586) (@lem2973584)). Qed.
Lemma lem2973588 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2973589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2973590 : term578 = (and True).
Proof. exact (MK_COMB (@lem2973589) (@lem2973588)). Qed.
Lemma lem2973591 : term729 = (True /\ False).
Proof. exact (MK_COMB (@lem2973590) (@lem2973587)). Qed.
Lemma lem2973593 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2973594 : term729 = False.
Proof. exact (TRANS (@lem2973591) (@lem2973593)). Qed.
Lemma lem2973595 : term724 = False.
Proof. exact (TRANS (@lem2973583) (@lem2973594)). Qed.
Lemma lem2973596 : term728 = False.
Proof. exact (TRANS (@lem2973580) (@lem2973595)). Qed.
Lemma lem2973597 : term725 = False.
Proof. exact (TRANS (@lem2973563) (@lem2973596)). Qed.
Lemma lem2973598 : term724 = False.
Proof. exact (TRANS (@lem2973540) (@lem2973597)). Qed.
Lemma lem2973599 : term723 = False.
Proof. exact (TRANS (@lem2973531) (@lem2973598)). Qed.
Lemma lem2973600 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term667 _31796 _31794 _31795) : False.
Proof. exact (EQ_MP (@lem2973599) (@lem2973528 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973601 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term731 _31796 _31794 _31795.
Proof. exact (h1). Qed.
Lemma lem2973602 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term467 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2973601 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973604 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term454 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2973602 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973606 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term441 _31796 _31794 _31795.
Proof. exact (proj2 (@lem2973604 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973608 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term428 _31794 _31795.
Proof. exact (proj2 (@lem2973606 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973609 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term331 _31794 _31795 _31796.
Proof. exact (proj1 (@lem2973606 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973610 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term329 _31796.
Proof. exact (proj2 (@lem2973609 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973611 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : (term280 _31794 _31795 _31796) = term140.
Proof. exact (proj1 (@lem2973609 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973612 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term404 _31794 _31795.
Proof. exact (proj2 (@lem2973608 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973615 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2973616 : term476 = term305.
Proof. exact (@lem2973615 term140 term169). Qed.
Lemma lem2973618 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973619 : term169 = term288.
Proof. exact (@lem2973618 term86). Qed.
Lemma lem2973621 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973622 : term140 = term229.
Proof. exact (@lem2973621 (NUMERAL 0)). Qed.
Lemma lem2973623 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2973624 : term477 = term478.
Proof. exact (MK_COMB (@lem2973623) (@lem2973622)). Qed.
Lemma lem2973625 : term305 = term479.
Proof. exact (MK_COMB (@lem2973624) (@lem2973619)). Qed.
Lemma lem2973626 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2973628 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973629 : term305 = term306.
Proof. exact (@lem2973628 (NUMERAL 0) term86). Qed.
Lemma lem2973630 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973631 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973632 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973631 h1) (fun h1 : term306 = True => @lem2973630)). Qed.
Lemma lem2973633 : term306 = True.
Proof. exact (EQ_MP (@lem2973632) (@lem2973630)). Qed.
Lemma lem2973634 : term305 = True.
Proof. exact (TRANS (@lem2973629) (@lem2973633)). Qed.
Lemma lem2973635 : True = term305.
Proof. exact (SYM (@lem2973634)). Qed.
Lemma lem2973636 : term305.
Proof. exact (EQ_MP (@lem2973635) (@lem0)). Qed.
Lemma lem2973637 : term481.
Proof. exact (@lem2973626 (@lem2973636)). Qed.
Lemma lem2973639 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973640 : term305 = term306.
Proof. exact (@lem2973639 (NUMERAL 0) term86). Qed.
Lemma lem2973641 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973642 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973643 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973642 h1) (fun h1 : term306 = True => @lem2973641)). Qed.
Lemma lem2973644 : term306 = True.
Proof. exact (EQ_MP (@lem2973643) (@lem2973641)). Qed.
Lemma lem2973645 : term305 = True.
Proof. exact (TRANS (@lem2973640) (@lem2973644)). Qed.
Lemma lem2973646 : True = term305.
Proof. exact (SYM (@lem2973645)). Qed.
Lemma lem2973647 : term305.
Proof. exact (EQ_MP (@lem2973646) (@lem0)). Qed.
Lemma lem2973648 : term479 = term482.
Proof. exact (@lem2973637 (@lem2973647)). Qed.
Lemma lem2973650 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973651 : term241 = term242.
Proof. exact (@lem2973650 term86 term86). Qed.
Lemma lem2973652 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973653 : term244 = term86.
Proof. exact (EQ_MP (@lem2973652) (@lem940073)). Qed.
Lemma lem2973654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973655 : term242 = term169.
Proof. exact (MK_COMB (@lem2973654) (@lem2973653)). Qed.
Lemma lem2973656 : term241 = term169.
Proof. exact (TRANS (@lem2973651) (@lem2973655)). Qed.
Lemma lem2973658 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973659 : term373 = term140.
Proof. exact (@lem2973658 term86). Qed.
Lemma lem2973660 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2973661 : term483 = term477.
Proof. exact (MK_COMB (@lem2973660) (@lem2973659)). Qed.
Lemma lem2973662 : term482 = term305.
Proof. exact (MK_COMB (@lem2973661) (@lem2973656)). Qed.
Lemma lem2973664 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973665 : term305 = term306.
Proof. exact (@lem2973664 (NUMERAL 0) term86). Qed.
Lemma lem2973666 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973667 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973668 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973667 h1) (fun h1 : term306 = True => @lem2973666)). Qed.
Lemma lem2973669 : term306 = True.
Proof. exact (EQ_MP (@lem2973668) (@lem2973666)). Qed.
Lemma lem2973670 : term305 = True.
Proof. exact (TRANS (@lem2973665) (@lem2973669)). Qed.
Lemma lem2973671 : term482 = True.
Proof. exact (TRANS (@lem2973662) (@lem2973670)). Qed.
Lemma lem2973672 : term479 = True.
Proof. exact (TRANS (@lem2973648) (@lem2973671)). Qed.
Lemma lem2973673 : term305 = True.
Proof. exact (TRANS (@lem2973625) (@lem2973672)). Qed.
Lemma lem2973674 : term476 = True.
Proof. exact (TRANS (@lem2973616) (@lem2973673)). Qed.
Lemma lem2973675 : True = term476.
Proof. exact (SYM (@lem2973674)). Qed.
Lemma lem2973676 : term476.
Proof. exact (EQ_MP (@lem2973675) (@lem0)). Qed.
Lemma lem2973677 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term668 _31794 _31795.
Proof. exact (conj (@lem2973676) (@lem2973612 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973679 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2973680 (_31794 : int) (_31795 : int) : term669 _31794 _31795.
Proof. exact (@lem2973679 term169 (term401 _31794 _31795)). Qed.
Lemma lem2973681 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term670 _31794 _31795.
Proof. exact (@lem2973680 _31794 _31795 (@lem2973677 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973682 (_31794 : int) (_31795 : int) : (term671 _31794 _31795) = (term401 _31794 _31795).
Proof. exact (@lem1982733 (term401 _31794 _31795)). Qed.
Lemma lem2973683 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2973684 (_31794 : int) (_31795 : int) : (term672 _31794 _31795) = (term403 _31794 _31795).
Proof. exact (MK_COMB (@lem2973683) (@lem2973682 _31794 _31795)). Qed.
Lemma lem2973685 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2973686 (_31794 : int) (_31795 : int) : (term670 _31794 _31795) = (term404 _31794 _31795).
Proof. exact (MK_COMB (@lem2973684 _31794 _31795) (@lem2973685)). Qed.
Lemma lem2973687 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term404 _31794 _31795.
Proof. exact (EQ_MP (@lem2973686 _31794 _31795) (@lem2973681 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973689 (y : real) : term495 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2973690 (_31794 : int) (_31795 : int) (_31796 : int) : term496 _31794 _31795 _31796.
Proof. exact (@lem2973689 (term280 _31794 _31795 _31796)). Qed.
Lemma lem2973691 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term497 _31794 _31795 _31796.
Proof. exact (@lem2973690 _31794 _31795 _31796 (@lem2973611 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973692 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term585 _31794 _31795 _31796.
Proof. exact (@lem2973691 _31796 _31794 _31795 h1 term232). Qed.
Lemma lem2973693 (_31794 : int) (_31795 : int) (_31796 : int) : (term585 _31794 _31795 _31796) = ((term586 _31794 _31795 _31796) = term140).
Proof. exact (eq_refl (term585 _31794 _31795 _31796)). Qed.
Lemma lem2973694 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : (term586 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2973693 _31794 _31795 _31796) (@lem2973692 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973695 (_31794 : int) (_31795 : int) (_31796 : int) : (term586 _31794 _31795 _31796) = (term587 _31794 _31795 _31796).
Proof. exact (@lem1982781 (real_of_int _31794) term232 (term279 _31795 _31796)). Qed.
Lemma lem2973696 (_31795 : int) (_31796 : int) : (term588 _31795 _31796) = (term589 _31795 _31796).
Proof. exact (@lem1982781 (term276 _31795) term232 (term257 _31796)). Qed.
Lemma lem2973697 (_31796 : int) : (term590 _31796) = (term591 _31796).
Proof. exact (@lem1982749 term232 term232 (real_of_int _31796)). Qed.
Lemma lem2973699 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973700 : term232 = term233.
Proof. exact (@lem2973699 term86). Qed.
Lemma lem2973702 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973703 : term232 = term233.
Proof. exact (@lem2973702 term86). Qed.
Lemma lem2973704 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973705 : term234 = term235.
Proof. exact (MK_COMB (@lem2973704) (@lem2973703)). Qed.
Lemma lem2973706 : term592 = term593.
Proof. exact (MK_COMB (@lem2973705) (@lem2973700)). Qed.
Lemma lem2973707 : term593 = term594.
Proof. exact (@lem1981613 term232 term232 term169 term169). Qed.
Lemma lem2973709 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973710 : term241 = term242.
Proof. exact (@lem2973709 term86 term86). Qed.
Lemma lem2973711 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973712 : term244 = term86.
Proof. exact (EQ_MP (@lem2973711) (@lem940073)). Qed.
Lemma lem2973713 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973714 : term242 = term169.
Proof. exact (MK_COMB (@lem2973713) (@lem2973712)). Qed.
Lemma lem2973715 : term241 = term169.
Proof. exact (TRANS (@lem2973710) (@lem2973714)). Qed.
Lemma lem2973717 (m : nat) (n : nat) : (term595 m n) = (term240 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2973718 : term592 = term242.
Proof. exact (@lem2973717 term86 term86). Qed.
Lemma lem2973719 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973720 : term244 = term86.
Proof. exact (EQ_MP (@lem2973719) (@lem940073)). Qed.
Lemma lem2973721 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973722 : term242 = term169.
Proof. exact (MK_COMB (@lem2973721) (@lem2973720)). Qed.
Lemma lem2973723 : term592 = term169.
Proof. exact (TRANS (@lem2973718) (@lem2973722)). Qed.
Lemma lem2973724 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2973725 : term596 = term597.
Proof. exact (MK_COMB (@lem2973724) (@lem2973723)). Qed.
Lemma lem2973726 : term594 = term288.
Proof. exact (MK_COMB (@lem2973725) (@lem2973715)). Qed.
Lemma lem2973727 : term593 = term288.
Proof. exact (TRANS (@lem2973707) (@lem2973726)). Qed.
Lemma lem2973728 : term592 = term288.
Proof. exact (TRANS (@lem2973706) (@lem2973727)). Qed.
Lemma lem2973730 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2973731 : term288 = term169.
Proof. exact (@lem2973730 term169). Qed.
Lemma lem2973732 : term592 = term169.
Proof. exact (TRANS (@lem2973728) (@lem2973731)). Qed.
Lemma lem2973733 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973734 : term598 = term323.
Proof. exact (MK_COMB (@lem2973733) (@lem2973732)). Qed.
Lemma lem2973735 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2973736 (_31796 : int) : (term591 _31796) = (term488 _31796).
Proof. exact (MK_COMB (@lem2973734) (@lem2973735 _31796)). Qed.
Lemma lem2973737 (_31796 : int) : (term590 _31796) = (term488 _31796).
Proof. exact (TRANS (@lem2973697 _31796) (@lem2973736 _31796)). Qed.
Lemma lem2973738 (_31796 : int) : (term488 _31796) = (real_of_int _31796).
Proof. exact (@lem1982709 (real_of_int _31796)). Qed.
Lemma lem2973739 (_31796 : int) : (term590 _31796) = (real_of_int _31796).
Proof. exact (TRANS (@lem2973737 _31796) (@lem2973738 _31796)). Qed.
Lemma lem2973740 (_31795 : int) : (term599 _31795) = (term600 _31795).
Proof. exact (@lem1982749 term232 term270 (real_of_int _31795)). Qed.
Lemma lem2973742 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973743 : term270 = term273.
Proof. exact (@lem2973742 term2). Qed.
Lemma lem2973745 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973746 : term232 = term233.
Proof. exact (@lem2973745 term86). Qed.
Lemma lem2973747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973748 : term234 = term235.
Proof. exact (MK_COMB (@lem2973747) (@lem2973746)). Qed.
Lemma lem2973749 : term601 = term602.
Proof. exact (MK_COMB (@lem2973748) (@lem2973743)). Qed.
Lemma lem2973750 : term602 = term603.
Proof. exact (@lem1981613 term232 term270 term169 term169). Qed.
Lemma lem2973752 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973753 : term241 = term242.
Proof. exact (@lem2973752 term86 term86). Qed.
Lemma lem2973754 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973755 : term244 = term86.
Proof. exact (EQ_MP (@lem2973754) (@lem940073)). Qed.
Lemma lem2973756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973757 : term242 = term169.
Proof. exact (MK_COMB (@lem2973756) (@lem2973755)). Qed.
Lemma lem2973758 : term241 = term169.
Proof. exact (TRANS (@lem2973753) (@lem2973757)). Qed.
Lemma lem2973760 (m : nat) (n : nat) : (term595 m n) = (term240 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2973761 : term601 = term269.
Proof. exact (@lem2973760 term86 term2). Qed.
Lemma lem2973762 : term267 = term27.
Proof. exact (@lem996238 term27). Qed.
Lemma lem2973763 : (term267 = term27) = (term268 = term2).
Proof. exact (@lem1007663 (BIT1 0) term27 term27). Qed.
Lemma lem2973764 : term268 = term2.
Proof. exact (EQ_MP (@lem2973763) (@lem2973762)). Qed.
Lemma lem2973765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973766 : term269 = term154.
Proof. exact (MK_COMB (@lem2973765) (@lem2973764)). Qed.
Lemma lem2973767 : term601 = term154.
Proof. exact (TRANS (@lem2973761) (@lem2973766)). Qed.
Lemma lem2973768 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2973769 : term604 = term605.
Proof. exact (MK_COMB (@lem2973768) (@lem2973767)). Qed.
Lemma lem2973770 : term603 = term260.
Proof. exact (MK_COMB (@lem2973769) (@lem2973758)). Qed.
Lemma lem2973771 : term602 = term260.
Proof. exact (TRANS (@lem2973750) (@lem2973770)). Qed.
Lemma lem2973772 : term601 = term260.
Proof. exact (TRANS (@lem2973749) (@lem2973771)). Qed.
Lemma lem2973774 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2973775 : term260 = term154.
Proof. exact (@lem2973774 term154). Qed.
Lemma lem2973776 : term601 = term154.
Proof. exact (TRANS (@lem2973772) (@lem2973775)). Qed.
Lemma lem2973777 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973778 : term606 = term156.
Proof. exact (MK_COMB (@lem2973777) (@lem2973776)). Qed.
Lemma lem2973779 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2973780 (_31795 : int) : (term600 _31795) = (term157 _31795).
Proof. exact (MK_COMB (@lem2973778) (@lem2973779 _31795)). Qed.
Lemma lem2973781 (_31795 : int) : (term599 _31795) = (term157 _31795).
Proof. exact (TRANS (@lem2973740 _31795) (@lem2973780 _31795)). Qed.
Lemma lem2973782 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973783 (_31795 : int) : (term607 _31795) = (term159 _31795).
Proof. exact (MK_COMB (@lem2973782) (@lem2973781 _31795)). Qed.
Lemma lem2973784 (_31795 : int) (_31796 : int) : (term589 _31795 _31796) = (term160 _31795 _31796).
Proof. exact (MK_COMB (@lem2973783 _31795) (@lem2973739 _31796)). Qed.
Lemma lem2973785 (_31795 : int) (_31796 : int) : (term588 _31795 _31796) = (term160 _31795 _31796).
Proof. exact (TRANS (@lem2973696 _31795 _31796) (@lem2973784 _31795 _31796)). Qed.
Lemma lem2973788 (_31794 : int) : (term295 _31794) = (term295 _31794).
Proof. exact (eq_refl (term295 _31794)). Qed.
Lemma lem2973789 (_31794 : int) (_31795 : int) (_31796 : int) : (term587 _31794 _31795 _31796) = (term608 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2973788 _31794) (@lem2973785 _31795 _31796)). Qed.
Lemma lem2973790 (_31794 : int) (_31795 : int) (_31796 : int) : (term586 _31794 _31795 _31796) = (term608 _31794 _31795 _31796).
Proof. exact (TRANS (@lem2973695 _31794 _31795 _31796) (@lem2973789 _31794 _31795 _31796)). Qed.
Lemma lem2973791 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2973792 (_31794 : int) (_31795 : int) (_31796 : int) : (term609 _31794 _31795 _31796) = (term610 _31794 _31795 _31796).
Proof. exact (MK_COMB (@lem2973791) (@lem2973790 _31794 _31795 _31796)). Qed.
Lemma lem2973793 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2973794 (_31794 : int) (_31795 : int) (_31796 : int) : ((term586 _31794 _31795 _31796) = term140) = ((term608 _31794 _31795 _31796) = term140).
Proof. exact (MK_COMB (@lem2973792 _31794 _31795 _31796) (@lem2973793)). Qed.
Lemma lem2973795 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : (term608 _31794 _31795 _31796) = term140.
Proof. exact (EQ_MP (@lem2973794 _31794 _31795 _31796) (@lem2973694 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973796 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term673 _31796 _31794 _31795.
Proof. exact (conj (@lem2973795 _31796 _31794 _31795 h1) (@lem2973687 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973798 (x : real) (y : real) : term502 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2973799 (_31796 : int) (_31794 : int) (_31795 : int) : term674 _31796 _31794 _31795.
Proof. exact (@lem2973798 (term608 _31794 _31795 _31796) (term401 _31794 _31795)). Qed.
Lemma lem2973800 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term675 _31796 _31794 _31795.
Proof. exact (@lem2973799 _31796 _31794 _31795 (@lem2973796 _31796 _31794 _31795 h1)). Qed.
Lemma lem2973801 (_31794 : int) (_31796 : int) (_31795 : int) : (term676 _31796 _31794 _31795) = (term677 _31794 _31796 _31795).
Proof. exact (@lem1982753 (term257 _31794) (real_of_int _31794) (term160 _31795 _31796) (term400 _31795)). Qed.
Lemma lem2973802 (_31794 : int) : (term562 _31794) = (term509 _31794).
Proof. exact (@lem1982713 term232 (real_of_int _31794)). Qed.
Lemma lem2973804 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973805 : term169 = term288.
Proof. exact (@lem2973804 term86). Qed.
Lemma lem2973807 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973808 : term232 = term233.
Proof. exact (@lem2973807 term86). Qed.
Lemma lem2973809 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973810 : term510 = term511.
Proof. exact (MK_COMB (@lem2973809) (@lem2973808)). Qed.
Lemma lem2973811 : term512 = term513.
Proof. exact (MK_COMB (@lem2973810) (@lem2973805)). Qed.
Lemma lem2973812 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2973814 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973815 : term305 = term306.
Proof. exact (@lem2973814 (NUMERAL 0) term86). Qed.
Lemma lem2973816 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973817 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973818 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973817 h1) (fun h1 : term306 = True => @lem2973816)). Qed.
Lemma lem2973819 : term306 = True.
Proof. exact (EQ_MP (@lem2973818) (@lem2973816)). Qed.
Lemma lem2973820 : term305 = True.
Proof. exact (TRANS (@lem2973815) (@lem2973819)). Qed.
Lemma lem2973821 : True = term305.
Proof. exact (SYM (@lem2973820)). Qed.
Lemma lem2973822 : term305.
Proof. exact (EQ_MP (@lem2973821) (@lem0)). Qed.
Lemma lem2973823 : term515.
Proof. exact (@lem2973812 (@lem2973822)). Qed.
Lemma lem2973825 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973826 : term305 = term306.
Proof. exact (@lem2973825 (NUMERAL 0) term86). Qed.
Lemma lem2973827 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973828 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973829 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973828 h1) (fun h1 : term306 = True => @lem2973827)). Qed.
Lemma lem2973830 : term306 = True.
Proof. exact (EQ_MP (@lem2973829) (@lem2973827)). Qed.
Lemma lem2973831 : term305 = True.
Proof. exact (TRANS (@lem2973826) (@lem2973830)). Qed.
Lemma lem2973832 : True = term305.
Proof. exact (SYM (@lem2973831)). Qed.
Lemma lem2973833 : term305.
Proof. exact (EQ_MP (@lem2973832) (@lem0)). Qed.
Lemma lem2973834 : term516.
Proof. exact (@lem2973823 (@lem2973833)). Qed.
Lemma lem2973836 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973837 : term305 = term306.
Proof. exact (@lem2973836 (NUMERAL 0) term86). Qed.
Lemma lem2973838 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973839 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973840 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973839 h1) (fun h1 : term306 = True => @lem2973838)). Qed.
Lemma lem2973841 : term306 = True.
Proof. exact (EQ_MP (@lem2973840) (@lem2973838)). Qed.
Lemma lem2973842 : term305 = True.
Proof. exact (TRANS (@lem2973837) (@lem2973841)). Qed.
Lemma lem2973843 : True = term305.
Proof. exact (SYM (@lem2973842)). Qed.
Lemma lem2973844 : term305.
Proof. exact (EQ_MP (@lem2973843) (@lem0)). Qed.
Lemma lem2973845 : term517.
Proof. exact (@lem2973834 (@lem2973844)). Qed.
Lemma lem2973847 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973848 : term241 = term242.
Proof. exact (@lem2973847 term86 term86). Qed.
Lemma lem2973849 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973850 : term244 = term86.
Proof. exact (EQ_MP (@lem2973849) (@lem940073)). Qed.
Lemma lem2973851 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973852 : term242 = term169.
Proof. exact (MK_COMB (@lem2973851) (@lem2973850)). Qed.
Lemma lem2973853 : term241 = term169.
Proof. exact (TRANS (@lem2973848) (@lem2973852)). Qed.
Lemma lem2973855 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973856 : term289 = term292.
Proof. exact (@lem2973855 term86 term86). Qed.
Lemma lem2973857 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973858 : term244 = term86.
Proof. exact (EQ_MP (@lem2973857) (@lem940073)). Qed.
Lemma lem2973859 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973860 : term242 = term169.
Proof. exact (MK_COMB (@lem2973859) (@lem2973858)). Qed.
Lemma lem2973861 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973862 : term292 = term232.
Proof. exact (MK_COMB (@lem2973861) (@lem2973860)). Qed.
Lemma lem2973863 : term289 = term232.
Proof. exact (TRANS (@lem2973856) (@lem2973862)). Qed.
Lemma lem2973864 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973865 : term518 = term510.
Proof. exact (MK_COMB (@lem2973864) (@lem2973863)). Qed.
Lemma lem2973866 : term519 = term512.
Proof. exact (MK_COMB (@lem2973865) (@lem2973853)). Qed.
Lemma lem2973868 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2973869 : term512 = term140.
Proof. exact (@lem2973868 term86). Qed.
Lemma lem2973870 : term519 = term140.
Proof. exact (TRANS (@lem2973866) (@lem2973869)). Qed.
Lemma lem2973871 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973872 : term521 = term371.
Proof. exact (MK_COMB (@lem2973871) (@lem2973870)). Qed.
Lemma lem2973873 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2973874 : term522 = term373.
Proof. exact (MK_COMB (@lem2973872) (@lem2973873)). Qed.
Lemma lem2973876 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973877 : term373 = term140.
Proof. exact (@lem2973876 term86). Qed.
Lemma lem2973878 : term522 = term140.
Proof. exact (TRANS (@lem2973874) (@lem2973877)). Qed.
Lemma lem2973880 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973881 : term241 = term242.
Proof. exact (@lem2973880 term86 term86). Qed.
Lemma lem2973882 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973883 : term244 = term86.
Proof. exact (EQ_MP (@lem2973882) (@lem940073)). Qed.
Lemma lem2973884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973885 : term242 = term169.
Proof. exact (MK_COMB (@lem2973884) (@lem2973883)). Qed.
Lemma lem2973886 : term241 = term169.
Proof. exact (TRANS (@lem2973881) (@lem2973885)). Qed.
Lemma lem2973887 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2973888 : term375 = term373.
Proof. exact (MK_COMB (@lem2973887) (@lem2973886)). Qed.
Lemma lem2973890 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973891 : term373 = term140.
Proof. exact (@lem2973890 term86). Qed.
Lemma lem2973892 : term375 = term140.
Proof. exact (TRANS (@lem2973888) (@lem2973891)). Qed.
Lemma lem2973893 : term140 = term375.
Proof. exact (SYM (@lem2973892)). Qed.
Lemma lem2973894 : term522 = term375.
Proof. exact (TRANS (@lem2973878) (@lem2973893)). Qed.
Lemma lem2973895 : term513 = term229.
Proof. exact (@lem2973845 (@lem2973894)). Qed.
Lemma lem2973896 : term512 = term229.
Proof. exact (TRANS (@lem2973811) (@lem2973895)). Qed.
Lemma lem2973898 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2973899 : term229 = term140.
Proof. exact (@lem2973898 term140). Qed.
Lemma lem2973900 : term512 = term140.
Proof. exact (TRANS (@lem2973896) (@lem2973899)). Qed.
Lemma lem2973901 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973902 : term523 = term371.
Proof. exact (MK_COMB (@lem2973901) (@lem2973900)). Qed.
Lemma lem2973903 (_31794 : int) : (real_of_int _31794) = (real_of_int _31794).
Proof. exact (eq_refl (real_of_int _31794)). Qed.
Lemma lem2973904 (_31794 : int) : (term509 _31794) = (term524 _31794).
Proof. exact (MK_COMB (@lem2973902) (@lem2973903 _31794)). Qed.
Lemma lem2973905 (_31794 : int) : (term562 _31794) = (term524 _31794).
Proof. exact (TRANS (@lem2973802 _31794) (@lem2973904 _31794)). Qed.
Lemma lem2973906 (_31794 : int) : (term524 _31794) = term140.
Proof. exact (@lem1982719 (real_of_int _31794)). Qed.
Lemma lem2973907 (_31794 : int) : (term562 _31794) = term140.
Proof. exact (TRANS (@lem2973905 _31794) (@lem2973906 _31794)). Qed.
Lemma lem2973908 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973909 (_31794 : int) : (term563 _31794) = term526.
Proof. exact (MK_COMB (@lem2973908) (@lem2973907 _31794)). Qed.
Lemma lem2973910 (_31795 : int) (_31796 : int) : (term678 _31796 _31795) = (term679 _31795 _31796).
Proof. exact (@lem1982753 (term157 _31795) (term276 _31795) (real_of_int _31796) term270). Qed.
Lemma lem2973911 (_31795 : int) : (term618 _31795) = (term619 _31795).
Proof. exact (@lem1982711 term154 term270 (real_of_int _31795)). Qed.
Lemma lem2973913 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2973914 : term270 = term273.
Proof. exact (@lem2973913 term2). Qed.
Lemma lem2973916 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2973917 : term154 = term260.
Proof. exact (@lem2973916 term2). Qed.
Lemma lem2973918 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973919 : term297 = term300.
Proof. exact (MK_COMB (@lem2973918) (@lem2973917)). Qed.
Lemma lem2973920 : term620 = term621.
Proof. exact (MK_COMB (@lem2973919) (@lem2973914)). Qed.
Lemma lem2973921 : term622.
Proof. exact (@lem1981473 term154 term169 term270 term169 term140 term169). Qed.
Lemma lem2973923 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973924 : term305 = term306.
Proof. exact (@lem2973923 (NUMERAL 0) term86). Qed.
Lemma lem2973925 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973926 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973927 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973926 h1) (fun h1 : term306 = True => @lem2973925)). Qed.
Lemma lem2973928 : term306 = True.
Proof. exact (EQ_MP (@lem2973927) (@lem2973925)). Qed.
Lemma lem2973929 : term305 = True.
Proof. exact (TRANS (@lem2973924) (@lem2973928)). Qed.
Lemma lem2973930 : True = term305.
Proof. exact (SYM (@lem2973929)). Qed.
Lemma lem2973931 : term305.
Proof. exact (EQ_MP (@lem2973930) (@lem0)). Qed.
Lemma lem2973932 : term623.
Proof. exact (@lem2973921 (@lem2973931)). Qed.
Lemma lem2973934 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973935 : term305 = term306.
Proof. exact (@lem2973934 (NUMERAL 0) term86). Qed.
Lemma lem2973936 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973937 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973938 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973937 h1) (fun h1 : term306 = True => @lem2973936)). Qed.
Lemma lem2973939 : term306 = True.
Proof. exact (EQ_MP (@lem2973938) (@lem2973936)). Qed.
Lemma lem2973940 : term305 = True.
Proof. exact (TRANS (@lem2973935) (@lem2973939)). Qed.
Lemma lem2973941 : True = term305.
Proof. exact (SYM (@lem2973940)). Qed.
Lemma lem2973942 : term305.
Proof. exact (EQ_MP (@lem2973941) (@lem0)). Qed.
Lemma lem2973943 : term624.
Proof. exact (@lem2973932 (@lem2973942)). Qed.
Lemma lem2973945 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2973946 : term305 = term306.
Proof. exact (@lem2973945 (NUMERAL 0) term86). Qed.
Lemma lem2973947 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2973948 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2973949 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2973948 h1) (fun h1 : term306 = True => @lem2973947)). Qed.
Lemma lem2973950 : term306 = True.
Proof. exact (EQ_MP (@lem2973949) (@lem2973947)). Qed.
Lemma lem2973951 : term305 = True.
Proof. exact (TRANS (@lem2973946) (@lem2973950)). Qed.
Lemma lem2973952 : True = term305.
Proof. exact (SYM (@lem2973951)). Qed.
Lemma lem2973953 : term305.
Proof. exact (EQ_MP (@lem2973952) (@lem0)). Qed.
Lemma lem2973954 : term625.
Proof. exact (@lem2973943 (@lem2973953)). Qed.
Lemma lem2973956 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2973957 : term539 = term540.
Proof. exact (@lem2973956 term2 term86). Qed.
Lemma lem2973958 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2973959 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2973960 : term314 = term2.
Proof. exact (EQ_MP (@lem2973959) (@lem2973958)). Qed.
Lemma lem2973961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973962 : term312 = term154.
Proof. exact (MK_COMB (@lem2973961) (@lem2973960)). Qed.
Lemma lem2973963 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2973964 : term540 = term270.
Proof. exact (MK_COMB (@lem2973963) (@lem2973962)). Qed.
Lemma lem2973965 : term539 = term270.
Proof. exact (TRANS (@lem2973957) (@lem2973964)). Qed.
Lemma lem2973967 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973968 : term311 = term312.
Proof. exact (@lem2973967 term2 term86). Qed.
Lemma lem2973969 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2973970 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2973971 : term314 = term2.
Proof. exact (EQ_MP (@lem2973970) (@lem2973969)). Qed.
Lemma lem2973972 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973973 : term312 = term154.
Proof. exact (MK_COMB (@lem2973972) (@lem2973971)). Qed.
Lemma lem2973974 : term311 = term154.
Proof. exact (TRANS (@lem2973968) (@lem2973973)). Qed.
Lemma lem2973975 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2973976 : term315 = term297.
Proof. exact (MK_COMB (@lem2973975) (@lem2973974)). Qed.
Lemma lem2973977 : term626 = term620.
Proof. exact (MK_COMB (@lem2973976) (@lem2973965)). Qed.
Lemma lem2973979 (m : nat) : (term369 m) = term140.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2973980 : term620 = term140.
Proof. exact (@lem2973979 term2). Qed.
Lemma lem2973981 : term626 = term140.
Proof. exact (TRANS (@lem2973977) (@lem2973980)). Qed.
Lemma lem2973982 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2973983 : term627 = term371.
Proof. exact (MK_COMB (@lem2973982) (@lem2973981)). Qed.
Lemma lem2973984 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2973985 : term628 = term373.
Proof. exact (MK_COMB (@lem2973983) (@lem2973984)). Qed.
Lemma lem2973987 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2973988 : term373 = term140.
Proof. exact (@lem2973987 term86). Qed.
Lemma lem2973989 : term628 = term140.
Proof. exact (TRANS (@lem2973985) (@lem2973988)). Qed.
Lemma lem2973991 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2973992 : term241 = term242.
Proof. exact (@lem2973991 term86 term86). Qed.
Lemma lem2973993 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2973994 : term244 = term86.
Proof. exact (EQ_MP (@lem2973993) (@lem940073)). Qed.
Lemma lem2973995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2973996 : term242 = term169.
Proof. exact (MK_COMB (@lem2973995) (@lem2973994)). Qed.
Lemma lem2973997 : term241 = term169.
Proof. exact (TRANS (@lem2973992) (@lem2973996)). Qed.
Lemma lem2973998 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2973999 : term375 = term373.
Proof. exact (MK_COMB (@lem2973998) (@lem2973997)). Qed.
Lemma lem2974001 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2974002 : term373 = term140.
Proof. exact (@lem2974001 term86). Qed.
Lemma lem2974003 : term375 = term140.
Proof. exact (TRANS (@lem2973999) (@lem2974002)). Qed.
Lemma lem2974004 : term140 = term375.
Proof. exact (SYM (@lem2974003)). Qed.
Lemma lem2974005 : term628 = term375.
Proof. exact (TRANS (@lem2973989) (@lem2974004)). Qed.
Lemma lem2974006 : term621 = term229.
Proof. exact (@lem2973954 (@lem2974005)). Qed.
Lemma lem2974007 : term620 = term229.
Proof. exact (TRANS (@lem2973920) (@lem2974006)). Qed.
Lemma lem2974009 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2974010 : term229 = term140.
Proof. exact (@lem2974009 term140). Qed.
Lemma lem2974011 : term620 = term140.
Proof. exact (TRANS (@lem2974007) (@lem2974010)). Qed.
Lemma lem2974012 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2974013 : term629 = term371.
Proof. exact (MK_COMB (@lem2974012) (@lem2974011)). Qed.
Lemma lem2974014 (_31795 : int) : (real_of_int _31795) = (real_of_int _31795).
Proof. exact (eq_refl (real_of_int _31795)). Qed.
Lemma lem2974015 (_31795 : int) : (term619 _31795) = (term524 _31795).
Proof. exact (MK_COMB (@lem2974013) (@lem2974014 _31795)). Qed.
Lemma lem2974016 (_31795 : int) : (term618 _31795) = (term524 _31795).
Proof. exact (TRANS (@lem2973911 _31795) (@lem2974015 _31795)). Qed.
Lemma lem2974017 (_31795 : int) : (term524 _31795) = term140.
Proof. exact (@lem1982719 (real_of_int _31795)). Qed.
Lemma lem2974018 (_31795 : int) : (term618 _31795) = term140.
Proof. exact (TRANS (@lem2974016 _31795) (@lem2974017 _31795)). Qed.
Lemma lem2974019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2974020 (_31795 : int) : (term630 _31795) = term526.
Proof. exact (MK_COMB (@lem2974019) (@lem2974018 _31795)). Qed.
Lemma lem2974021 (_31796 : int) : (term680 _31796) = (term680 _31796).
Proof. exact (eq_refl (term680 _31796)). Qed.
Lemma lem2974022 (_31795 : int) (_31796 : int) : (term679 _31795 _31796) = (term681 _31796).
Proof. exact (MK_COMB (@lem2974020 _31795) (@lem2974021 _31796)). Qed.
Lemma lem2974023 (_31795 : int) (_31796 : int) : (term678 _31796 _31795) = (term681 _31796).
Proof. exact (TRANS (@lem2973910 _31795 _31796) (@lem2974022 _31795 _31796)). Qed.
Lemma lem2974024 (_31796 : int) : (term681 _31796) = (term680 _31796).
Proof. exact (@lem1982721 (term680 _31796)). Qed.
Lemma lem2974025 (_31795 : int) (_31796 : int) : (term678 _31796 _31795) = (term680 _31796).
Proof. exact (TRANS (@lem2974023 _31795 _31796) (@lem2974024 _31796)). Qed.
Lemma lem2974026 (_31794 : int) (_31795 : int) (_31796 : int) : (term677 _31794 _31796 _31795) = (term681 _31796).
Proof. exact (MK_COMB (@lem2973909 _31794) (@lem2974025 _31795 _31796)). Qed.
Lemma lem2974027 (_31794 : int) (_31795 : int) (_31796 : int) : (term676 _31796 _31794 _31795) = (term681 _31796).
Proof. exact (TRANS (@lem2973801 _31794 _31796 _31795) (@lem2974026 _31794 _31795 _31796)). Qed.
Lemma lem2974028 (_31796 : int) : (term681 _31796) = (term680 _31796).
Proof. exact (@lem1982721 (term680 _31796)). Qed.
Lemma lem2974029 (_31794 : int) (_31795 : int) (_31796 : int) : (term676 _31796 _31794 _31795) = (term680 _31796).
Proof. exact (TRANS (@lem2974027 _31794 _31795 _31796) (@lem2974028 _31796)). Qed.
Lemma lem2974030 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2974031 (_31794 : int) (_31795 : int) (_31796 : int) : (term682 _31796 _31794 _31795) = (term683 _31796).
Proof. exact (MK_COMB (@lem2974030) (@lem2974029 _31794 _31795 _31796)). Qed.
Lemma lem2974032 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2974033 (_31794 : int) (_31795 : int) (_31796 : int) : (term675 _31796 _31794 _31795) = (term684 _31796).
Proof. exact (MK_COMB (@lem2974031 _31794 _31795 _31796) (@lem2974032)). Qed.
Lemma lem2974034 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term684 _31796.
Proof. exact (EQ_MP (@lem2974033 _31794 _31795 _31796) (@lem2973800 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974036 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2974037 : term476 = term305.
Proof. exact (@lem2974036 term140 term169). Qed.
Lemma lem2974039 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2974040 : term169 = term288.
Proof. exact (@lem2974039 term86). Qed.
Lemma lem2974042 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2974043 : term140 = term229.
Proof. exact (@lem2974042 (NUMERAL 0)). Qed.
Lemma lem2974044 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2974045 : term477 = term478.
Proof. exact (MK_COMB (@lem2974044) (@lem2974043)). Qed.
Lemma lem2974046 : term305 = term479.
Proof. exact (MK_COMB (@lem2974045) (@lem2974040)). Qed.
Lemma lem2974047 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2974049 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974050 : term305 = term306.
Proof. exact (@lem2974049 (NUMERAL 0) term86). Qed.
Lemma lem2974051 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974052 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974053 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974052 h1) (fun h1 : term306 = True => @lem2974051)). Qed.
Lemma lem2974054 : term306 = True.
Proof. exact (EQ_MP (@lem2974053) (@lem2974051)). Qed.
Lemma lem2974055 : term305 = True.
Proof. exact (TRANS (@lem2974050) (@lem2974054)). Qed.
Lemma lem2974056 : True = term305.
Proof. exact (SYM (@lem2974055)). Qed.
Lemma lem2974057 : term305.
Proof. exact (EQ_MP (@lem2974056) (@lem0)). Qed.
Lemma lem2974058 : term481.
Proof. exact (@lem2974047 (@lem2974057)). Qed.
Lemma lem2974060 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974061 : term305 = term306.
Proof. exact (@lem2974060 (NUMERAL 0) term86). Qed.
Lemma lem2974062 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974063 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974064 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974063 h1) (fun h1 : term306 = True => @lem2974062)). Qed.
Lemma lem2974065 : term306 = True.
Proof. exact (EQ_MP (@lem2974064) (@lem2974062)). Qed.
Lemma lem2974066 : term305 = True.
Proof. exact (TRANS (@lem2974061) (@lem2974065)). Qed.
Lemma lem2974067 : True = term305.
Proof. exact (SYM (@lem2974066)). Qed.
Lemma lem2974068 : term305.
Proof. exact (EQ_MP (@lem2974067) (@lem0)). Qed.
Lemma lem2974069 : term479 = term482.
Proof. exact (@lem2974058 (@lem2974068)). Qed.
Lemma lem2974071 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2974072 : term241 = term242.
Proof. exact (@lem2974071 term86 term86). Qed.
Lemma lem2974073 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974074 : term244 = term86.
Proof. exact (EQ_MP (@lem2974073) (@lem940073)). Qed.
Lemma lem2974075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974076 : term242 = term169.
Proof. exact (MK_COMB (@lem2974075) (@lem2974074)). Qed.
Lemma lem2974077 : term241 = term169.
Proof. exact (TRANS (@lem2974072) (@lem2974076)). Qed.
Lemma lem2974079 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2974080 : term373 = term140.
Proof. exact (@lem2974079 term86). Qed.
Lemma lem2974081 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2974082 : term483 = term477.
Proof. exact (MK_COMB (@lem2974081) (@lem2974080)). Qed.
Lemma lem2974083 : term482 = term305.
Proof. exact (MK_COMB (@lem2974082) (@lem2974077)). Qed.
Lemma lem2974085 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974086 : term305 = term306.
Proof. exact (@lem2974085 (NUMERAL 0) term86). Qed.
Lemma lem2974087 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974088 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974089 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974088 h1) (fun h1 : term306 = True => @lem2974087)). Qed.
Lemma lem2974090 : term306 = True.
Proof. exact (EQ_MP (@lem2974089) (@lem2974087)). Qed.
Lemma lem2974091 : term305 = True.
Proof. exact (TRANS (@lem2974086) (@lem2974090)). Qed.
Lemma lem2974092 : term482 = True.
Proof. exact (TRANS (@lem2974083) (@lem2974091)). Qed.
Lemma lem2974093 : term479 = True.
Proof. exact (TRANS (@lem2974069) (@lem2974092)). Qed.
Lemma lem2974094 : term305 = True.
Proof. exact (TRANS (@lem2974046) (@lem2974093)). Qed.
Lemma lem2974095 : term476 = True.
Proof. exact (TRANS (@lem2974037) (@lem2974094)). Qed.
Lemma lem2974096 : True = term476.
Proof. exact (SYM (@lem2974095)). Qed.
Lemma lem2974097 : term476.
Proof. exact (EQ_MP (@lem2974096) (@lem0)). Qed.
Lemma lem2974098 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term685 _31796.
Proof. exact (conj (@lem2974097) (@lem2974034 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974100 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2974101 (_31796 : int) : term686 _31796.
Proof. exact (@lem2974100 term169 (term680 _31796)). Qed.
Lemma lem2974102 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term687 _31796.
Proof. exact (@lem2974101 _31796 (@lem2974098 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974103 (_31796 : int) : (term688 _31796) = (term680 _31796).
Proof. exact (@lem1982733 (term680 _31796)). Qed.
Lemma lem2974104 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2974105 (_31796 : int) : (term689 _31796) = (term683 _31796).
Proof. exact (MK_COMB (@lem2974104) (@lem2974103 _31796)). Qed.
Lemma lem2974106 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2974107 (_31796 : int) : (term687 _31796) = (term684 _31796).
Proof. exact (MK_COMB (@lem2974105 _31796) (@lem2974106)). Qed.
Lemma lem2974108 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term684 _31796.
Proof. exact (EQ_MP (@lem2974107 _31796) (@lem2974102 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974110 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2974111 : term476 = term305.
Proof. exact (@lem2974110 term140 term169). Qed.
Lemma lem2974113 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2974114 : term169 = term288.
Proof. exact (@lem2974113 term86). Qed.
Lemma lem2974116 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2974117 : term140 = term229.
Proof. exact (@lem2974116 (NUMERAL 0)). Qed.
Lemma lem2974118 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2974119 : term477 = term478.
Proof. exact (MK_COMB (@lem2974118) (@lem2974117)). Qed.
Lemma lem2974120 : term305 = term479.
Proof. exact (MK_COMB (@lem2974119) (@lem2974114)). Qed.
Lemma lem2974121 : term480.
Proof. exact (@lem1980255 term140 term169 term169 term169). Qed.
Lemma lem2974123 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974124 : term305 = term306.
Proof. exact (@lem2974123 (NUMERAL 0) term86). Qed.
Lemma lem2974125 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974126 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974127 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974126 h1) (fun h1 : term306 = True => @lem2974125)). Qed.
Lemma lem2974128 : term306 = True.
Proof. exact (EQ_MP (@lem2974127) (@lem2974125)). Qed.
Lemma lem2974129 : term305 = True.
Proof. exact (TRANS (@lem2974124) (@lem2974128)). Qed.
Lemma lem2974130 : True = term305.
Proof. exact (SYM (@lem2974129)). Qed.
Lemma lem2974131 : term305.
Proof. exact (EQ_MP (@lem2974130) (@lem0)). Qed.
Lemma lem2974132 : term481.
Proof. exact (@lem2974121 (@lem2974131)). Qed.
Lemma lem2974134 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974135 : term305 = term306.
Proof. exact (@lem2974134 (NUMERAL 0) term86). Qed.
Lemma lem2974136 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974137 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974138 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974137 h1) (fun h1 : term306 = True => @lem2974136)). Qed.
Lemma lem2974139 : term306 = True.
Proof. exact (EQ_MP (@lem2974138) (@lem2974136)). Qed.
Lemma lem2974140 : term305 = True.
Proof. exact (TRANS (@lem2974135) (@lem2974139)). Qed.
Lemma lem2974141 : True = term305.
Proof. exact (SYM (@lem2974140)). Qed.
Lemma lem2974142 : term305.
Proof. exact (EQ_MP (@lem2974141) (@lem0)). Qed.
Lemma lem2974143 : term479 = term482.
Proof. exact (@lem2974132 (@lem2974142)). Qed.
Lemma lem2974145 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2974146 : term241 = term242.
Proof. exact (@lem2974145 term86 term86). Qed.
Lemma lem2974147 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974148 : term244 = term86.
Proof. exact (EQ_MP (@lem2974147) (@lem940073)). Qed.
Lemma lem2974149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974150 : term242 = term169.
Proof. exact (MK_COMB (@lem2974149) (@lem2974148)). Qed.
Lemma lem2974151 : term241 = term169.
Proof. exact (TRANS (@lem2974146) (@lem2974150)). Qed.
Lemma lem2974153 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2974154 : term373 = term140.
Proof. exact (@lem2974153 term86). Qed.
Lemma lem2974155 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2974156 : term483 = term477.
Proof. exact (MK_COMB (@lem2974155) (@lem2974154)). Qed.
Lemma lem2974157 : term482 = term305.
Proof. exact (MK_COMB (@lem2974156) (@lem2974151)). Qed.
Lemma lem2974159 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974160 : term305 = term306.
Proof. exact (@lem2974159 (NUMERAL 0) term86). Qed.
Lemma lem2974161 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974162 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974163 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974162 h1) (fun h1 : term306 = True => @lem2974161)). Qed.
Lemma lem2974164 : term306 = True.
Proof. exact (EQ_MP (@lem2974163) (@lem2974161)). Qed.
Lemma lem2974165 : term305 = True.
Proof. exact (TRANS (@lem2974160) (@lem2974164)). Qed.
Lemma lem2974166 : term482 = True.
Proof. exact (TRANS (@lem2974157) (@lem2974165)). Qed.
Lemma lem2974167 : term479 = True.
Proof. exact (TRANS (@lem2974143) (@lem2974166)). Qed.
Lemma lem2974168 : term305 = True.
Proof. exact (TRANS (@lem2974120) (@lem2974167)). Qed.
Lemma lem2974169 : term476 = True.
Proof. exact (TRANS (@lem2974111) (@lem2974168)). Qed.
Lemma lem2974170 : True = term476.
Proof. exact (SYM (@lem2974169)). Qed.
Lemma lem2974171 : term476.
Proof. exact (EQ_MP (@lem2974170) (@lem0)). Qed.
Lemma lem2974172 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term732 _31796.
Proof. exact (conj (@lem2974171) (@lem2973610 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974174 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2974175 (_31796 : int) : term733 _31796.
Proof. exact (@lem2974174 term169 (term326 _31796)). Qed.
Lemma lem2974176 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term734 _31796.
Proof. exact (@lem2974175 _31796 (@lem2974172 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974177 (_31796 : int) : (term735 _31796) = (term326 _31796).
Proof. exact (@lem1982733 (term326 _31796)). Qed.
Lemma lem2974178 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2974179 (_31796 : int) : (term736 _31796) = (term328 _31796).
Proof. exact (MK_COMB (@lem2974178) (@lem2974177 _31796)). Qed.
Lemma lem2974180 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2974181 (_31796 : int) : (term734 _31796) = (term329 _31796).
Proof. exact (MK_COMB (@lem2974179 _31796) (@lem2974180)). Qed.
Lemma lem2974182 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term329 _31796.
Proof. exact (EQ_MP (@lem2974181 _31796) (@lem2974176 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974183 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term737 _31796.
Proof. exact (conj (@lem2974182 _31796 _31794 _31795 h1) (@lem2974108 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974185 (x : real) (y : real) : term557 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2974186 (_31796 : int) : term738 _31796.
Proof. exact (@lem2974185 (term326 _31796) (term680 _31796)). Qed.
Lemma lem2974187 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term739 _31796.
Proof. exact (@lem2974186 _31796 (@lem2974183 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974188 (_31796 : int) : (term740 _31796) = (term741 _31796).
Proof. exact (@lem1982753 (term257 _31796) (real_of_int _31796) term169 term270). Qed.
Lemma lem2974189 (_31796 : int) : (term562 _31796) = (term509 _31796).
Proof. exact (@lem1982713 term232 (real_of_int _31796)). Qed.
Lemma lem2974191 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2974192 : term169 = term288.
Proof. exact (@lem2974191 term86). Qed.
Lemma lem2974194 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2974195 : term232 = term233.
Proof. exact (@lem2974194 term86). Qed.
Lemma lem2974196 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2974197 : term510 = term511.
Proof. exact (MK_COMB (@lem2974196) (@lem2974195)). Qed.
Lemma lem2974198 : term512 = term513.
Proof. exact (MK_COMB (@lem2974197) (@lem2974192)). Qed.
Lemma lem2974199 : term514.
Proof. exact (@lem1981473 term232 term169 term169 term169 term140 term169). Qed.
Lemma lem2974201 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974202 : term305 = term306.
Proof. exact (@lem2974201 (NUMERAL 0) term86). Qed.
Lemma lem2974203 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974204 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974205 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974204 h1) (fun h1 : term306 = True => @lem2974203)). Qed.
Lemma lem2974206 : term306 = True.
Proof. exact (EQ_MP (@lem2974205) (@lem2974203)). Qed.
Lemma lem2974207 : term305 = True.
Proof. exact (TRANS (@lem2974202) (@lem2974206)). Qed.
Lemma lem2974208 : True = term305.
Proof. exact (SYM (@lem2974207)). Qed.
Lemma lem2974209 : term305.
Proof. exact (EQ_MP (@lem2974208) (@lem0)). Qed.
Lemma lem2974210 : term515.
Proof. exact (@lem2974199 (@lem2974209)). Qed.
Lemma lem2974212 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974213 : term305 = term306.
Proof. exact (@lem2974212 (NUMERAL 0) term86). Qed.
Lemma lem2974214 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974215 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974216 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974215 h1) (fun h1 : term306 = True => @lem2974214)). Qed.
Lemma lem2974217 : term306 = True.
Proof. exact (EQ_MP (@lem2974216) (@lem2974214)). Qed.
Lemma lem2974218 : term305 = True.
Proof. exact (TRANS (@lem2974213) (@lem2974217)). Qed.
Lemma lem2974219 : True = term305.
Proof. exact (SYM (@lem2974218)). Qed.
Lemma lem2974220 : term305.
Proof. exact (EQ_MP (@lem2974219) (@lem0)). Qed.
Lemma lem2974221 : term516.
Proof. exact (@lem2974210 (@lem2974220)). Qed.
Lemma lem2974223 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974224 : term305 = term306.
Proof. exact (@lem2974223 (NUMERAL 0) term86). Qed.
Lemma lem2974225 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974226 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974227 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974226 h1) (fun h1 : term306 = True => @lem2974225)). Qed.
Lemma lem2974228 : term306 = True.
Proof. exact (EQ_MP (@lem2974227) (@lem2974225)). Qed.
Lemma lem2974229 : term305 = True.
Proof. exact (TRANS (@lem2974224) (@lem2974228)). Qed.
Lemma lem2974230 : True = term305.
Proof. exact (SYM (@lem2974229)). Qed.
Lemma lem2974231 : term305.
Proof. exact (EQ_MP (@lem2974230) (@lem0)). Qed.
Lemma lem2974232 : term517.
Proof. exact (@lem2974221 (@lem2974231)). Qed.
Lemma lem2974234 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2974235 : term241 = term242.
Proof. exact (@lem2974234 term86 term86). Qed.
Lemma lem2974236 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974237 : term244 = term86.
Proof. exact (EQ_MP (@lem2974236) (@lem940073)). Qed.
Lemma lem2974238 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974239 : term242 = term169.
Proof. exact (MK_COMB (@lem2974238) (@lem2974237)). Qed.
Lemma lem2974240 : term241 = term169.
Proof. exact (TRANS (@lem2974235) (@lem2974239)). Qed.
Lemma lem2974242 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2974243 : term289 = term292.
Proof. exact (@lem2974242 term86 term86). Qed.
Lemma lem2974244 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974245 : term244 = term86.
Proof. exact (EQ_MP (@lem2974244) (@lem940073)). Qed.
Lemma lem2974246 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974247 : term242 = term169.
Proof. exact (MK_COMB (@lem2974246) (@lem2974245)). Qed.
Lemma lem2974248 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2974249 : term292 = term232.
Proof. exact (MK_COMB (@lem2974248) (@lem2974247)). Qed.
Lemma lem2974250 : term289 = term232.
Proof. exact (TRANS (@lem2974243) (@lem2974249)). Qed.
Lemma lem2974251 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2974252 : term518 = term510.
Proof. exact (MK_COMB (@lem2974251) (@lem2974250)). Qed.
Lemma lem2974253 : term519 = term512.
Proof. exact (MK_COMB (@lem2974252) (@lem2974240)). Qed.
Lemma lem2974255 (m : nat) : (term520 m) = term140.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2974256 : term512 = term140.
Proof. exact (@lem2974255 term86). Qed.
Lemma lem2974257 : term519 = term140.
Proof. exact (TRANS (@lem2974253) (@lem2974256)). Qed.
Lemma lem2974258 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2974259 : term521 = term371.
Proof. exact (MK_COMB (@lem2974258) (@lem2974257)). Qed.
Lemma lem2974260 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2974261 : term522 = term373.
Proof. exact (MK_COMB (@lem2974259) (@lem2974260)). Qed.
Lemma lem2974263 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2974264 : term373 = term140.
Proof. exact (@lem2974263 term86). Qed.
Lemma lem2974265 : term522 = term140.
Proof. exact (TRANS (@lem2974261) (@lem2974264)). Qed.
Lemma lem2974267 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2974268 : term241 = term242.
Proof. exact (@lem2974267 term86 term86). Qed.
Lemma lem2974269 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974270 : term244 = term86.
Proof. exact (EQ_MP (@lem2974269) (@lem940073)). Qed.
Lemma lem2974271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974272 : term242 = term169.
Proof. exact (MK_COMB (@lem2974271) (@lem2974270)). Qed.
Lemma lem2974273 : term241 = term169.
Proof. exact (TRANS (@lem2974268) (@lem2974272)). Qed.
Lemma lem2974274 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem2974275 : term375 = term373.
Proof. exact (MK_COMB (@lem2974274) (@lem2974273)). Qed.
Lemma lem2974277 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2974278 : term373 = term140.
Proof. exact (@lem2974277 term86). Qed.
Lemma lem2974279 : term375 = term140.
Proof. exact (TRANS (@lem2974275) (@lem2974278)). Qed.
Lemma lem2974280 : term140 = term375.
Proof. exact (SYM (@lem2974279)). Qed.
Lemma lem2974281 : term522 = term375.
Proof. exact (TRANS (@lem2974265) (@lem2974280)). Qed.
Lemma lem2974282 : term513 = term229.
Proof. exact (@lem2974232 (@lem2974281)). Qed.
Lemma lem2974283 : term512 = term229.
Proof. exact (TRANS (@lem2974198) (@lem2974282)). Qed.
Lemma lem2974285 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2974286 : term229 = term140.
Proof. exact (@lem2974285 term140). Qed.
Lemma lem2974287 : term512 = term140.
Proof. exact (TRANS (@lem2974283) (@lem2974286)). Qed.
Lemma lem2974288 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2974289 : term523 = term371.
Proof. exact (MK_COMB (@lem2974288) (@lem2974287)). Qed.
Lemma lem2974290 (_31796 : int) : (real_of_int _31796) = (real_of_int _31796).
Proof. exact (eq_refl (real_of_int _31796)). Qed.
Lemma lem2974291 (_31796 : int) : (term509 _31796) = (term524 _31796).
Proof. exact (MK_COMB (@lem2974289) (@lem2974290 _31796)). Qed.
Lemma lem2974292 (_31796 : int) : (term562 _31796) = (term524 _31796).
Proof. exact (TRANS (@lem2974189 _31796) (@lem2974291 _31796)). Qed.
Lemma lem2974293 (_31796 : int) : (term524 _31796) = term140.
Proof. exact (@lem1982719 (real_of_int _31796)). Qed.
Lemma lem2974294 (_31796 : int) : (term562 _31796) = term140.
Proof. exact (TRANS (@lem2974292 _31796) (@lem2974293 _31796)). Qed.
Lemma lem2974295 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2974296 (_31796 : int) : (term563 _31796) = term526.
Proof. exact (MK_COMB (@lem2974295) (@lem2974294 _31796)). Qed.
Lemma lem2974298 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2974299 : term270 = term273.
Proof. exact (@lem2974298 term2). Qed.
Lemma lem2974301 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2974302 : term169 = term288.
Proof. exact (@lem2974301 term86). Qed.
Lemma lem2974303 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2974304 : term359 = term360.
Proof. exact (MK_COMB (@lem2974303) (@lem2974302)). Qed.
Lemma lem2974305 : term742 = term743.
Proof. exact (MK_COMB (@lem2974304) (@lem2974299)). Qed.
Lemma lem2974306 : term744.
Proof. exact (@lem1981473 term169 term169 term270 term169 term232 term169). Qed.
Lemma lem2974308 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974309 : term305 = term306.
Proof. exact (@lem2974308 (NUMERAL 0) term86). Qed.
Lemma lem2974310 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974311 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974312 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974311 h1) (fun h1 : term306 = True => @lem2974310)). Qed.
Lemma lem2974313 : term306 = True.
Proof. exact (EQ_MP (@lem2974312) (@lem2974310)). Qed.
Lemma lem2974314 : term305 = True.
Proof. exact (TRANS (@lem2974309) (@lem2974313)). Qed.
Lemma lem2974315 : True = term305.
Proof. exact (SYM (@lem2974314)). Qed.
Lemma lem2974316 : term305.
Proof. exact (EQ_MP (@lem2974315) (@lem0)). Qed.
Lemma lem2974317 : term745.
Proof. exact (@lem2974306 (@lem2974316)). Qed.
Lemma lem2974319 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974320 : term305 = term306.
Proof. exact (@lem2974319 (NUMERAL 0) term86). Qed.
Lemma lem2974321 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974322 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974323 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974322 h1) (fun h1 : term306 = True => @lem2974321)). Qed.
Lemma lem2974324 : term306 = True.
Proof. exact (EQ_MP (@lem2974323) (@lem2974321)). Qed.
Lemma lem2974325 : term305 = True.
Proof. exact (TRANS (@lem2974320) (@lem2974324)). Qed.
Lemma lem2974326 : True = term305.
Proof. exact (SYM (@lem2974325)). Qed.
Lemma lem2974327 : term305.
Proof. exact (EQ_MP (@lem2974326) (@lem0)). Qed.
Lemma lem2974328 : term746.
Proof. exact (@lem2974317 (@lem2974327)). Qed.
Lemma lem2974330 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974331 : term305 = term306.
Proof. exact (@lem2974330 (NUMERAL 0) term86). Qed.
Lemma lem2974332 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974333 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974334 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974333 h1) (fun h1 : term306 = True => @lem2974332)). Qed.
Lemma lem2974335 : term306 = True.
Proof. exact (EQ_MP (@lem2974334) (@lem2974332)). Qed.
Lemma lem2974336 : term305 = True.
Proof. exact (TRANS (@lem2974331) (@lem2974335)). Qed.
Lemma lem2974337 : True = term305.
Proof. exact (SYM (@lem2974336)). Qed.
Lemma lem2974338 : term305.
Proof. exact (EQ_MP (@lem2974337) (@lem0)). Qed.
Lemma lem2974339 : term747.
Proof. exact (@lem2974328 (@lem2974338)). Qed.
Lemma lem2974341 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2974342 : term539 = term540.
Proof. exact (@lem2974341 term2 term86). Qed.
Lemma lem2974343 : term313 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem2974344 : (term313 = term27) = (term314 = term2).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem2974345 : term314 = term2.
Proof. exact (EQ_MP (@lem2974344) (@lem2974343)). Qed.
Lemma lem2974346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974347 : term312 = term154.
Proof. exact (MK_COMB (@lem2974346) (@lem2974345)). Qed.
Lemma lem2974348 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2974349 : term540 = term270.
Proof. exact (MK_COMB (@lem2974348) (@lem2974347)). Qed.
Lemma lem2974350 : term539 = term270.
Proof. exact (TRANS (@lem2974342) (@lem2974349)). Qed.
Lemma lem2974352 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2974353 : term241 = term242.
Proof. exact (@lem2974352 term86 term86). Qed.
Lemma lem2974354 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974355 : term244 = term86.
Proof. exact (EQ_MP (@lem2974354) (@lem940073)). Qed.
Lemma lem2974356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974357 : term242 = term169.
Proof. exact (MK_COMB (@lem2974356) (@lem2974355)). Qed.
Lemma lem2974358 : term241 = term169.
Proof. exact (TRANS (@lem2974353) (@lem2974357)). Qed.
Lemma lem2974359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2974360 : term367 = term359.
Proof. exact (MK_COMB (@lem2974359) (@lem2974358)). Qed.
Lemma lem2974361 : term748 = term742.
Proof. exact (MK_COMB (@lem2974360) (@lem2974350)). Qed.
Lemma lem2974364 : term749 = term232.
Proof. exact (@lem1367771 term86 term86). Qed.
Lemma lem2974365 : term318 = term27.
Proof. exact (@lem706885). Qed.
Lemma lem2974366 : (term318 = term27) = (term319 = term2).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term27). Qed.
Lemma lem2974367 : term319 = term2.
Proof. exact (EQ_MP (@lem2974366) (@lem2974365)). Qed.
Lemma lem2974368 : term2 = term319.
Proof. exact (SYM (@lem2974367)). Qed.
Lemma lem2974369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974370 : term154 = term320.
Proof. exact (MK_COMB (@lem2974369) (@lem2974368)). Qed.
Lemma lem2974371 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2974372 : term270 = term750.
Proof. exact (MK_COMB (@lem2974371) (@lem2974370)). Qed.
Lemma lem2974373 : term359 = term359.
Proof. exact (eq_refl term359). Qed.
Lemma lem2974374 : term742 = term749.
Proof. exact (MK_COMB (@lem2974373) (@lem2974372)). Qed.
Lemma lem2974375 : term742 = term232.
Proof. exact (TRANS (@lem2974374) (@lem2974364)). Qed.
Lemma lem2974376 : term748 = term232.
Proof. exact (TRANS (@lem2974361) (@lem2974375)). Qed.
Lemma lem2974377 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2974378 : term751 = term234.
Proof. exact (MK_COMB (@lem2974377) (@lem2974376)). Qed.
Lemma lem2974379 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem2974380 : term752 = term289.
Proof. exact (MK_COMB (@lem2974378) (@lem2974379)). Qed.
Lemma lem2974382 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2974383 : term289 = term292.
Proof. exact (@lem2974382 term86 term86). Qed.
Lemma lem2974384 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974385 : term244 = term86.
Proof. exact (EQ_MP (@lem2974384) (@lem940073)). Qed.
Lemma lem2974386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974387 : term242 = term169.
Proof. exact (MK_COMB (@lem2974386) (@lem2974385)). Qed.
Lemma lem2974388 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2974389 : term292 = term232.
Proof. exact (MK_COMB (@lem2974388) (@lem2974387)). Qed.
Lemma lem2974390 : term289 = term232.
Proof. exact (TRANS (@lem2974383) (@lem2974389)). Qed.
Lemma lem2974391 : term752 = term232.
Proof. exact (TRANS (@lem2974380) (@lem2974390)). Qed.
Lemma lem2974393 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2974394 : term241 = term242.
Proof. exact (@lem2974393 term86 term86). Qed.
Lemma lem2974395 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974396 : term244 = term86.
Proof. exact (EQ_MP (@lem2974395) (@lem940073)). Qed.
Lemma lem2974397 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974398 : term242 = term169.
Proof. exact (MK_COMB (@lem2974397) (@lem2974396)). Qed.
Lemma lem2974399 : term241 = term169.
Proof. exact (TRANS (@lem2974394) (@lem2974398)). Qed.
Lemma lem2974400 : term234 = term234.
Proof. exact (eq_refl term234). Qed.
Lemma lem2974401 : term753 = term289.
Proof. exact (MK_COMB (@lem2974400) (@lem2974399)). Qed.
Lemma lem2974403 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2974404 : term289 = term292.
Proof. exact (@lem2974403 term86 term86). Qed.
Lemma lem2974405 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974406 : term244 = term86.
Proof. exact (EQ_MP (@lem2974405) (@lem940073)). Qed.
Lemma lem2974407 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974408 : term242 = term169.
Proof. exact (MK_COMB (@lem2974407) (@lem2974406)). Qed.
Lemma lem2974409 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2974410 : term292 = term232.
Proof. exact (MK_COMB (@lem2974409) (@lem2974408)). Qed.
Lemma lem2974411 : term289 = term232.
Proof. exact (TRANS (@lem2974404) (@lem2974410)). Qed.
Lemma lem2974412 : term753 = term232.
Proof. exact (TRANS (@lem2974401) (@lem2974411)). Qed.
Lemma lem2974413 : term232 = term753.
Proof. exact (SYM (@lem2974412)). Qed.
Lemma lem2974414 : term752 = term753.
Proof. exact (TRANS (@lem2974391) (@lem2974413)). Qed.
Lemma lem2974415 : term743 = term233.
Proof. exact (@lem2974339 (@lem2974414)). Qed.
Lemma lem2974416 : term742 = term233.
Proof. exact (TRANS (@lem2974305) (@lem2974415)). Qed.
Lemma lem2974418 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2974419 : term233 = term232.
Proof. exact (@lem2974418 term232). Qed.
Lemma lem2974420 : term742 = term232.
Proof. exact (TRANS (@lem2974416) (@lem2974419)). Qed.
Lemma lem2974421 (_31796 : int) : (term741 _31796) = term564.
Proof. exact (MK_COMB (@lem2974296 _31796) (@lem2974420)). Qed.
Lemma lem2974422 (_31796 : int) : (term740 _31796) = term564.
Proof. exact (TRANS (@lem2974188 _31796) (@lem2974421 _31796)). Qed.
Lemma lem2974423 : term564 = term232.
Proof. exact (@lem1982721 term232). Qed.
Lemma lem2974424 (_31796 : int) : (term740 _31796) = term232.
Proof. exact (TRANS (@lem2974422 _31796) (@lem2974423)). Qed.
Lemma lem2974425 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2974426 (_31796 : int) : (term754 _31796) = term566.
Proof. exact (MK_COMB (@lem2974425) (@lem2974424 _31796)). Qed.
Lemma lem2974427 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2974428 (_31796 : int) : (term739 _31796) = term567.
Proof. exact (MK_COMB (@lem2974426 _31796) (@lem2974427)). Qed.
Lemma lem2974429 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : term567.
Proof. exact (EQ_MP (@lem2974428 _31796) (@lem2974187 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974431 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2974432 : term567 = term568.
Proof. exact (@lem2974431 term140 term232). Qed.
Lemma lem2974434 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2974435 : term232 = term233.
Proof. exact (@lem2974434 term86). Qed.
Lemma lem2974437 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2974438 : term140 = term229.
Proof. exact (@lem2974437 (NUMERAL 0)). Qed.
Lemma lem2974439 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2974440 : term142 = term569.
Proof. exact (MK_COMB (@lem2974439) (@lem2974438)). Qed.
Lemma lem2974441 : term568 = term570.
Proof. exact (MK_COMB (@lem2974440) (@lem2974435)). Qed.
Lemma lem2974442 : term571.
Proof. exact (@lem1980026 term140 term169 term232 term169). Qed.
Lemma lem2974444 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974445 : term305 = term306.
Proof. exact (@lem2974444 (NUMERAL 0) term86). Qed.
Lemma lem2974446 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974447 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974448 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974447 h1) (fun h1 : term306 = True => @lem2974446)). Qed.
Lemma lem2974449 : term306 = True.
Proof. exact (EQ_MP (@lem2974448) (@lem2974446)). Qed.
Lemma lem2974450 : term305 = True.
Proof. exact (TRANS (@lem2974445) (@lem2974449)). Qed.
Lemma lem2974451 : True = term305.
Proof. exact (SYM (@lem2974450)). Qed.
Lemma lem2974452 : term305.
Proof. exact (EQ_MP (@lem2974451) (@lem0)). Qed.
Lemma lem2974453 : term572.
Proof. exact (@lem2974442 (@lem2974452)). Qed.
Lemma lem2974455 (m : nat) (n : nat) : (term304 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2974456 : term305 = term306.
Proof. exact (@lem2974455 (NUMERAL 0) term86). Qed.
Lemma lem2974457 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974458 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2974459 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974458 h1) (fun h1 : term306 = True => @lem2974457)). Qed.
Lemma lem2974460 : term306 = True.
Proof. exact (EQ_MP (@lem2974459) (@lem2974457)). Qed.
Lemma lem2974461 : term305 = True.
Proof. exact (TRANS (@lem2974456) (@lem2974460)). Qed.
Lemma lem2974462 : True = term305.
Proof. exact (SYM (@lem2974461)). Qed.
Lemma lem2974463 : term305.
Proof. exact (EQ_MP (@lem2974462) (@lem0)). Qed.
Lemma lem2974464 : term570 = term573.
Proof. exact (@lem2974453 (@lem2974463)). Qed.
Lemma lem2974466 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2974467 : term289 = term292.
Proof. exact (@lem2974466 term86 term86). Qed.
Lemma lem2974468 : (term243 = (BIT1 0)) = (term244 = term86).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2974469 : term244 = term86.
Proof. exact (EQ_MP (@lem2974468) (@lem940073)). Qed.
Lemma lem2974470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2974471 : term242 = term169.
Proof. exact (MK_COMB (@lem2974470) (@lem2974469)). Qed.
Lemma lem2974472 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2974473 : term292 = term232.
Proof. exact (MK_COMB (@lem2974472) (@lem2974471)). Qed.
Lemma lem2974474 : term289 = term232.
Proof. exact (TRANS (@lem2974467) (@lem2974473)). Qed.
Lemma lem2974476 (x : nat) : (term374 x) = term140.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2974477 : term373 = term140.
Proof. exact (@lem2974476 term86). Qed.
Lemma lem2974478 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2974479 : term574 = term142.
Proof. exact (MK_COMB (@lem2974478) (@lem2974477)). Qed.
Lemma lem2974480 : term573 = term568.
Proof. exact (MK_COMB (@lem2974479) (@lem2974474)). Qed.
Lemma lem2974482 (m : nat) (n : nat) : (term575 m n) = (term576 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2974483 : term568 = term577.
Proof. exact (@lem2974482 (NUMERAL 0) term86). Qed.
Lemma lem2974484 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2974485 (h1 : term307 = (BIT1 0)) : (term86 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2974486 : (term307 = (BIT1 0)) = ((term86 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem2974485 h1) (fun h1 : (term86 = (NUMERAL 0)) = False => @lem2974484)). Qed.
Lemma lem2974487 : (term86 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2974486) (@lem2974484)). Qed.
Lemma lem2974488 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2974489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2974490 : term578 = (and True).
Proof. exact (MK_COMB (@lem2974489) (@lem2974488)). Qed.
Lemma lem2974491 : term577 = (True /\ False).
Proof. exact (MK_COMB (@lem2974490) (@lem2974487)). Qed.
Lemma lem2974493 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2974494 : term577 = False.
Proof. exact (TRANS (@lem2974491) (@lem2974493)). Qed.
Lemma lem2974495 : term568 = False.
Proof. exact (TRANS (@lem2974483) (@lem2974494)). Qed.
Lemma lem2974496 : term573 = False.
Proof. exact (TRANS (@lem2974480) (@lem2974495)). Qed.
Lemma lem2974497 : term570 = False.
Proof. exact (TRANS (@lem2974464) (@lem2974496)). Qed.
Lemma lem2974498 : term568 = False.
Proof. exact (TRANS (@lem2974441) (@lem2974497)). Qed.
Lemma lem2974499 : term567 = False.
Proof. exact (TRANS (@lem2974432) (@lem2974498)). Qed.
Lemma lem2974500 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term731 _31796 _31794 _31795) : False.
Proof. exact (EQ_MP (@lem2974499) (@lem2974429 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974501 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term465 _31796 _31794 _31795) : False.
Proof. exact (or_elim (@lem2972374 _31796 _31794 _31795 h1) (fun h0 : term667 _31796 _31794 _31795 => @lem2973600 _31796 _31794 _31795 h0) (fun h0 : term731 _31796 _31794 _31795 => @lem2974500 _31796 _31794 _31795 h0)). Qed.
Lemma lem2974502 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term474 _31796 _31794 _31795) : False.
Proof. exact (or_elim (@lem2970586 _31796 _31794 _31795 h1) (fun h0 : term469 _31796 _31794 _31795 => @lem2972373 _31796 _31794 _31795 h0) (fun h0 : term465 _31796 _31794 _31795 => @lem2974501 _31796 _31794 _31795 h0)). Qed.
Lemma lem2974504 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term474 _31796 _31794 _31795) : term474 _31796 _31794 _31795.
Proof. exact (h1). Qed.
Lemma lem2974505 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term474 _31796 _31794 _31795) : (term474 _31796 _31794 _31795) = False.
Proof. exact (prop_ext (fun h2 : term474 _31796 _31794 _31795 => @lem2974502 _31796 _31794 _31795 h1) (fun h2 : False => @lem2974504 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974506 (_31796 : int) (_31794 : int) (_31795 : int) (h1 : term474 _31796 _31794 _31795) : False.
Proof. exact (EQ_MP (@lem2974505 _31796 _31794 _31795 h1) (@lem2974504 _31796 _31794 _31795 h1)). Qed.
Lemma lem2974507 (_31796 : int) (_31795 : int) (_31794 : int) (h1 : term224 _31796 _31795 _31794) : term224 _31796 _31795 _31794.
Proof. exact (h1). Qed.
Lemma lem2974508 (_31796 : int) (_31795 : int) (_31794 : int) (h1 : term224 _31796 _31795 _31794) : term474 _31796 _31794 _31795.
Proof. exact (EQ_MP (@lem2970564 _31796 _31794 _31795) (@lem2974507 _31796 _31795 _31794 h1)). Qed.
Lemma lem2974509 (_31796 : int) (_31795 : int) (_31794 : int) (h1 : term224 _31796 _31795 _31794) : (term474 _31796 _31794 _31795) = False.
Proof. exact (prop_ext (fun h2 : term474 _31796 _31794 _31795 => @lem2974506 _31796 _31794 _31795 h2) (fun h2 : False => @lem2974508 _31796 _31795 _31794 h1)). Qed.
Lemma lem2974510 (_31796 : int) (_31795 : int) (_31794 : int) (h1 : term224 _31796 _31795 _31794) : False.
Proof. exact (EQ_MP (@lem2974509 _31796 _31795 _31794 h1) (@lem2974508 _31796 _31795 _31794 h1)). Qed.
Lemma lem2974511 (_31796 : int) (_31795 : int) (_31794 : int) : term755 _31796 _31795 _31794.
Proof. exact (fun h0 : term224 _31796 _31795 _31794 => @lem2974510 _31796 _31795 _31794 h0). Qed.
Lemma lem2974512 (_31796 : int) (_31795 : int) (_31794 : int) : term756 _31796 _31795 _31794.
Proof. exact (@lem1386578 (term757 _31796 _31795 _31794)). Qed.
Lemma lem2974515 (_31796 : int) (_31795 : int) (_31794 : int) : term757 _31796 _31795 _31794.
Proof. exact (@lem2974512 _31796 _31795 _31794 (@lem2974511 _31796 _31795 _31794)). Qed.
Lemma lem2974516 (_31796 : int) (_31794 : int) (_31795 : int) : (term222 _31796 _31795 _31794) = (term133 _31796 _31794 _31795).
Proof. exact (SYM (@lem2969276 _31796 _31795 _31794)). Qed.
Lemma lem2974517 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2974518 (_31796 : int) (_31794 : int) (_31795 : int) : (term757 _31796 _31795 _31794) = (term97 _31796 _31794 _31795).
Proof. exact (MK_COMB (@lem2974517) (@lem2974516 _31796 _31794 _31795)). Qed.
Lemma lem2974519 (_31796 : int) (_31794 : int) (_31795 : int) : term97 _31796 _31794 _31795.
Proof. exact (EQ_MP (@lem2974518 _31796 _31794 _31795) (@lem2974515 _31796 _31795 _31794)). Qed.
Lemma lem2974520 (_31796 : int) (_31794 : int) (_31795 : int) : term98 _31796 _31794 _31795.
Proof. exact (EQ_MP (@lem2968931 _31796 _31794 _31795) (@lem2974519 _31796 _31794 _31795)). Qed.
Lemma lem2974521 (r : nat) (n : nat) (q : nat) : term758 r n q.
Proof. exact (@lem2974520 (int_of_num r) (int_of_num n) (int_of_num q)). Qed.
Lemma lem2974522 (r : nat) (n : nat) (q : nat) : term759 r n q.
Proof. exact (@lem2974521 r n q (@lem2968924 n)). Qed.
Lemma lem2974523 (r : nat) (n : nat) (q : nat) : term760 r n q.
Proof. exact (@lem2974522 r n q (@lem2968927 q)). Qed.
Lemma lem2974524 (r : nat) (n : nat) (q : nat) : term90 r n q.
Proof. exact (@lem2974523 r n q (@lem2968930 r)). Qed.
Lemma lem2974525 (n : nat) (q : nat) : term92 n q.
Proof. exact (fun r : nat => @lem2974524 r n q). Qed.
Lemma lem2974526 (n : nat) : term94 n.
Proof. exact (fun q : nat => @lem2974525 n q). Qed.
Lemma lem2974527 (n : nat) : (term94 n) = (term23 n).
Proof. exact (SYM (@lem2968921 n)). Qed.
Lemma lem2974528 (n : nat) : term23 n.
Proof. exact (EQ_MP (@lem2974527 n) (@lem2974526 n)). Qed.
Lemma lem2974539 : term761.
Proof. exact (fun n : nat => @lem2974528 n). Qed.
Lemma lem2974541 (p : Prop) : p = (term762 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2974542 : term763 = term764.
Proof. exact (@lem2974541 term763). Qed.
Lemma lem2974543 : term764 = term763.
Proof. exact (SYM (@lem2974542)). Qed.
Lemma lem2974544 (h1 : term765) : term765.
Proof. exact (h1). Qed.
Lemma lem2974547 (h1 : term766) : term766.
Proof. exact (h1). Qed.
Lemma lem2974548 : term767.
Proof. exact (fun h0 : term766 => @lem2974547 h0). Qed.
Lemma lem2974549 (h1 : term767) : term767.
Proof. exact (h1). Qed.
Lemma lem2974550 (h1 : term766) : term766.
Proof. exact (h1). Qed.
Lemma lem2974551 (h1 : term766) (h2 : term767) : term766.
Proof. exact (@lem2974549 h2 (@lem2974550 h1)). Qed.
Lemma lem2974552 (h1 : term766) : term768.
Proof. exact (fun h0 : term767 => @lem2974551 h1 h0). Qed.
Lemma lem2974553 (h1 : term767) : term767.
Proof. exact (h1). Qed.
Lemma lem2974554 (h1 : term766) (h2 : term767) : term766.
Proof. exact (@lem2974552 h1 (@lem2974553 h2)). Qed.
Lemma lem2974555 (h1 : term767) : term767.
Proof. exact (fun h0 : term766 => @lem2974554 h0 h1). Qed.
Lemma lem2974556 : term769.
Proof. exact (fun h0 : term767 => @lem2974555 h0). Qed.
Lemma lem2974559 : term767.
Proof. exact (@lem2974556 (@lem2974548)). Qed.
Lemma lem2974581 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2974582 : term770 = term771.
Proof. exact (@lem2974581 term761). Qed.
Lemma lem2974633 : term772 = term772.
Proof. exact (eq_refl term772). Qed.
Lemma lem2974640 : term766 = term773.
Proof. exact (MK_COMB (@lem2974633) (@lem2974582)). Qed.
Lemma lem2974645 (n : nat) : (term23 n) = (term23 n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem2974646 : term774 = term774.
Proof. exact (fun_ext (fun n : nat => @lem2974645 n)). Qed.
Lemma lem2974647 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2974648 : term761 = term761.
Proof. exact (MK_COMB (@lem2974647) (@lem2974646)). Qed.
Lemma lem2974649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2974650 : term771 = term771.
Proof. exact (MK_COMB (@lem2974649) (@lem2974648)). Qed.
Lemma lem2974651 (P : nat -> Prop) (n : nat) : (term775 P n) = (term775 P n).
Proof. exact (eq_refl (term775 P n)). Qed.
Lemma lem2974652 (P : nat -> Prop) : (term776 P) = (term776 P).
Proof. exact (fun_ext (fun n : nat => @lem2974651 P n)). Qed.
Lemma lem2974653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2974654 (P : nat -> Prop) : (term777 P) = (term777 P).
Proof. exact (MK_COMB (@lem2974653) (@lem2974652 P)). Qed.
Lemma lem2974655 (P : nat -> Prop) (n : nat) : (term778 P n) = (term778 P n).
Proof. exact (eq_refl (term778 P n)). Qed.
Lemma lem2974656 (P : nat -> Prop) : (term779 P) = (term779 P).
Proof. exact (fun_ext (fun n : nat => @lem2974655 P n)). Qed.
Lemma lem2974657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2974658 (P : nat -> Prop) : (term780 P) = (term780 P).
Proof. exact (MK_COMB (@lem2974657) (@lem2974656 P)). Qed.
Lemma lem2974659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2974660 (P : nat -> Prop) : (term781 P) = (term781 P).
Proof. exact (MK_COMB (@lem2974659) (@lem2974658 P)). Qed.
Lemma lem2974661 (P : nat -> Prop) : (term782 P) = (term782 P).
Proof. exact (MK_COMB (@lem2974660 P) (@lem2974654 P)). Qed.
Lemma lem2974662 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem2974663 (P : nat -> Prop) : (term783 P) = (term783 P).
Proof. exact (fun_ext (fun n : nat => @lem2974662 P n)). Qed.
Lemma lem2974664 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2974665 (P : nat -> Prop) : (term784 P) = (term784 P).
Proof. exact (MK_COMB (@lem2974664) (@lem2974663 P)). Qed.
Lemma lem2974666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2974667 (P : nat -> Prop) : (term785 P) = (term785 P).
Proof. exact (MK_COMB (@lem2974666) (@lem2974665 P)). Qed.
Lemma lem2974668 (P : nat -> Prop) : ((term784 P) = (term782 P)) = ((term784 P) = (term782 P)).
Proof. exact (MK_COMB (@lem2974667 P) (@lem2974661 P)). Qed.
Lemma lem2974669 : term786 = term786.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2974668 P)). Qed.
Lemma lem2974670 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem2974671 : term763 = term763.
Proof. exact (MK_COMB (@lem2974670) (@lem2974669)). Qed.
Lemma lem2974672 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2974673 : term765 = term765.
Proof. exact (MK_COMB (@lem2974672) (@lem2974671)). Qed.
Lemma lem2974674 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2974675 : term772 = term772.
Proof. exact (MK_COMB (@lem2974674) (@lem2974673)). Qed.
Lemma lem2974676 : term773 = term773.
Proof. exact (MK_COMB (@lem2974675) (@lem2974650)). Qed.
Lemma lem2974715 : term766 = term773.
Proof. exact (TRANS (@lem2974640) (@lem2974676)). Qed.
Lemma lem2974716 : term773 = term766.
Proof. exact (SYM (@lem2974715)). Qed.
Lemma lem2974717 (h1 : term765) : term765.
Proof. exact (h1). Qed.
Lemma lem2974718 (h1 : term761) : term761.
Proof. exact (h1). Qed.
Lemma lem2974720 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem2974721 (P : nat -> Prop) : (term787 P) = (term788 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem2974722 (P : nat -> Prop) : (term789 P) = (term790 P).
Proof. exact (@lem2974721 (term783 P)). Qed.
Lemma lem2974723 (P : nat -> Prop) (n : nat) : (term791 P n) = (P n).
Proof. exact (eq_refl (term791 P n)). Qed.
Lemma lem2974724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2974726 (P : nat -> Prop) (n : nat) : (term792 P n) = (term793 P n).
Proof. exact (MK_COMB (@lem2974724) (@lem2974723 P n)). Qed.
Lemma lem2974727 (P : nat -> Prop) : (term794 P) = (term795 P).
Proof. exact (fun_ext (fun n : nat => @lem2974726 P n)). Qed.
Lemma lem2974728 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2974729 (P : nat -> Prop) : (term790 P) = (term788 P).
Proof. exact (MK_COMB (@lem2974728) (@lem2974727 P)). Qed.
Lemma lem2974730 (P : nat -> Prop) : (term789 P) = (term788 P).
Proof. exact (TRANS (@lem2974722 P) (@lem2974729 P)). Qed.
Lemma lem2974731 (P : nat -> Prop) : (term783 P) = (term783 P).
Proof. exact (fun_ext (fun n : nat => @lem2974720 P n)). Qed.
Lemma lem2974732 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2974733 (P : nat -> Prop) : (term784 P) = (term784 P).
Proof. exact (MK_COMB (@lem2974732) (@lem2974731 P)). Qed.
Lemma lem2974735 (P : nat -> Prop) (n : nat) : (term778 P n) = (term778 P n).
Proof. exact (eq_refl (term778 P n)). Qed.
Lemma lem2974736 (P : nat -> Prop) : (term787 P) = (term788 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem2974737 (P : nat -> Prop) : (term796 P) = (term797 P).
Proof. exact (@lem2974736 (term779 P)). Qed.
Lemma lem2974738 (P : nat -> Prop) (n : nat) : (term798 P n) = (term778 P n).
Proof. exact (eq_refl (term798 P n)). Qed.
Lemma lem2974739 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2974741 (P : nat -> Prop) (n : nat) : (term799 P n) = (term800 P n).
Proof. exact (MK_COMB (@lem2974739) (@lem2974738 P n)). Qed.
Lemma lem2974742 (P : nat -> Prop) : (term801 P) = (term802 P).
Proof. exact (fun_ext (fun n : nat => @lem2974741 P n)). Qed.
Lemma lem2974743 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2974744 (P : nat -> Prop) : (term797 P) = (term803 P).
Proof. exact (MK_COMB (@lem2974743) (@lem2974742 P)). Qed.
Lemma lem2974745 (P : nat -> Prop) : (term796 P) = (term803 P).
Proof. exact (TRANS (@lem2974737 P) (@lem2974744 P)). Qed.
Lemma lem2974746 (P : nat -> Prop) : (term779 P) = (term779 P).
Proof. exact (fun_ext (fun n : nat => @lem2974735 P n)). Qed.
Lemma lem2974747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2974748 (P : nat -> Prop) : (term780 P) = (term780 P).
Proof. exact (MK_COMB (@lem2974747) (@lem2974746 P)). Qed.
Lemma lem2974750 (P : nat -> Prop) (n : nat) : (term775 P n) = (term775 P n).
Proof. exact (eq_refl (term775 P n)). Qed.
Lemma lem2974751 (P : nat -> Prop) : (term787 P) = (term788 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem2974752 (P : nat -> Prop) : (term804 P) = (term805 P).
Proof. exact (@lem2974751 (term776 P)). Qed.
Lemma lem2974753 (P : nat -> Prop) (n : nat) : (term806 P n) = (term775 P n).
Proof. exact (eq_refl (term806 P n)). Qed.
Lemma lem2974754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2974756 (P : nat -> Prop) (n : nat) : (term807 P n) = (term808 P n).
Proof. exact (MK_COMB (@lem2974754) (@lem2974753 P n)). Qed.
Lemma lem2974757 (P : nat -> Prop) : (term809 P) = (term810 P).
Proof. exact (fun_ext (fun n : nat => @lem2974756 P n)). Qed.
Lemma lem2974758 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2974759 (P : nat -> Prop) : (term805 P) = (term811 P).
Proof. exact (MK_COMB (@lem2974758) (@lem2974757 P)). Qed.
Lemma lem2974760 (P : nat -> Prop) : (term804 P) = (term811 P).
Proof. exact (TRANS (@lem2974752 P) (@lem2974759 P)). Qed.
Lemma lem2974761 (P : nat -> Prop) : (term776 P) = (term776 P).
Proof. exact (fun_ext (fun n : nat => @lem2974750 P n)). Qed.
Lemma lem2974762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2974763 (P : nat -> Prop) : (term777 P) = (term777 P).
Proof. exact (MK_COMB (@lem2974762) (@lem2974761 P)). Qed.
Lemma lem2974764 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2974765 (P : nat -> Prop) : (term812 P) = (term813 P).
Proof. exact (MK_COMB (@lem2974764) (@lem2974745 P)). Qed.
Lemma lem2974766 (P : nat -> Prop) : (term814 P) = (term815 P).
Proof. exact (MK_COMB (@lem2974765 P) (@lem2974760 P)). Qed.
Lemma lem2974767 (P : nat -> Prop) : (term816 P) = (term814 P).
Proof. exact (@lem17045 (term780 P) (term777 P)). Qed.
Lemma lem2974768 (P : nat -> Prop) : (term816 P) = (term815 P).
Proof. exact (TRANS (@lem2974767 P) (@lem2974766 P)). Qed.
Lemma lem2974769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2974770 (P : nat -> Prop) : (term781 P) = (term781 P).
Proof. exact (MK_COMB (@lem2974769) (@lem2974748 P)). Qed.
Lemma lem2974771 (P : nat -> Prop) : (term782 P) = (term782 P).
Proof. exact (MK_COMB (@lem2974770 P) (@lem2974763 P)). Qed.
Lemma lem2974772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2974773 (P : nat -> Prop) : (term817 P) = (term818 P).
Proof. exact (MK_COMB (@lem2974772) (@lem2974730 P)). Qed.
Lemma lem2974774 (P : nat -> Prop) : (term819 P) = (term820 P).
Proof. exact (MK_COMB (@lem2974773 P) (@lem2974771 P)). Qed.
Lemma lem2974775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2974776 (P : nat -> Prop) : (term821 P) = (term821 P).
Proof. exact (MK_COMB (@lem2974775) (@lem2974733 P)). Qed.
Lemma lem2974777 (P : nat -> Prop) : (term822 P) = (term823 P).
Proof. exact (MK_COMB (@lem2974776 P) (@lem2974768 P)). Qed.
Lemma lem2974778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2974779 (P : nat -> Prop) : (term824 P) = (term825 P).
Proof. exact (MK_COMB (@lem2974778) (@lem2974777 P)). Qed.
Lemma lem2974780 (P : nat -> Prop) : (term826 P) = (term827 P).
Proof. exact (MK_COMB (@lem2974779 P) (@lem2974774 P)). Qed.
Lemma lem2974781 (P : nat -> Prop) : (term828 P) = (term826 P).
Proof. exact (@lem17646 (term784 P) (term782 P)). Qed.
Lemma lem2974782 (P : nat -> Prop) : (term828 P) = (term827 P).
Proof. exact (TRANS (@lem2974781 P) (@lem2974780 P)). Qed.
Lemma lem2974783 (P : type993) : (term829 P) = (term830 P).
Proof. exact (@lem18392 (nat -> Prop) P). Qed.
Lemma lem2974784 : term765 = term831.
Proof. exact (@lem2974783 term786). Qed.
Lemma lem2974785 (P : nat -> Prop) : (term832 P) = ((term784 P) = (term782 P)).
Proof. exact (eq_refl (term832 P)). Qed.
Lemma lem2974786 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2974787 (P : nat -> Prop) : (term833 P) = (term828 P).
Proof. exact (MK_COMB (@lem2974786) (@lem2974785 P)). Qed.
Lemma lem2974788 (P : nat -> Prop) : (term833 P) = (term827 P).
Proof. exact (TRANS (@lem2974787 P) (@lem2974782 P)). Qed.
Lemma lem2974789 : term834 = term835.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2974788 P)). Qed.
Lemma lem2974790 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2974791 : term831 = term836.
Proof. exact (MK_COMB (@lem2974790) (@lem2974789)). Qed.
Lemma lem2974792 : term765 = term836.
Proof. exact (TRANS (@lem2974784) (@lem2974791)). Qed.
Lemma lem2974794 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term837 A P Q) = (term838 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem2974795 (P : type993) (Q : type993) : (term839 P Q) = (term840 P Q).
Proof. exact (@lem2974794 (nat -> Prop) P Q). Qed.
Lemma lem2974796 : term841 = term842.
Proof. exact (@lem2974795 term843 term844). Qed.
Lemma lem2974797 (P : nat -> Prop) : (term845 P) = (term823 P).
Proof. exact (eq_refl (term845 P)). Qed.
Lemma lem2974798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2974799 (P : nat -> Prop) : (term846 P) = (term825 P).
Proof. exact (MK_COMB (@lem2974798) (@lem2974797 P)). Qed.
Lemma lem2974800 (P : nat -> Prop) : (term847 P) = (term820 P).
Proof. exact (eq_refl (term847 P)). Qed.
Lemma lem2974801 (P : nat -> Prop) : (term848 P) = (term827 P).
Proof. exact (MK_COMB (@lem2974799 P) (@lem2974800 P)). Qed.
Lemma lem2974802 : term849 = term835.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2974801 P)). Qed.
Lemma lem2974803 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2974804 : term841 = term836.
Proof. exact (MK_COMB (@lem2974803) (@lem2974802)). Qed.
Lemma lem2974805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2974806 : term850 = term851.
Proof. exact (MK_COMB (@lem2974805) (@lem2974804)). Qed.
Lemma lem2974807 (P : nat -> Prop) : (term845 P) = (term823 P).
Proof. exact (eq_refl (term845 P)). Qed.
Lemma lem2974808 : term852 = term843.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2974807 P)). Qed.
Lemma lem2974809 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2974810 : term853 = term854.
Proof. exact (MK_COMB (@lem2974809) (@lem2974808)). Qed.
Lemma lem2974811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2974812 : term855 = term856.
Proof. exact (MK_COMB (@lem2974811) (@lem2974810)). Qed.
Lemma lem2974813 (P : nat -> Prop) : (term847 P) = (term820 P).
Proof. exact (eq_refl (term847 P)). Qed.
Lemma lem2974814 : term857 = term844.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2974813 P)). Qed.
Lemma lem2974815 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2974816 : term858 = term859.
Proof. exact (MK_COMB (@lem2974815) (@lem2974814)). Qed.
Lemma lem2974817 : term842 = term860.
Proof. exact (MK_COMB (@lem2974812) (@lem2974816)). Qed.
Lemma lem2974818 : (term841 = term842) = (term836 = term860).
Proof. exact (MK_COMB (@lem2974806) (@lem2974817)). Qed.
Lemma lem2974819 : term836 = term860.
Proof. exact (EQ_MP (@lem2974818) (@lem2974796)). Qed.
Lemma lem2974941 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term838 A P Q) = (term837 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2974942 (P : nat -> Prop) (Q : nat -> Prop) : (term861 P Q) = (term862 P Q).
Proof. exact (@lem2974941 nat P Q). Qed.
Lemma lem2974943 (P : nat -> Prop) : (term863 P) = (term864 P).
Proof. exact (@lem2974942 (term802 P) (term810 P)). Qed.
Lemma lem2974944 (P : nat -> Prop) (n : nat) : (term865 P n) = (term800 P n).
Proof. exact (eq_refl (term865 P n)). Qed.
Lemma lem2974945 (P : nat -> Prop) : (term866 P) = (term802 P).
Proof. exact (fun_ext (fun n : nat => @lem2974944 P n)). Qed.
Lemma lem2974946 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2974947 (P : nat -> Prop) : (term867 P) = (term803 P).
Proof. exact (MK_COMB (@lem2974946) (@lem2974945 P)). Qed.
Lemma lem2974948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2974949 (P : nat -> Prop) : (term868 P) = (term813 P).
Proof. exact (MK_COMB (@lem2974948) (@lem2974947 P)). Qed.
Lemma lem2974950 (P : nat -> Prop) (n : nat) : (term869 P n) = (term808 P n).
Proof. exact (eq_refl (term869 P n)). Qed.
Lemma lem2974951 (P : nat -> Prop) : (term870 P) = (term810 P).
Proof. exact (fun_ext (fun n : nat => @lem2974950 P n)). Qed.
Lemma lem2974952 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2974953 (P : nat -> Prop) : (term871 P) = (term811 P).
Proof. exact (MK_COMB (@lem2974952) (@lem2974951 P)). Qed.
Lemma lem2974954 (P : nat -> Prop) : (term863 P) = (term815 P).
Proof. exact (MK_COMB (@lem2974949 P) (@lem2974953 P)). Qed.
Lemma lem2974955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2974956 (P : nat -> Prop) : (term872 P) = (term873 P).
Proof. exact (MK_COMB (@lem2974955) (@lem2974954 P)). Qed.
Lemma lem2974957 (P : nat -> Prop) (n : nat) : (term865 P n) = (term800 P n).
Proof. exact (eq_refl (term865 P n)). Qed.
Lemma lem2974958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2974959 (P : nat -> Prop) (n : nat) : (term874 P n) = (term875 P n).
Proof. exact (MK_COMB (@lem2974958) (@lem2974957 P n)). Qed.
Lemma lem2974960 (P : nat -> Prop) (n : nat) : (term869 P n) = (term808 P n).
Proof. exact (eq_refl (term869 P n)). Qed.
Lemma lem2974961 (P : nat -> Prop) (n : nat) : (term876 P n) = (term877 P n).
Proof. exact (MK_COMB (@lem2974959 P n) (@lem2974960 P n)). Qed.
Lemma lem2974962 (P : nat -> Prop) : (term878 P) = (term879 P).
Proof. exact (fun_ext (fun n : nat => @lem2974961 P n)). Qed.
Lemma lem2974963 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2974964 (P : nat -> Prop) : (term864 P) = (term880 P).
Proof. exact (MK_COMB (@lem2974963) (@lem2974962 P)). Qed.
Lemma lem2974965 (P : nat -> Prop) : ((term863 P) = (term864 P)) = ((term815 P) = (term880 P)).
Proof. exact (MK_COMB (@lem2974956 P) (@lem2974964 P)). Qed.
Lemma lem2974966 (P : nat -> Prop) : (term815 P) = (term880 P).
Proof. exact (EQ_MP (@lem2974965 P) (@lem2974943 P)). Qed.
Lemma lem2974967 (P : nat -> Prop) : (term821 P) = (term821 P).
Proof. exact (eq_refl (term821 P)). Qed.
Lemma lem2974968 (P : nat -> Prop) : (term823 P) = (term881 P).
Proof. exact (MK_COMB (@lem2974967 P) (@lem2974966 P)). Qed.
Lemma lem2974970 {A : Type'} (P : Prop) (Q : A -> Prop) : (term882 A P Q) = (term883 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2974971 (P : Prop) (Q : nat -> Prop) : (term884 P Q) = (term885 P Q).
Proof. exact (@lem2974970 nat P Q). Qed.
Lemma lem2974972 (P : nat -> Prop) : (term886 P) = (term887 P).
Proof. exact (@lem2974971 (term784 P) (term879 P)). Qed.
Lemma lem2974973 (P : nat -> Prop) (n : nat) : (term888 P n) = (term877 P n).
Proof. exact (eq_refl (term888 P n)). Qed.
Lemma lem2974974 (P : nat -> Prop) : (term889 P) = (term879 P).
Proof. exact (fun_ext (fun n : nat => @lem2974973 P n)). Qed.
Lemma lem2974975 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2974976 (P : nat -> Prop) : (term890 P) = (term880 P).
Proof. exact (MK_COMB (@lem2974975) (@lem2974974 P)). Qed.
Lemma lem2974977 (P : nat -> Prop) : (term821 P) = (term821 P).
Proof. exact (eq_refl (term821 P)). Qed.
Lemma lem2974978 (P : nat -> Prop) : (term886 P) = (term881 P).
Proof. exact (MK_COMB (@lem2974977 P) (@lem2974976 P)). Qed.
Lemma lem2974979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2974980 (P : nat -> Prop) : (term891 P) = (term892 P).
Proof. exact (MK_COMB (@lem2974979) (@lem2974978 P)). Qed.
Lemma lem2974981 (P : nat -> Prop) (n : nat) : (term888 P n) = (term877 P n).
Proof. exact (eq_refl (term888 P n)). Qed.
Lemma lem2974982 (P : nat -> Prop) : (term821 P) = (term821 P).
Proof. exact (eq_refl (term821 P)). Qed.
Lemma lem2974983 (P : nat -> Prop) (n : nat) : (term893 P n) = (term894 P n).
Proof. exact (MK_COMB (@lem2974982 P) (@lem2974981 P n)). Qed.
Lemma lem2974984 (P : nat -> Prop) : (term895 P) = (term896 P).
Proof. exact (fun_ext (fun n : nat => @lem2974983 P n)). Qed.
Lemma lem2974985 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2974986 (P : nat -> Prop) : (term887 P) = (term897 P).
Proof. exact (MK_COMB (@lem2974985) (@lem2974984 P)). Qed.
Lemma lem2974987 (P : nat -> Prop) : ((term886 P) = (term887 P)) = ((term881 P) = (term897 P)).
Proof. exact (MK_COMB (@lem2974980 P) (@lem2974986 P)). Qed.
Lemma lem2974988 (P : nat -> Prop) : (term881 P) = (term897 P).
Proof. exact (EQ_MP (@lem2974987 P) (@lem2974972 P)). Qed.
Lemma lem2974989 (P : nat -> Prop) : (term823 P) = (term897 P).
Proof. exact (TRANS (@lem2974968 P) (@lem2974988 P)). Qed.
Lemma lem2974990 : term843 = term898.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2974989 P)). Qed.
Lemma lem2974991 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2974992 : term854 = term899.
Proof. exact (MK_COMB (@lem2974991) (@lem2974990)). Qed.
Lemma lem2974993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2974994 : term856 = term900.
Proof. exact (MK_COMB (@lem2974993) (@lem2974992)). Qed.
Lemma lem2974996 {A : Type'} (P : A -> Prop) (Q : Prop) : (term901 A P Q) = (term902 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem2974997 (P : nat -> Prop) (Q : Prop) : (term903 P Q) = (term904 P Q).
Proof. exact (@lem2974996 nat P Q). Qed.
Lemma lem2974998 (P : nat -> Prop) : (term905 P) = (term906 P).
Proof. exact (@lem2974997 (term795 P) (term782 P)). Qed.
Lemma lem2974999 (P : nat -> Prop) (n : nat) : (term907 P n) = (term793 P n).
Proof. exact (eq_refl (term907 P n)). Qed.
Lemma lem2975000 (P : nat -> Prop) : (term908 P) = (term795 P).
Proof. exact (fun_ext (fun n : nat => @lem2974999 P n)). Qed.
Lemma lem2975001 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2975002 (P : nat -> Prop) : (term909 P) = (term788 P).
Proof. exact (MK_COMB (@lem2975001) (@lem2975000 P)). Qed.
Lemma lem2975003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2975004 (P : nat -> Prop) : (term910 P) = (term818 P).
Proof. exact (MK_COMB (@lem2975003) (@lem2975002 P)). Qed.
Lemma lem2975005 (P : nat -> Prop) : (term782 P) = (term782 P).
Proof. exact (eq_refl (term782 P)). Qed.
Lemma lem2975006 (P : nat -> Prop) : (term905 P) = (term820 P).
Proof. exact (MK_COMB (@lem2975004 P) (@lem2975005 P)). Qed.
Lemma lem2975007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2975008 (P : nat -> Prop) : (term911 P) = (term912 P).
Proof. exact (MK_COMB (@lem2975007) (@lem2975006 P)). Qed.
Lemma lem2975009 (P : nat -> Prop) (n : nat) : (term907 P n) = (term793 P n).
Proof. exact (eq_refl (term907 P n)). Qed.
Lemma lem2975010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2975011 (P : nat -> Prop) (n : nat) : (term913 P n) = (term914 P n).
Proof. exact (MK_COMB (@lem2975010) (@lem2975009 P n)). Qed.
Lemma lem2975012 (P : nat -> Prop) : (term782 P) = (term782 P).
Proof. exact (eq_refl (term782 P)). Qed.
Lemma lem2975013 (n : nat) (P : nat -> Prop) : (term915 n P) = (term916 n P).
Proof. exact (MK_COMB (@lem2975011 P n) (@lem2975012 P)). Qed.
Lemma lem2975014 (P : nat -> Prop) : (term917 P) = (term918 P).
Proof. exact (fun_ext (fun n : nat => @lem2975013 n P)). Qed.
Lemma lem2975015 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2975016 (P : nat -> Prop) : (term906 P) = (term919 P).
Proof. exact (MK_COMB (@lem2975015) (@lem2975014 P)). Qed.
Lemma lem2975017 (P : nat -> Prop) : ((term905 P) = (term906 P)) = ((term820 P) = (term919 P)).
Proof. exact (MK_COMB (@lem2975008 P) (@lem2975016 P)). Qed.
Lemma lem2975018 (P : nat -> Prop) : (term820 P) = (term919 P).
Proof. exact (EQ_MP (@lem2975017 P) (@lem2974998 P)). Qed.
Lemma lem2975019 : term844 = term920.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2975018 P)). Qed.
Lemma lem2975020 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2975021 : term859 = term921.
Proof. exact (MK_COMB (@lem2975020) (@lem2975019)). Qed.
Lemma lem2975022 : term860 = term922.
Proof. exact (MK_COMB (@lem2974994) (@lem2975021)). Qed.
Lemma lem2975024 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term838 A P Q) = (term837 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2975025 (P : type993) (Q : type993) : (term840 P Q) = (term839 P Q).
Proof. exact (@lem2975024 (nat -> Prop) P Q). Qed.
Lemma lem2975026 : term923 = term924.
Proof. exact (@lem2975025 term898 term920). Qed.
Lemma lem2975027 (P : nat -> Prop) : (term925 P) = (term897 P).
Proof. exact (eq_refl (term925 P)). Qed.
Lemma lem2975028 : term926 = term898.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2975027 P)). Qed.
Lemma lem2975029 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2975030 : term927 = term899.
Proof. exact (MK_COMB (@lem2975029) (@lem2975028)). Qed.
Lemma lem2975031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2975032 : term928 = term900.
Proof. exact (MK_COMB (@lem2975031) (@lem2975030)). Qed.
Lemma lem2975033 (P : nat -> Prop) : (term929 P) = (term919 P).
Proof. exact (eq_refl (term929 P)). Qed.
Lemma lem2975034 : term930 = term920.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2975033 P)). Qed.
Lemma lem2975035 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2975036 : term931 = term921.
Proof. exact (MK_COMB (@lem2975035) (@lem2975034)). Qed.
Lemma lem2975037 : term923 = term922.
Proof. exact (MK_COMB (@lem2975032) (@lem2975036)). Qed.
Lemma lem2975038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2975039 : term932 = term933.
Proof. exact (MK_COMB (@lem2975038) (@lem2975037)). Qed.
Lemma lem2975040 (P : nat -> Prop) : (term925 P) = (term897 P).
Proof. exact (eq_refl (term925 P)). Qed.
Lemma lem2975041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2975042 (P : nat -> Prop) : (term934 P) = (term935 P).
Proof. exact (MK_COMB (@lem2975041) (@lem2975040 P)). Qed.
Lemma lem2975043 (P : nat -> Prop) : (term929 P) = (term919 P).
Proof. exact (eq_refl (term929 P)). Qed.
Lemma lem2975044 (P : nat -> Prop) : (term936 P) = (term937 P).
Proof. exact (MK_COMB (@lem2975042 P) (@lem2975043 P)). Qed.
Lemma lem2975045 : term938 = term939.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2975044 P)). Qed.
Lemma lem2975046 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2975047 : term924 = term940.
Proof. exact (MK_COMB (@lem2975046) (@lem2975045)). Qed.
Lemma lem2975048 : (term923 = term924) = (term922 = term940).
Proof. exact (MK_COMB (@lem2975039) (@lem2975047)). Qed.
Lemma lem2975049 : term922 = term940.
Proof. exact (EQ_MP (@lem2975048) (@lem2975026)). Qed.
Lemma lem2975051 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term838 A P Q) = (term837 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2975052 (P : nat -> Prop) (Q : nat -> Prop) : (term861 P Q) = (term862 P Q).
Proof. exact (@lem2975051 nat P Q). Qed.
Lemma lem2975053 (P : nat -> Prop) : (term941 P) = (term942 P).
Proof. exact (@lem2975052 (term896 P) (term918 P)). Qed.
Lemma lem2975054 (P : nat -> Prop) (n : nat) : (term943 P n) = (term894 P n).
Proof. exact (eq_refl (term943 P n)). Qed.
Lemma lem2975055 (P : nat -> Prop) : (term944 P) = (term896 P).
Proof. exact (fun_ext (fun n : nat => @lem2975054 P n)). Qed.
Lemma lem2975056 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2975057 (P : nat -> Prop) : (term945 P) = (term897 P).
Proof. exact (MK_COMB (@lem2975056) (@lem2975055 P)). Qed.
Lemma lem2975058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2975059 (P : nat -> Prop) : (term946 P) = (term935 P).
Proof. exact (MK_COMB (@lem2975058) (@lem2975057 P)). Qed.
Lemma lem2975060 (n : nat) (P : nat -> Prop) : (term947 P n) = (term916 n P).
Proof. exact (eq_refl (term947 P n)). Qed.
Lemma lem2975061 (P : nat -> Prop) : (term948 P) = (term918 P).
Proof. exact (fun_ext (fun n : nat => @lem2975060 n P)). Qed.
Lemma lem2975062 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2975063 (P : nat -> Prop) : (term949 P) = (term919 P).
Proof. exact (MK_COMB (@lem2975062) (@lem2975061 P)). Qed.
Lemma lem2975064 (P : nat -> Prop) : (term941 P) = (term937 P).
Proof. exact (MK_COMB (@lem2975059 P) (@lem2975063 P)). Qed.
Lemma lem2975065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2975066 (P : nat -> Prop) : (term950 P) = (term951 P).
Proof. exact (MK_COMB (@lem2975065) (@lem2975064 P)). Qed.
Lemma lem2975067 (P : nat -> Prop) (n : nat) : (term943 P n) = (term894 P n).
Proof. exact (eq_refl (term943 P n)). Qed.
Lemma lem2975068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2975069 (P : nat -> Prop) (n : nat) : (term952 P n) = (term953 P n).
Proof. exact (MK_COMB (@lem2975068) (@lem2975067 P n)). Qed.
Lemma lem2975070 (n : nat) (P : nat -> Prop) : (term947 P n) = (term916 n P).
Proof. exact (eq_refl (term947 P n)). Qed.
Lemma lem2975071 (n : nat) (P : nat -> Prop) : (term954 P n) = (term955 n P).
Proof. exact (MK_COMB (@lem2975069 P n) (@lem2975070 n P)). Qed.
Lemma lem2975072 (P : nat -> Prop) : (term956 P) = (term957 P).
Proof. exact (fun_ext (fun n : nat => @lem2975071 n P)). Qed.
Lemma lem2975073 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2975074 (P : nat -> Prop) : (term942 P) = (term958 P).
Proof. exact (MK_COMB (@lem2975073) (@lem2975072 P)). Qed.
Lemma lem2975075 (P : nat -> Prop) : ((term941 P) = (term942 P)) = ((term937 P) = (term958 P)).
Proof. exact (MK_COMB (@lem2975066 P) (@lem2975074 P)). Qed.
Lemma lem2975076 (P : nat -> Prop) : (term937 P) = (term958 P).
Proof. exact (EQ_MP (@lem2975075 P) (@lem2975053 P)). Qed.
Lemma lem2975077 : term939 = term959.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem2975076 P)). Qed.
Lemma lem2975078 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem2975079 : term940 = term960.
Proof. exact (MK_COMB (@lem2975078) (@lem2975077)). Qed.
Lemma lem2975080 : term922 = term960.
Proof. exact (TRANS (@lem2975049) (@lem2975079)). Qed.
Lemma lem2975081 : term860 = term960.
Proof. exact (TRANS (@lem2975022) (@lem2975080)). Qed.
Lemma lem2975082 : term836 = term960.
Proof. exact (TRANS (@lem2974819) (@lem2975081)). Qed.
Lemma lem2975083 : term765 = term960.
Proof. exact (TRANS (@lem2974792) (@lem2975082)). Qed.
Lemma lem2975084 (h1 : term765) : term960.
Proof. exact (EQ_MP (@lem2975083) (@lem2974717 h1)). Qed.
Lemma lem2975089 (n : nat) : (term23 n) = (term23 n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem2975090 : term774 = term774.
Proof. exact (fun_ext (fun n : nat => @lem2975089 n)). Qed.
Lemma lem2975091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975144 : term761 = term761.
Proof. exact (MK_COMB (@lem2975091) (@lem2975090)). Qed.
Lemma lem2975145 (h1 : term761) : term761.
Proof. exact (EQ_MP (@lem2975144) (@lem2974718 h1)). Qed.
Lemma lem2975146 (P : nat -> Prop) (h1 : term958 P) : term958 P.
Proof. exact (h1). Qed.
Lemma lem2975147 (n : nat) (P : nat -> Prop) (h1 : term955 n P) : term955 n P.
Proof. exact (h1). Qed.
Lemma lem2975208 (n : nat) : (term23 n) = (term23 n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem2975209 : term774 = term774.
Proof. exact (fun_ext (fun n : nat => @lem2975208 n)). Qed.
Lemma lem2975210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975211 : term761 = term761.
Proof. exact (MK_COMB (@lem2975210) (@lem2975209)). Qed.
Lemma lem2975212 (h1 : term761) : term761.
Proof. exact (EQ_MP (@lem2975211) (@lem2975145 h1)). Qed.
Lemma lem2975233 (P : nat -> Prop) (n : nat) : (term775 P n) = (term775 P n).
Proof. exact (eq_refl (term775 P n)). Qed.
Lemma lem2975234 (P : nat -> Prop) : (term776 P) = (term776 P).
Proof. exact (fun_ext (fun n : nat => @lem2975233 P n)). Qed.
Lemma lem2975235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975236 (P : nat -> Prop) : (term777 P) = (term777 P).
Proof. exact (MK_COMB (@lem2975235) (@lem2975234 P)). Qed.
Lemma lem2975249 (P : nat -> Prop) (n : nat) : (term778 P n) = (term778 P n).
Proof. exact (eq_refl (term778 P n)). Qed.
Lemma lem2975250 (P : nat -> Prop) : (term779 P) = (term779 P).
Proof. exact (fun_ext (fun n : nat => @lem2975249 P n)). Qed.
Lemma lem2975251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975252 (P : nat -> Prop) : (term780 P) = (term780 P).
Proof. exact (MK_COMB (@lem2975251) (@lem2975250 P)). Qed.
Lemma lem2975253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2975254 (P : nat -> Prop) : (term781 P) = (term781 P).
Proof. exact (MK_COMB (@lem2975253) (@lem2975252 P)). Qed.
Lemma lem2975255 (P : nat -> Prop) : (term782 P) = (term782 P).
Proof. exact (MK_COMB (@lem2975254 P) (@lem2975236 P)). Qed.
Lemma lem2975262 (P : nat -> Prop) (n : nat) : (term914 P n) = (term914 P n).
Proof. exact (eq_refl (term914 P n)). Qed.
Lemma lem2975263 (n : nat) (P : nat -> Prop) : (term916 n P) = (term916 n P).
Proof. exact (MK_COMB (@lem2975262 P n) (@lem2975255 P)). Qed.
Lemma lem2975304 (P : nat -> Prop) (n : nat) : (term877 P n) = (term877 P n).
Proof. exact (eq_refl (term877 P n)). Qed.
Lemma lem2975307 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem2975308 (P : nat -> Prop) : (term783 P) = (term783 P).
Proof. exact (fun_ext (fun n : nat => @lem2975307 P n)). Qed.
Lemma lem2975309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975310 (P : nat -> Prop) : (term784 P) = (term784 P).
Proof. exact (MK_COMB (@lem2975309) (@lem2975308 P)). Qed.
Lemma lem2975311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2975312 (P : nat -> Prop) : (term821 P) = (term821 P).
Proof. exact (MK_COMB (@lem2975311) (@lem2975310 P)). Qed.
Lemma lem2975313 (P : nat -> Prop) (n : nat) : (term894 P n) = (term894 P n).
Proof. exact (MK_COMB (@lem2975312 P) (@lem2975304 P n)). Qed.
Lemma lem2975314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2975315 (P : nat -> Prop) (n : nat) : (term953 P n) = (term953 P n).
Proof. exact (MK_COMB (@lem2975314) (@lem2975313 P n)). Qed.
Lemma lem2975316 (n : nat) (P : nat -> Prop) : (term955 n P) = (term955 n P).
Proof. exact (MK_COMB (@lem2975315 P n) (@lem2975263 n P)). Qed.
Lemma lem2975317 (n : nat) (P : nat -> Prop) (h1 : term955 n P) : term955 n P.
Proof. exact (EQ_MP (@lem2975316 n P) (@lem2975147 n P h1)). Qed.
Lemma lem2975318 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term894 P n.
Proof. exact (h1). Qed.
Lemma lem2975319 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term916 n P.
Proof. exact (h1). Qed.
Lemma lem2975320 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term877 P n.
Proof. exact (proj2 (@lem2975318 P n h1)). Qed.
Lemma lem2975321 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term784 P.
Proof. exact (proj1 (@lem2975318 P n h1)). Qed.
Lemma lem2975324 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term782 P.
Proof. exact (proj2 (@lem2975319 n P h1)). Qed.
Lemma lem2975326 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term777 P.
Proof. exact (proj2 (@lem2975324 n P h1)). Qed.
Lemma lem2975327 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term780 P.
Proof. exact (proj1 (@lem2975324 n P h1)). Qed.
Lemma lem2975342 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem2975343 (P : nat -> Prop) : (term783 P) = (term783 P).
Proof. exact (fun_ext (fun n : nat => @lem2975342 P n)). Qed.
Lemma lem2975344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975346 (P : nat -> Prop) : (term784 P) = (term784 P).
Proof. exact (MK_COMB (@lem2975344) (@lem2975343 P)). Qed.
Lemma lem2975347 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term784 P.
Proof. exact (EQ_MP (@lem2975346 P) (@lem2975321 P n h1)). Qed.
Lemma lem2975351 (P : nat -> Prop) (n : nat) (h1 : term800 P n) : term800 P n.
Proof. exact (h1). Qed.
Lemma lem2975366 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem2975367 (P : nat -> Prop) : (term783 P) = (term783 P).
Proof. exact (fun_ext (fun n : nat => @lem2975366 P n)). Qed.
Lemma lem2975368 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975370 (P : nat -> Prop) : (term784 P) = (term784 P).
Proof. exact (MK_COMB (@lem2975368) (@lem2975367 P)). Qed.
Lemma lem2975371 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term784 P.
Proof. exact (EQ_MP (@lem2975370 P) (@lem2975321 P n h1)). Qed.
Lemma lem2975375 (P : nat -> Prop) (n : nat) (h1 : term808 P n) : term808 P n.
Proof. exact (h1). Qed.
Lemma lem2975383 (n : nat) : (term23 n) = (term23 n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem2975384 : term774 = term774.
Proof. exact (fun_ext (fun n : nat => @lem2975383 n)). Qed.
Lemma lem2975385 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975387 : term761 = term761.
Proof. exact (MK_COMB (@lem2975385) (@lem2975384)). Qed.
Lemma lem2975388 (h1 : term761) : term761.
Proof. exact (EQ_MP (@lem2975387) (@lem2975212 h1)). Qed.
Lemma lem2975394 (P : nat -> Prop) (n : nat) : (term778 P n) = (term778 P n).
Proof. exact (eq_refl (term778 P n)). Qed.
Lemma lem2975395 (P : nat -> Prop) : (term779 P) = (term779 P).
Proof. exact (fun_ext (fun n : nat => @lem2975394 P n)). Qed.
Lemma lem2975396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975398 (P : nat -> Prop) : (term780 P) = (term780 P).
Proof. exact (MK_COMB (@lem2975396) (@lem2975395 P)). Qed.
Lemma lem2975399 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term780 P.
Proof. exact (EQ_MP (@lem2975398 P) (@lem2975327 n P h1)). Qed.
Lemma lem2975401 (P : nat -> Prop) (n : nat) : (term775 P n) = (term775 P n).
Proof. exact (eq_refl (term775 P n)). Qed.
Lemma lem2975402 (P : nat -> Prop) : (term776 P) = (term776 P).
Proof. exact (fun_ext (fun n : nat => @lem2975401 P n)). Qed.
Lemma lem2975403 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2975405 (P : nat -> Prop) : (term777 P) = (term777 P).
Proof. exact (MK_COMB (@lem2975403) (@lem2975402 P)). Qed.
Lemma lem2975406 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term777 P.
Proof. exact (EQ_MP (@lem2975405 P) (@lem2975326 n P h1)). Qed.
Lemma lem2975410 (_31801 : nat) (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term791 P _31801.
Proof. exact (@lem2975347 P n h1 _31801). Qed.
Lemma lem2975411 (P : nat -> Prop) (_31801 : nat) : (term791 P _31801) = (P _31801).
Proof. exact (eq_refl (term791 P _31801)). Qed.
Lemma lem2975416 (_31803 : nat) (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term791 P _31803.
Proof. exact (@lem2975371 P n h1 _31803). Qed.
Lemma lem2975417 (P : nat -> Prop) (_31803 : nat) : (term791 P _31803) = (P _31803).
Proof. exact (eq_refl (term791 P _31803)). Qed.
Lemma lem2975419 (_31804 : nat) (h1 : term761) : term961 _31804.
Proof. exact (@lem2975388 h1 _31804). Qed.
Lemma lem2975420 (_31804 : nat) : (term961 _31804) = (term23 _31804).
Proof. exact (eq_refl (term961 _31804)). Qed.
Lemma lem2975422 (_31805 : nat) (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term798 P _31805.
Proof. exact (@lem2975399 n P h1 _31805). Qed.
Lemma lem2975423 (P : nat -> Prop) (_31805 : nat) : (term798 P _31805) = (term778 P _31805).
Proof. exact (eq_refl (term798 P _31805)). Qed.
Lemma lem2975425 (_31806 : nat) (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term806 P _31806.
Proof. exact (@lem2975406 n P h1 _31806). Qed.
Lemma lem2975426 (P : nat -> Prop) (_31806 : nat) : (term806 P _31806) = (term775 P _31806).
Proof. exact (eq_refl (term806 P _31806)). Qed.
Lemma lem2975437 (P : nat -> Prop) (n : nat) (h1 : term800 P n) : term800 P n.
Proof. exact (h1). Qed.
Lemma lem2975447 (P : nat -> Prop) (n : nat) (h1 : term808 P n) : term808 P n.
Proof. exact (h1). Qed.
Lemma lem2975453 (_31804 : nat) (h1 : term761) : term23 _31804.
Proof. exact (EQ_MP (@lem2975420 _31804) (@lem2975419 _31804 h1)). Qed.
Lemma lem2975455 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term793 P n.
Proof. exact (proj1 (@lem2975319 n P h1)). Qed.
Lemma lem2975544 (_31801 : nat) (P : nat -> Prop) (n : nat) (h1 : term894 P n) : P _31801.
Proof. exact (EQ_MP (@lem2975411 P _31801) (@lem2975410 _31801 P n h1)). Qed.
Lemma lem2975545 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term778 P n.
Proof. exact (@lem2975544 (term45 n) P n h1). Qed.
Lemma lem2975546 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term962 P n.
Proof. exact (fun h0 : term800 P n => @lem2975545 P n h1). Qed.
Lemma lem2975548 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2975549 (P : nat -> Prop) (n : nat) : (term962 P n) = (term778 P n).
Proof. exact (@lem2975548 (term778 P n)). Qed.
Lemma lem2975550 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term778 P n.
Proof. exact (EQ_MP (@lem2975549 P n) (@lem2975546 P n h1)). Qed.
Lemma lem2975553 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2975555 (P : nat -> Prop) (n : nat) : (term800 P n) = (term964 P n).
Proof. exact (@lem2975553 (term778 P n)). Qed.
Lemma lem2975558 (P : nat -> Prop) (n : nat) (h1 : term800 P n) : term964 P n.
Proof. exact (EQ_MP (@lem2975555 P n) (@lem2975437 P n h1)). Qed.
Lemma lem2975561 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : False.
Proof. exact (@lem2975558 P n h1 (@lem2975550 P n h2)). Qed.
Lemma lem2975562 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : term965.
Proof. exact (fun h0 : ~ False => @lem2975561 P n h1 h2). Qed.
Lemma lem2975564 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2975565 : term965 = False.
Proof. exact (@lem2975564 False). Qed.
Lemma lem2975566 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : False.
Proof. exact (EQ_MP (@lem2975565) (@lem2975562 P n h1 h2)). Qed.
Lemma lem2975651 (_31803 : nat) (P : nat -> Prop) (n : nat) (h1 : term894 P n) : P _31803.
Proof. exact (EQ_MP (@lem2975417 P _31803) (@lem2975416 _31803 P n h1)). Qed.
Lemma lem2975652 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term775 P n.
Proof. exact (@lem2975651 (term83 n) P n h1). Qed.
Lemma lem2975653 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term966 P n.
Proof. exact (fun h0 : term808 P n => @lem2975652 P n h1). Qed.
Lemma lem2975655 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2975656 (P : nat -> Prop) (n : nat) : (term966 P n) = (term775 P n).
Proof. exact (@lem2975655 (term775 P n)). Qed.
Lemma lem2975657 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : term775 P n.
Proof. exact (EQ_MP (@lem2975656 P n) (@lem2975653 P n h1)). Qed.
Lemma lem2975660 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2975662 (P : nat -> Prop) (n : nat) : (term808 P n) = (term967 P n).
Proof. exact (@lem2975660 (term775 P n)). Qed.
Lemma lem2975665 (P : nat -> Prop) (n : nat) (h1 : term808 P n) : term967 P n.
Proof. exact (EQ_MP (@lem2975662 P n) (@lem2975447 P n h1)). Qed.
Lemma lem2975668 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : False.
Proof. exact (@lem2975665 P n h1 (@lem2975657 P n h2)). Qed.
Lemma lem2975669 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : term965.
Proof. exact (fun h0 : ~ False => @lem2975668 P n h1 h2). Qed.
Lemma lem2975671 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2975672 : term965 = False.
Proof. exact (@lem2975671 False). Qed.
Lemma lem2975673 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : False.
Proof. exact (EQ_MP (@lem2975672) (@lem2975669 P n h1 h2)). Qed.
Lemma lem2975674 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem2975675 (_31847 : nat) (_31848 : nat) (h1 : _31847 = _31848) : _31847 = _31848.
Proof. exact (h1). Qed.
Lemma lem2975676 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) (h1 : _31847 = _31848) : (P _31847) = (P _31848).
Proof. exact (MK_COMB (@lem2975674 P) (@lem2975675 _31847 _31848 h1)). Qed.
Lemma lem2975678 (b : Prop) (a : Prop) : term968 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem2975679 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : term969 _31848 P _31847.
Proof. exact (@lem2975678 (P _31848) (P _31847)). Qed.
Lemma lem2975680 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) (h1 : _31847 = _31848) : term970 _31848 P _31847.
Proof. exact (@lem2975679 _31848 P _31847 (@lem2975676 P _31847 _31848 h1)). Qed.
Lemma lem2975681 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : term971 _31848 P _31847.
Proof. exact (fun h0 : _31847 = _31848 => @lem2975680 P _31847 _31848 h0). Qed.
Lemma lem2975683 (a : Prop) (b : Prop) : (a -> b) = (term972 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2975684 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term971 _31848 P _31847) = (term973 _31848 P _31847).
Proof. exact (@lem2975683 (_31847 = _31848) (term970 _31848 P _31847)). Qed.
Lemma lem2975685 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : term973 _31848 P _31847.
Proof. exact (EQ_MP (@lem2975684 _31848 P _31847) (@lem2975681 _31848 P _31847)). Qed.
Lemma lem2975756 (x : nat) (y : nat) (z : nat) : term974 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem2975758 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem2975759 (n : nat) : n = n.
Proof. exact (@lem2975758 n). Qed.
Lemma lem2975760 (n : nat) : term975 n.
Proof. exact (fun h0 : term976 n => @lem2975759 n). Qed.
Lemma lem2975762 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2975763 (n : nat) : (term975 n) = (n = n).
Proof. exact (@lem2975762 (n = n)). Qed.
Lemma lem2975764 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem2975763 n) (@lem2975760 n)). Qed.
Lemma lem2975767 (P : nat -> Prop) (n : nat) (h1 : term793 P n) : term793 P n.
Proof. exact (h1). Qed.
Lemma lem2975768 (P : nat -> Prop) (n : nat) (h1 : term793 P n) : term977 P n.
Proof. exact (fun h0 : P n => @lem2975767 P n h1). Qed.
Lemma lem2975770 (p : Prop) : (term978 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2975771 (P : nat -> Prop) (n : nat) : (term977 P n) = (term793 P n).
Proof. exact (@lem2975770 (P n)). Qed.
Lemma lem2975772 (P : nat -> Prop) (n : nat) (h1 : term793 P n) : term793 P n.
Proof. exact (EQ_MP (@lem2975771 P n) (@lem2975768 P n h1)). Qed.
Lemma lem2975774 (_31805 : nat) (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term778 P _31805.
Proof. exact (EQ_MP (@lem2975423 P _31805) (@lem2975422 _31805 n P h1)). Qed.
Lemma lem2975775 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term979 P n.
Proof. exact (@lem2975774 (term980 n) n P h1). Qed.
Lemma lem2975776 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term981 P n.
Proof. exact (fun h0 : term982 P n => @lem2975775 n P h1). Qed.
Lemma lem2975778 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2975779 (P : nat -> Prop) (n : nat) : (term981 P n) = (term979 P n).
Proof. exact (@lem2975778 (term979 P n)). Qed.
Lemma lem2975780 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term979 P n.
Proof. exact (EQ_MP (@lem2975779 P n) (@lem2975776 n P h1)). Qed.
Lemma lem2975782 (b : Prop) (a : Prop) : (a \/ b) = (term983 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2975783 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term973 _31848 P _31847) = (term984 P _31847 _31848).
Proof. exact (@lem2975782 (term970 _31848 P _31847) (term985 _31847 _31848)). Qed.
Lemma lem2975785 (a : Prop) (b : Prop) : (term986 a b) = (term987 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2975786 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term988 _31848 P _31847) = (term989 _31848 P _31847).
Proof. exact (@lem2975785 (P _31848) (term793 P _31847)). Qed.
Lemma lem2975788 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2975789 (P : nat -> Prop) (_31847 : nat) : (term990 P _31847) = (P _31847).
Proof. exact (@lem2975788 (P _31847)). Qed.
Lemma lem2975790 (P : nat -> Prop) (_31848 : nat) : (term914 P _31848) = (term914 P _31848).
Proof. exact (eq_refl (term914 P _31848)). Qed.
Lemma lem2975791 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term989 _31848 P _31847) = (term991 _31848 P _31847).
Proof. exact (MK_COMB (@lem2975790 P _31848) (@lem2975789 P _31847)). Qed.
Lemma lem2975792 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term988 _31848 P _31847) = (term991 _31848 P _31847).
Proof. exact (TRANS (@lem2975786 _31848 P _31847) (@lem2975791 _31848 P _31847)). Qed.
Lemma lem2975793 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2975794 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term992 _31848 P _31847) = (term993 _31848 P _31847).
Proof. exact (MK_COMB (@lem2975793) (@lem2975792 _31848 P _31847)). Qed.
Lemma lem2975795 (_31847 : nat) (_31848 : nat) : (term985 _31847 _31848) = (term985 _31847 _31848).
Proof. exact (eq_refl (term985 _31847 _31848)). Qed.
Lemma lem2975796 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term984 P _31847 _31848) = (term994 P _31847 _31848).
Proof. exact (MK_COMB (@lem2975794 _31848 P _31847) (@lem2975795 _31847 _31848)). Qed.
Lemma lem2975797 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term973 _31848 P _31847) = (term994 P _31847 _31848).
Proof. exact (TRANS (@lem2975783 P _31847 _31848) (@lem2975796 P _31847 _31848)). Qed.
Lemma lem2975799 (n : nat) (P : nat -> Prop) (h1 : term793 P n) (h2 : term916 n P) : term995 P n.
Proof. exact (conj (@lem2975772 P n h1) (@lem2975780 n P h2)). Qed.
Lemma lem2975801 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : term994 P _31847 _31848.
Proof. exact (EQ_MP (@lem2975797 P _31847 _31848) (@lem2975685 _31848 P _31847)). Qed.
Lemma lem2975802 (P : nat -> Prop) (n : nat) : term996 P n.
Proof. exact (@lem2975801 P (term997 n) n). Qed.
Lemma lem2975805 (n : nat) (P : nat -> Prop) (h1 : term793 P n) (h2 : term916 n P) : term998 n.
Proof. exact (@lem2975802 P n (@lem2975799 n P h1 h2)). Qed.
Lemma lem2975806 (n : nat) (P : nat -> Prop) (h1 : term793 P n) (h2 : term916 n P) : term999 n.
Proof. exact (fun h0 : (term997 n) = n => @lem2975805 n P h1 h2). Qed.
Lemma lem2975808 (p : Prop) : (term978 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2975809 (n : nat) : (term999 n) = (term998 n).
Proof. exact (@lem2975808 ((term997 n) = n)). Qed.
Lemma lem2975810 (n : nat) (P : nat -> Prop) (h1 : term793 P n) (h2 : term916 n P) : term998 n.
Proof. exact (EQ_MP (@lem2975809 n) (@lem2975806 n P h1 h2)). Qed.
Lemma lem2975812 (b : Prop) (a : Prop) : (a \/ b) = (term983 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2975813 (z : nat) (x : nat) (y : nat) : (term974 x y z) = (term1000 z x y).
Proof. exact (@lem2975812 (term1001 x y z) (term985 x y)). Qed.
Lemma lem2975815 (a : Prop) (b : Prop) : (term986 a b) = (term987 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2975816 (x : nat) (y : nat) (z : nat) : (term1002 x y z) = (term1003 x y z).
Proof. exact (@lem2975815 (term985 x z) (y = z)). Qed.
Lemma lem2975818 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2975819 (x : nat) (z : nat) : (term1004 x z) = (x = z).
Proof. exact (@lem2975818 (x = z)). Qed.
Lemma lem2975820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2975821 (x : nat) (z : nat) : (term1005 x z) = (term1006 x z).
Proof. exact (MK_COMB (@lem2975820) (@lem2975819 x z)). Qed.
Lemma lem2975822 (y : nat) (z : nat) : (term985 y z) = (term985 y z).
Proof. exact (eq_refl (term985 y z)). Qed.
Lemma lem2975823 (x : nat) (y : nat) (z : nat) : (term1003 x y z) = (term1007 x y z).
Proof. exact (MK_COMB (@lem2975821 x z) (@lem2975822 y z)). Qed.
Lemma lem2975824 (x : nat) (y : nat) (z : nat) : (term1002 x y z) = (term1007 x y z).
Proof. exact (TRANS (@lem2975816 x y z) (@lem2975823 x y z)). Qed.
Lemma lem2975825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2975826 (x : nat) (y : nat) (z : nat) : (term1008 x y z) = (term1009 x y z).
Proof. exact (MK_COMB (@lem2975825) (@lem2975824 x y z)). Qed.
Lemma lem2975827 (x : nat) (y : nat) : (term985 x y) = (term985 x y).
Proof. exact (eq_refl (term985 x y)). Qed.
Lemma lem2975828 (z : nat) (x : nat) (y : nat) : (term1000 z x y) = (term1010 z x y).
Proof. exact (MK_COMB (@lem2975826 x y z) (@lem2975827 x y)). Qed.
Lemma lem2975829 (z : nat) (x : nat) (y : nat) : (term974 x y z) = (term1010 z x y).
Proof. exact (TRANS (@lem2975813 z x y) (@lem2975828 z x y)). Qed.
Lemma lem2975831 (n : nat) (P : nat -> Prop) (h1 : term793 P n) (h2 : term916 n P) : term1011 n.
Proof. exact (conj (@lem2975764 n) (@lem2975810 n P h1 h2)). Qed.
Lemma lem2975833 (z : nat) (x : nat) (y : nat) : term1010 z x y.
Proof. exact (EQ_MP (@lem2975829 z x y) (@lem2975756 x y z)). Qed.
Lemma lem2975834 (n : nat) : term1012 n.
Proof. exact (@lem2975833 n n (term997 n)). Qed.
Lemma lem2975837 (n : nat) (P : nat -> Prop) (h1 : term793 P n) (h2 : term916 n P) : term1013 n.
Proof. exact (@lem2975834 n (@lem2975831 n P h1 h2)). Qed.
Lemma lem2975838 (n : nat) (P : nat -> Prop) (h1 : term793 P n) (h2 : term916 n P) : term1014 n.
Proof. exact (fun h0 : n = (term997 n) => @lem2975837 n P h1 h2). Qed.
Lemma lem2975840 (p : Prop) : (term978 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2975841 (n : nat) : (term1014 n) = (term1013 n).
Proof. exact (@lem2975840 (n = (term997 n))). Qed.
Lemma lem2975842 (n : nat) (P : nat -> Prop) (h1 : term793 P n) (h2 : term916 n P) : term1013 n.
Proof. exact (EQ_MP (@lem2975841 n) (@lem2975838 n P h1 h2)). Qed.
Lemma lem2975857 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2975858 (_31804 : nat) : (term1015 _31804) = (term23 _31804).
Proof. exact (@lem2975857 (_31804 = (term997 _31804)) (_31804 = (term1016 _31804))). Qed.
Lemma lem2975868 (_31804 : nat) : (term25 _31804) = (term25 _31804).
Proof. exact (eq_refl (term25 _31804)). Qed.
Lemma lem2975869 (_31804 : nat) : ((term23 _31804) = (term1015 _31804)) = ((term23 _31804) = (term23 _31804)).
Proof. exact (MK_COMB (@lem2975868 _31804) (@lem2975858 _31804)). Qed.
Lemma lem2975871 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2975872 (x : Prop) : (x = x) = True.
Proof. exact (@lem2975871 Prop x). Qed.
Lemma lem2975873 (_31804 : nat) : ((term23 _31804) = (term23 _31804)) = True.
Proof. exact (@lem2975872 (term23 _31804)). Qed.
Lemma lem2975874 (_31804 : nat) : ((term23 _31804) = (term1015 _31804)) = True.
Proof. exact (TRANS (@lem2975869 _31804) (@lem2975873 _31804)). Qed.
Lemma lem2975875 (_31804 : nat) : True = ((term23 _31804) = (term1015 _31804)).
Proof. exact (SYM (@lem2975874 _31804)). Qed.
Lemma lem2975876 (_31804 : nat) : (term23 _31804) = (term1015 _31804).
Proof. exact (EQ_MP (@lem2975875 _31804) (@lem0)). Qed.
Lemma lem2975877 (_31804 : nat) (h1 : term761) : term1015 _31804.
Proof. exact (EQ_MP (@lem2975876 _31804) (@lem2975453 _31804 h1)). Qed.
Lemma lem2975879 (b : Prop) (a : Prop) : (a \/ b) = (term983 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2975882 (_31804 : nat) : (term1015 _31804) = (term1017 _31804).
Proof. exact (@lem2975879 (_31804 = (term997 _31804)) (_31804 = (term1016 _31804))). Qed.
Lemma lem2975885 (_31804 : nat) (h1 : term761) : term1017 _31804.
Proof. exact (EQ_MP (@lem2975882 _31804) (@lem2975877 _31804 h1)). Qed.
Lemma lem2975886 (n : nat) (h1 : term761) : term1017 n.
Proof. exact (@lem2975885 n h1). Qed.
Lemma lem2975889 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : n = (term1016 n).
Proof. exact (@lem2975886 n h1 (@lem2975842 n P h2 h3)). Qed.
Lemma lem2975890 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : term1018 n.
Proof. exact (fun h0 : term1019 n => @lem2975889 n P h1 h2 h3). Qed.
Lemma lem2975892 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2975893 (n : nat) : (term1018 n) = (n = (term1016 n)).
Proof. exact (@lem2975892 (n = (term1016 n))). Qed.
Lemma lem2975894 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : n = (term1016 n).
Proof. exact (EQ_MP (@lem2975893 n) (@lem2975890 n P h1 h2 h3)). Qed.
Lemma lem2975896 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem2975897 (n : nat) : n = n.
Proof. exact (@lem2975896 n). Qed.
Lemma lem2975898 (n : nat) : term975 n.
Proof. exact (fun h0 : term976 n => @lem2975897 n). Qed.
Lemma lem2975900 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2975901 (n : nat) : (term975 n) = (n = n).
Proof. exact (@lem2975900 (n = n)). Qed.
Lemma lem2975902 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem2975901 n) (@lem2975898 n)). Qed.
Lemma lem2975920 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2975921 (y : nat) (x : nat) (z : nat) : (term1001 x y z) = (term1020 y x z).
Proof. exact (@lem2975920 (y = z) (term985 x z)). Qed.
Lemma lem2975931 (x : nat) (y : nat) : (term1021 x y) = (term1021 x y).
Proof. exact (eq_refl (term1021 x y)). Qed.
Lemma lem2975932 (y : nat) (x : nat) (z : nat) : (term974 x y z) = (term1022 y x z).
Proof. exact (MK_COMB (@lem2975931 x y) (@lem2975921 y x z)). Qed.
Lemma lem2975936 (q : Prop) (p : Prop) (r : Prop) : (term1023 p q r) = (term1023 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2975937 (y : nat) (x : nat) (z : nat) : (term1022 y x z) = (term1024 y x z).
Proof. exact (@lem2975936 (y = z) (term985 x y) (term985 x z)). Qed.
Lemma lem2975959 (y : nat) (x : nat) (z : nat) : (term974 x y z) = (term1024 y x z).
Proof. exact (TRANS (@lem2975932 y x z) (@lem2975937 y x z)). Qed.
Lemma lem2975960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2975961 (y : nat) (x : nat) (z : nat) : (term1025 x y z) = (term1026 y x z).
Proof. exact (MK_COMB (@lem2975960) (@lem2975959 y x z)). Qed.
Lemma lem2975983 (y : nat) (x : nat) (z : nat) : (term1024 y x z) = (term1024 y x z).
Proof. exact (eq_refl (term1024 y x z)). Qed.
Lemma lem2975984 (y : nat) (x : nat) (z : nat) : ((term974 x y z) = (term1024 y x z)) = ((term1024 y x z) = (term1024 y x z)).
Proof. exact (MK_COMB (@lem2975961 y x z) (@lem2975983 y x z)). Qed.
Lemma lem2975986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2975987 (x : Prop) : (x = x) = True.
Proof. exact (@lem2975986 Prop x). Qed.
Lemma lem2975988 (y : nat) (x : nat) (z : nat) : ((term1024 y x z) = (term1024 y x z)) = True.
Proof. exact (@lem2975987 (term1024 y x z)). Qed.
Lemma lem2975989 (y : nat) (x : nat) (z : nat) : ((term974 x y z) = (term1024 y x z)) = True.
Proof. exact (TRANS (@lem2975984 y x z) (@lem2975988 y x z)). Qed.
Lemma lem2975990 (y : nat) (x : nat) (z : nat) : True = ((term974 x y z) = (term1024 y x z)).
Proof. exact (SYM (@lem2975989 y x z)). Qed.
Lemma lem2975991 (y : nat) (x : nat) (z : nat) : (term974 x y z) = (term1024 y x z).
Proof. exact (EQ_MP (@lem2975990 y x z) (@lem0)). Qed.
Lemma lem2975992 (y : nat) (x : nat) (z : nat) : term1024 y x z.
Proof. exact (EQ_MP (@lem2975991 y x z) (@lem2975756 x y z)). Qed.
Lemma lem2975994 (b : Prop) (a : Prop) : (a \/ b) = (term983 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2975995 (x : nat) (y : nat) (z : nat) : (term1024 y x z) = (term1027 x y z).
Proof. exact (@lem2975994 (term1028 y x z) (y = z)). Qed.
Lemma lem2975997 (a : Prop) (b : Prop) : (term986 a b) = (term987 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2975998 (y : nat) (x : nat) (z : nat) : (term1029 y x z) = (term1030 y x z).
Proof. exact (@lem2975997 (term985 x y) (term985 x z)). Qed.
Lemma lem2976000 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2976001 (x : nat) (y : nat) : (term1004 x y) = (x = y).
Proof. exact (@lem2976000 (x = y)). Qed.
Lemma lem2976002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2976003 (x : nat) (y : nat) : (term1005 x y) = (term1006 x y).
Proof. exact (MK_COMB (@lem2976002) (@lem2976001 x y)). Qed.
Lemma lem2976005 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2976006 (x : nat) (z : nat) : (term1004 x z) = (x = z).
Proof. exact (@lem2976005 (x = z)). Qed.
Lemma lem2976007 (y : nat) (x : nat) (z : nat) : (term1030 y x z) = (term1031 y x z).
Proof. exact (MK_COMB (@lem2976003 x y) (@lem2976006 x z)). Qed.
Lemma lem2976008 (y : nat) (x : nat) (z : nat) : (term1029 y x z) = (term1031 y x z).
Proof. exact (TRANS (@lem2975998 y x z) (@lem2976007 y x z)). Qed.
Lemma lem2976009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2976010 (y : nat) (x : nat) (z : nat) : (term1032 y x z) = (term1033 y x z).
Proof. exact (MK_COMB (@lem2976009) (@lem2976008 y x z)). Qed.
Lemma lem2976011 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem2976012 (x : nat) (y : nat) (z : nat) : (term1027 x y z) = (term1034 x y z).
Proof. exact (MK_COMB (@lem2976010 y x z) (@lem2976011 y z)). Qed.
Lemma lem2976013 (x : nat) (y : nat) (z : nat) : (term1024 y x z) = (term1034 x y z).
Proof. exact (TRANS (@lem2975995 x y z) (@lem2976012 x y z)). Qed.
Lemma lem2976015 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : term1035 n.
Proof. exact (conj (@lem2975894 n P h1 h2 h3) (@lem2975902 n)). Qed.
Lemma lem2976017 (x : nat) (y : nat) (z : nat) : term1034 x y z.
Proof. exact (EQ_MP (@lem2976013 x y z) (@lem2975992 y x z)). Qed.
Lemma lem2976018 (n : nat) : term1036 n.
Proof. exact (@lem2976017 n (term1016 n) n). Qed.
Lemma lem2976021 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : (term1016 n) = n.
Proof. exact (@lem2976018 n (@lem2976015 n P h1 h2 h3)). Qed.
Lemma lem2976022 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : term1037 n.
Proof. exact (fun h0 : term1038 n => @lem2976021 n P h1 h2 h3). Qed.
Lemma lem2976024 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2976025 (n : nat) : (term1037 n) = ((term1016 n) = n).
Proof. exact (@lem2976024 ((term1016 n) = n)). Qed.
Lemma lem2976026 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : (term1016 n) = n.
Proof. exact (EQ_MP (@lem2976025 n) (@lem2976022 n P h1 h2 h3)). Qed.
Lemma lem2976028 (_31806 : nat) (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term775 P _31806.
Proof. exact (EQ_MP (@lem2975426 P _31806) (@lem2975425 _31806 n P h1)). Qed.
Lemma lem2976029 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term1039 P n.
Proof. exact (@lem2976028 (term980 n) n P h1). Qed.
Lemma lem2976030 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term1040 P n.
Proof. exact (fun h0 : term1041 P n => @lem2976029 n P h1). Qed.
Lemma lem2976032 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2976033 (P : nat -> Prop) (n : nat) : (term1040 P n) = (term1039 P n).
Proof. exact (@lem2976032 (term1039 P n)). Qed.
Lemma lem2976034 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term1039 P n.
Proof. exact (EQ_MP (@lem2976033 P n) (@lem2976030 n P h1)). Qed.
Lemma lem2976040 (q : Prop) (p : Prop) (r : Prop) : (term1023 p q r) = (term1023 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2976041 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term973 _31848 P _31847) = (term1042 _31848 P _31847).
Proof. exact (@lem2976040 (P _31848) (term985 _31847 _31848) (term793 P _31847)). Qed.
Lemma lem2976055 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2976056 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term1043 _31848 P _31847) = (term1044 P _31847 _31848).
Proof. exact (@lem2976055 (term793 P _31847) (term985 _31847 _31848)). Qed.
Lemma lem2976064 (P : nat -> Prop) (_31848 : nat) : (term1045 P _31848) = (term1045 P _31848).
Proof. exact (eq_refl (term1045 P _31848)). Qed.
Lemma lem2976065 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term1042 _31848 P _31847) = (term1046 P _31847 _31848).
Proof. exact (MK_COMB (@lem2976064 P _31848) (@lem2976056 P _31847 _31848)). Qed.
Lemma lem2976076 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term973 _31848 P _31847) = (term1046 P _31847 _31848).
Proof. exact (TRANS (@lem2976041 _31848 P _31847) (@lem2976065 P _31847 _31848)). Qed.
Lemma lem2976077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2976078 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term1047 _31848 P _31847) = (term1048 P _31847 _31848).
Proof. exact (MK_COMB (@lem2976077) (@lem2976076 P _31847 _31848)). Qed.
Lemma lem2976092 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2976093 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term1043 _31848 P _31847) = (term1044 P _31847 _31848).
Proof. exact (@lem2976092 (term793 P _31847) (term985 _31847 _31848)). Qed.
Lemma lem2976101 (P : nat -> Prop) (_31848 : nat) : (term1045 P _31848) = (term1045 P _31848).
Proof. exact (eq_refl (term1045 P _31848)). Qed.
Lemma lem2976102 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : (term1042 _31848 P _31847) = (term1046 P _31847 _31848).
Proof. exact (MK_COMB (@lem2976101 P _31848) (@lem2976093 P _31847 _31848)). Qed.
Lemma lem2976113 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : ((term973 _31848 P _31847) = (term1042 _31848 P _31847)) = ((term1046 P _31847 _31848) = (term1046 P _31847 _31848)).
Proof. exact (MK_COMB (@lem2976078 P _31847 _31848) (@lem2976102 P _31847 _31848)). Qed.
Lemma lem2976115 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2976116 (x : Prop) : (x = x) = True.
Proof. exact (@lem2976115 Prop x). Qed.
Lemma lem2976117 (P : nat -> Prop) (_31847 : nat) (_31848 : nat) : ((term1046 P _31847 _31848) = (term1046 P _31847 _31848)) = True.
Proof. exact (@lem2976116 (term1046 P _31847 _31848)). Qed.
Lemma lem2976118 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : ((term973 _31848 P _31847) = (term1042 _31848 P _31847)) = True.
Proof. exact (TRANS (@lem2976113 P _31847 _31848) (@lem2976117 P _31847 _31848)). Qed.
Lemma lem2976119 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : True = ((term973 _31848 P _31847) = (term1042 _31848 P _31847)).
Proof. exact (SYM (@lem2976118 _31848 P _31847)). Qed.
Lemma lem2976120 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term973 _31848 P _31847) = (term1042 _31848 P _31847).
Proof. exact (EQ_MP (@lem2976119 _31848 P _31847) (@lem0)). Qed.
Lemma lem2976121 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : term1042 _31848 P _31847.
Proof. exact (EQ_MP (@lem2976120 _31848 P _31847) (@lem2975685 _31848 P _31847)). Qed.
Lemma lem2976123 (b : Prop) (a : Prop) : (a \/ b) = (term983 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2976124 (_31847 : nat) (P : nat -> Prop) (_31848 : nat) : (term1042 _31848 P _31847) = (term1049 _31847 P _31848).
Proof. exact (@lem2976123 (term1043 _31848 P _31847) (P _31848)). Qed.
Lemma lem2976126 (a : Prop) (b : Prop) : (term986 a b) = (term987 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2976127 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term1050 _31848 P _31847) = (term1051 _31848 P _31847).
Proof. exact (@lem2976126 (term985 _31847 _31848) (term793 P _31847)). Qed.
Lemma lem2976129 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2976130 (_31847 : nat) (_31848 : nat) : (term1004 _31847 _31848) = (_31847 = _31848).
Proof. exact (@lem2976129 (_31847 = _31848)). Qed.
Lemma lem2976131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2976132 (_31847 : nat) (_31848 : nat) : (term1005 _31847 _31848) = (term1006 _31847 _31848).
Proof. exact (MK_COMB (@lem2976131) (@lem2976130 _31847 _31848)). Qed.
Lemma lem2976134 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2976135 (P : nat -> Prop) (_31847 : nat) : (term990 P _31847) = (P _31847).
Proof. exact (@lem2976134 (P _31847)). Qed.
Lemma lem2976136 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term1051 _31848 P _31847) = (term1052 _31848 P _31847).
Proof. exact (MK_COMB (@lem2976132 _31847 _31848) (@lem2976135 P _31847)). Qed.
Lemma lem2976137 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term1050 _31848 P _31847) = (term1052 _31848 P _31847).
Proof. exact (TRANS (@lem2976127 _31848 P _31847) (@lem2976136 _31848 P _31847)). Qed.
Lemma lem2976138 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2976139 (_31848 : nat) (P : nat -> Prop) (_31847 : nat) : (term1053 _31848 P _31847) = (term1054 _31848 P _31847).
Proof. exact (MK_COMB (@lem2976138) (@lem2976137 _31848 P _31847)). Qed.
Lemma lem2976140 (P : nat -> Prop) (_31848 : nat) : (P _31848) = (P _31848).
Proof. exact (eq_refl (P _31848)). Qed.
Lemma lem2976141 (_31847 : nat) (P : nat -> Prop) (_31848 : nat) : (term1049 _31847 P _31848) = (term1055 _31847 P _31848).
Proof. exact (MK_COMB (@lem2976139 _31848 P _31847) (@lem2976140 P _31848)). Qed.
Lemma lem2976142 (_31847 : nat) (P : nat -> Prop) (_31848 : nat) : (term1042 _31848 P _31847) = (term1055 _31847 P _31848).
Proof. exact (TRANS (@lem2976124 _31847 P _31848) (@lem2976141 _31847 P _31848)). Qed.
Lemma lem2976144 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : term1056 P n.
Proof. exact (conj (@lem2976026 n P h1 h2 h3) (@lem2976034 n P h3)). Qed.
Lemma lem2976146 (_31847 : nat) (P : nat -> Prop) (_31848 : nat) : term1055 _31847 P _31848.
Proof. exact (EQ_MP (@lem2976142 _31847 P _31848) (@lem2976121 _31848 P _31847)). Qed.
Lemma lem2976147 (P : nat -> Prop) (n : nat) : term1057 P n.
Proof. exact (@lem2976146 (term1016 n) P n). Qed.
Lemma lem2976150 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term793 P n) (h3 : term916 n P) : P n.
Proof. exact (@lem2976147 P n (@lem2976144 n P h1 h2 h3)). Qed.
Lemma lem2976151 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term916 n P) : term1058 P n.
Proof. exact (fun h0 : term793 P n => @lem2976150 n P h1 h0 h2). Qed.
Lemma lem2976153 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2976154 (P : nat -> Prop) (n : nat) : (term1058 P n) = (P n).
Proof. exact (@lem2976153 (P n)). Qed.
Lemma lem2976155 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term916 n P) : P n.
Proof. exact (EQ_MP (@lem2976154 P n) (@lem2976151 n P h1 h2)). Qed.
Lemma lem2976158 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2976160 (P : nat -> Prop) (n : nat) : (term793 P n) = (term1059 P n).
Proof. exact (@lem2976158 (P n)). Qed.
Lemma lem2976163 (n : nat) (P : nat -> Prop) (h1 : term916 n P) : term1059 P n.
Proof. exact (EQ_MP (@lem2976160 P n) (@lem2975455 n P h1)). Qed.
Lemma lem2976166 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term916 n P) : False.
Proof. exact (@lem2976163 n P h2 (@lem2976155 n P h1 h2)). Qed.
Lemma lem2976167 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term916 n P) : term965.
Proof. exact (fun h0 : ~ False => @lem2976166 n P h1 h2). Qed.
Lemma lem2976169 (p : Prop) : (term963 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2976170 : term965 = False.
Proof. exact (@lem2976169 False). Qed.
Lemma lem2976171 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term916 n P) : False.
Proof. exact (EQ_MP (@lem2976170) (@lem2976167 n P h1 h2)). Qed.
Lemma lem2976172 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : (term808 P n) = False.
Proof. exact (prop_ext (fun h3 : term808 P n => @lem2975673 P n h1 h2) (fun h3 : False => @lem2975447 P n h1)). Qed.
Lemma lem2976173 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : False.
Proof. exact (EQ_MP (@lem2976172 P n h1 h2) (@lem2975447 P n h1)). Qed.
Lemma lem2976174 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : (term800 P n) = False.
Proof. exact (prop_ext (fun h3 : term800 P n => @lem2975566 P n h1 h2) (fun h3 : False => @lem2975437 P n h1)). Qed.
Lemma lem2976175 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : False.
Proof. exact (EQ_MP (@lem2976174 P n h1 h2) (@lem2975437 P n h1)). Qed.
Lemma lem2976176 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : (term808 P n) = False.
Proof. exact (prop_ext (fun h3 : term808 P n => @lem2976173 P n h1 h2) (fun h3 : False => @lem2975375 P n h1)). Qed.
Lemma lem2976177 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : False.
Proof. exact (EQ_MP (@lem2976176 P n h1 h2) (@lem2975375 P n h1)). Qed.
Lemma lem2976178 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : (term800 P n) = False.
Proof. exact (prop_ext (fun h3 : term800 P n => @lem2976175 P n h1 h2) (fun h3 : False => @lem2975351 P n h1)). Qed.
Lemma lem2976179 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : False.
Proof. exact (EQ_MP (@lem2976178 P n h1 h2) (@lem2975351 P n h1)). Qed.
Lemma lem2976180 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term916 n P) : term761 = False.
Proof. exact (prop_ext (fun h3 : term761 => @lem2976171 n P h1 h2) (fun h3 : False => @lem2975388 h1)). Qed.
Lemma lem2976181 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term916 n P) : False.
Proof. exact (EQ_MP (@lem2976180 n P h1 h2) (@lem2975388 h1)). Qed.
Lemma lem2976182 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : (term808 P n) = False.
Proof. exact (prop_ext (fun h3 : term808 P n => @lem2976177 P n h1 h2) (fun h3 : False => @lem2975375 P n h1)). Qed.
Lemma lem2976183 (P : nat -> Prop) (n : nat) (h1 : term808 P n) (h2 : term894 P n) : False.
Proof. exact (EQ_MP (@lem2976182 P n h1 h2) (@lem2975375 P n h1)). Qed.
Lemma lem2976184 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : (term800 P n) = False.
Proof. exact (prop_ext (fun h3 : term800 P n => @lem2976179 P n h1 h2) (fun h3 : False => @lem2975351 P n h1)). Qed.
Lemma lem2976185 (P : nat -> Prop) (n : nat) (h1 : term800 P n) (h2 : term894 P n) : False.
Proof. exact (EQ_MP (@lem2976184 P n h1 h2) (@lem2975351 P n h1)). Qed.
Lemma lem2976186 (P : nat -> Prop) (n : nat) (h1 : term894 P n) : False.
Proof. exact (or_elim (@lem2975320 P n h1) (fun h0 : term800 P n => @lem2976185 P n h0 h1) (fun h0 : term808 P n => @lem2976183 P n h0 h1)). Qed.
Lemma lem2976187 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term955 n P) : False.
Proof. exact (or_elim (@lem2975317 n P h2) (fun h0 : term894 P n => @lem2976186 P n h0) (fun h0 : term916 n P => @lem2976181 n P h1 h0)). Qed.
Lemma lem2976188 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term955 n P) : (term955 n P) = False.
Proof. exact (prop_ext (fun h3 : term955 n P => @lem2976187 n P h1 h2) (fun h3 : False => @lem2975317 n P h2)). Qed.
Lemma lem2976189 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term955 n P) : False.
Proof. exact (EQ_MP (@lem2976188 n P h1 h2) (@lem2975317 n P h2)). Qed.
Lemma lem2976190 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term955 n P) : term761 = False.
Proof. exact (prop_ext (fun h3 : term761 => @lem2976189 n P h1 h2) (fun h3 : False => @lem2975212 h1)). Qed.
Lemma lem2976191 (n : nat) (P : nat -> Prop) (h1 : term761) (h2 : term955 n P) : False.
Proof. exact (EQ_MP (@lem2976190 n P h1 h2) (@lem2975212 h1)). Qed.
Lemma lem2976192 (P : nat -> Prop) (h1 : term761) (h2 : term958 P) : False.
Proof. exact (ex_elim (@lem2975146 P h2) (fun n : nat => fun h0 : term957 P n => @lem2976191 n P h1 h0)). Qed.
Lemma lem2976193 (h1 : term761) (h2 : term765) : False.
Proof. exact (ex_elim (@lem2975084 h2) (fun P : nat -> Prop => fun h0 : term959 P => @lem2976192 P h1 h0)). Qed.
Lemma lem2976194 (h1 : term761) (h2 : term765) : term761 = False.
Proof. exact (prop_ext (fun h3 : term761 => @lem2976193 h1 h2) (fun h3 : False => @lem2975145 h1)). Qed.
Lemma lem2976195 (h1 : term761) (h2 : term765) : False.
Proof. exact (EQ_MP (@lem2976194 h1 h2) (@lem2975145 h1)). Qed.
Lemma lem2976196 (h1 : term765) : term770.
Proof. exact (fun h0 : term761 => @lem2976195 h0 h1). Qed.
Lemma lem2976197 : term770 = term771.
Proof. exact (@lem69 term761). Qed.
Lemma lem2976198 (h1 : term765) : term771.
Proof. exact (EQ_MP (@lem2976197) (@lem2976196 h1)). Qed.
Lemma lem2976199 : term773.
Proof. exact (fun h0 : term765 => @lem2976198 h0). Qed.
Lemma lem2976200 : term766.
Proof. exact (EQ_MP (@lem2974716) (@lem2976199)). Qed.
Lemma lem2976202 : term766.
Proof. exact (@lem2974559 (@lem2976200)). Qed.
Lemma lem2976203 (h1 : term765) : term770.
Proof. exact (@lem2976202 (@lem2974544 h1)). Qed.
Lemma lem2976204 (h1 : term765) : False.
Proof. exact (@lem2976203 h1 (@lem2974539)). Qed.
Lemma lem2976205 (h1 : term765) : term765 = False.
Proof. exact (prop_ext (fun h2 : term765 => @lem2976204 h1) (fun h2 : False => @lem2974544 h1)). Qed.
Lemma lem2976206 (h1 : term765) : False.
Proof. exact (EQ_MP (@lem2976205 h1) (@lem2974544 h1)). Qed.
Lemma lem2976207 : term764.
Proof. exact (fun h0 : term765 => @lem2976206 h0). Qed.
Lemma lem2976208 : term763.
Proof. exact (EQ_MP (@lem2974543) (@lem2976207)). Qed.
