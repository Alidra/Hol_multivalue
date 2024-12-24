Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_ADD_SPLIT_term_abbrevs.
Require Import DISJOINT_NUMSEG_spec.
Require Import FINITE_NUMSEG_spec.
Require Import INT_POS_spec.
Require Import NSUM_UNION_spec.
Require Import NUMSEG_ADD_SPLIT_spec.
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
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
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
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2318496_spec.
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
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7047656 (m : nat) (n : nat) : (Peano.lt m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7047657 (x : nat) : (term1 x) = (term2 x).
Proof. exact (@lem7047656 x (term3 x)). Qed.
Lemma lem7047659 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7047660 (x : nat) : (term6 x) = (term7 x).
Proof. exact (@lem7047659 x term8). Qed.
Lemma lem7047661 (x : nat) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem7047662 (x : nat) : (term2 x) = (term10 x).
Proof. exact (MK_COMB (@lem7047661 x) (@lem7047660 x)). Qed.
Lemma lem7047664 (x : nat) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem7047657 x) (@lem7047662 x)). Qed.
Lemma lem7047665 (x : nat) : term11 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem7047666 (x : nat) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem7047667 (x : nat) : term12 x.
Proof. exact (EQ_MP (@lem7047666 x) (@lem7047665 x)). Qed.
Lemma lem7047668 (_94144 : int) : (term13 _94144) = (term14 _94144).
Proof. exact (@lem2318604 (term14 _94144)). Qed.
Lemma lem7047691 (_94144 : int) : (term15 _94144) = (term16 _94144).
Proof. exact (@lem17362 (term17 _94144) (term18 _94144)). Qed.
Lemma lem7047694 (x : int) (y : int) : (int_le x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7047695 (_94144 : int) : (term17 _94144) = (term20 _94144).
Proof. exact (@lem7047694 term21 _94144). Qed.
Lemma lem7047697 (n : nat) : (term22 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7047698 : term23 = term24.
Proof. exact (@lem7047697 (NUMERAL 0)). Qed.
Lemma lem7047699 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7047700 : term25 = term26.
Proof. exact (MK_COMB (@lem7047699) (@lem7047698)). Qed.
Lemma lem7047701 (_94144 : int) : (real_of_int _94144) = (real_of_int _94144).
Proof. exact (eq_refl (real_of_int _94144)). Qed.
Lemma lem7047702 (_94144 : int) : (term20 _94144) = (term27 _94144).
Proof. exact (MK_COMB (@lem7047700) (@lem7047701 _94144)). Qed.
Lemma lem7047704 (_94144 : int) : (term17 _94144) = (term27 _94144).
Proof. exact (TRANS (@lem7047695 _94144) (@lem7047702 _94144)). Qed.
Lemma lem7047706 (y : int) (x : int) : (term28 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem7047707 (_94144 : int) : (term29 _94144) = (term30 _94144).
Proof. exact (@lem7047706 (term31 _94144) _94144). Qed.
Lemma lem7047709 (x : int) (y : int) : (int_le x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7047710 (_94144 : int) : (term30 _94144) = (term32 _94144).
Proof. exact (@lem7047709 (term31 _94144) _94144). Qed.
Lemma lem7047712 (x : int) (y : int) : (term33 x y) = (term34 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7047713 (_94144 : int) : (term35 _94144) = (term36 _94144).
Proof. exact (@lem7047712 _94144 term37). Qed.
Lemma lem7047715 (n : nat) : (term22 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7047716 : term38 = term39.
Proof. exact (@lem7047715 term8). Qed.
Lemma lem7047717 (_94144 : int) : (term40 _94144) = (term40 _94144).
Proof. exact (eq_refl (term40 _94144)). Qed.
Lemma lem7047718 (_94144 : int) : (term36 _94144) = (term41 _94144).
Proof. exact (MK_COMB (@lem7047717 _94144) (@lem7047716)). Qed.
Lemma lem7047719 (_94144 : int) : (term35 _94144) = (term41 _94144).
Proof. exact (TRANS (@lem7047713 _94144) (@lem7047718 _94144)). Qed.
Lemma lem7047720 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7047721 (_94144 : int) : (term42 _94144) = (term43 _94144).
Proof. exact (MK_COMB (@lem7047720) (@lem7047719 _94144)). Qed.
Lemma lem7047722 (_94144 : int) : (real_of_int _94144) = (real_of_int _94144).
Proof. exact (eq_refl (real_of_int _94144)). Qed.
Lemma lem7047723 (_94144 : int) : (term32 _94144) = (term44 _94144).
Proof. exact (MK_COMB (@lem7047721 _94144) (@lem7047722 _94144)). Qed.
Lemma lem7047724 (_94144 : int) : (term30 _94144) = (term44 _94144).
Proof. exact (TRANS (@lem7047710 _94144) (@lem7047723 _94144)). Qed.
Lemma lem7047725 (_94144 : int) : (term29 _94144) = (term44 _94144).
Proof. exact (TRANS (@lem7047707 _94144) (@lem7047724 _94144)). Qed.
Lemma lem7047726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7047727 (_94144 : int) : (term45 _94144) = (term46 _94144).
Proof. exact (MK_COMB (@lem7047726) (@lem7047704 _94144)). Qed.
Lemma lem7047728 (_94144 : int) : (term16 _94144) = (term47 _94144).
Proof. exact (MK_COMB (@lem7047727 _94144) (@lem7047725 _94144)). Qed.
Lemma lem7047729 (_94144 : int) : (term15 _94144) = (term47 _94144).
Proof. exact (TRANS (@lem7047691 _94144) (@lem7047728 _94144)). Qed.
Lemma lem7047733 (t : Prop) : (term48 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7047749 (_94144 : int) : (term49 _94144) = (term47 _94144).
Proof. exact (@lem7047733 (term47 _94144)). Qed.
Lemma lem7047750 (_94144 : int) : (term27 _94144) = (term50 _94144).
Proof. exact (@lem1988287 (real_of_int _94144) term24). Qed.
Lemma lem7047756 (_94144 : int) : (term51 _94144) = (term52 _94144).
Proof. exact (@lem1982792 (real_of_int _94144) term24). Qed.
Lemma lem7047758 (x : nat) : (real_of_num x) = (term53 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7047759 : term24 = term54.
Proof. exact (@lem7047758 (NUMERAL 0)). Qed.
Lemma lem7047761 (x : nat) : (term55 x) = (term56 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7047762 : term57 = term58.
Proof. exact (@lem7047761 term8). Qed.
Lemma lem7047763 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7047764 : term59 = term60.
Proof. exact (MK_COMB (@lem7047763) (@lem7047762)). Qed.
Lemma lem7047765 : term61 = term62.
Proof. exact (MK_COMB (@lem7047764) (@lem7047759)). Qed.
Lemma lem7047766 : term62 = term63.
Proof. exact (@lem1981613 term57 term24 term39 term39). Qed.
Lemma lem7047768 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7047769 : term66 = term67.
Proof. exact (@lem7047768 term8 term8). Qed.
Lemma lem7047770 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7047771 : term69 = term8.
Proof. exact (EQ_MP (@lem7047770) (@lem940073)). Qed.
Lemma lem7047772 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7047773 : term67 = term39.
Proof. exact (MK_COMB (@lem7047772) (@lem7047771)). Qed.
Lemma lem7047774 : term66 = term39.
Proof. exact (TRANS (@lem7047769) (@lem7047773)). Qed.
Lemma lem7047776 (x : nat) : (term70 x) = term24.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7047777 : term61 = term24.
Proof. exact (@lem7047776 term8). Qed.
Lemma lem7047778 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7047779 : term71 = term72.
Proof. exact (MK_COMB (@lem7047778) (@lem7047777)). Qed.
Lemma lem7047780 : term63 = term54.
Proof. exact (MK_COMB (@lem7047779) (@lem7047774)). Qed.
Lemma lem7047781 : term62 = term54.
Proof. exact (TRANS (@lem7047766) (@lem7047780)). Qed.
Lemma lem7047782 : term61 = term54.
Proof. exact (TRANS (@lem7047765) (@lem7047781)). Qed.
Lemma lem7047784 (x : real) : (term73 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7047785 : term54 = term24.
Proof. exact (@lem7047784 term24). Qed.
Lemma lem7047786 : term61 = term24.
Proof. exact (TRANS (@lem7047782) (@lem7047785)). Qed.
Lemma lem7047787 (_94144 : int) : (term40 _94144) = (term40 _94144).
Proof. exact (eq_refl (term40 _94144)). Qed.
Lemma lem7047788 (_94144 : int) : (term52 _94144) = (term74 _94144).
Proof. exact (MK_COMB (@lem7047787 _94144) (@lem7047786)). Qed.
Lemma lem7047789 (_94144 : int) : (term74 _94144) = (real_of_int _94144).
Proof. exact (@lem1982723 (real_of_int _94144)). Qed.
Lemma lem7047790 (_94144 : int) : (term52 _94144) = (real_of_int _94144).
Proof. exact (TRANS (@lem7047788 _94144) (@lem7047789 _94144)). Qed.
Lemma lem7047792 (_94144 : int) : (term51 _94144) = (real_of_int _94144).
Proof. exact (TRANS (@lem7047756 _94144) (@lem7047790 _94144)). Qed.
Lemma lem7047793 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7047794 (_94144 : int) : (term75 _94144) = (term76 _94144).
Proof. exact (MK_COMB (@lem7047793) (@lem7047792 _94144)). Qed.
Lemma lem7047795 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7047796 (_94144 : int) : (term50 _94144) = (term77 _94144).
Proof. exact (MK_COMB (@lem7047794 _94144) (@lem7047795)). Qed.
Lemma lem7047797 (_94144 : int) : (term27 _94144) = (term77 _94144).
Proof. exact (TRANS (@lem7047750 _94144) (@lem7047796 _94144)). Qed.
Lemma lem7047798 (_94144 : int) : (term44 _94144) = (term78 _94144).
Proof. exact (@lem1988287 (real_of_int _94144) (term41 _94144)). Qed.
Lemma lem7047810 (_94144 : int) : (term79 _94144) = (term80 _94144).
Proof. exact (@lem1982792 (real_of_int _94144) (term41 _94144)). Qed.
Lemma lem7047811 (_94144 : int) : (term81 _94144) = (term82 _94144).
Proof. exact (@lem1982781 (real_of_int _94144) term57 term39). Qed.
Lemma lem7047813 (x : nat) : (real_of_num x) = (term53 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7047814 : term39 = term83.
Proof. exact (@lem7047813 term8). Qed.
Lemma lem7047816 (x : nat) : (term55 x) = (term56 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7047817 : term57 = term58.
Proof. exact (@lem7047816 term8). Qed.
Lemma lem7047818 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7047819 : term59 = term60.
Proof. exact (MK_COMB (@lem7047818) (@lem7047817)). Qed.
Lemma lem7047820 : term84 = term85.
Proof. exact (MK_COMB (@lem7047819) (@lem7047814)). Qed.
Lemma lem7047821 : term85 = term86.
Proof. exact (@lem1981613 term57 term39 term39 term39). Qed.
Lemma lem7047823 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7047824 : term66 = term67.
Proof. exact (@lem7047823 term8 term8). Qed.
Lemma lem7047825 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7047826 : term69 = term8.
Proof. exact (EQ_MP (@lem7047825) (@lem940073)). Qed.
Lemma lem7047827 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7047828 : term67 = term39.
Proof. exact (MK_COMB (@lem7047827) (@lem7047826)). Qed.
Lemma lem7047829 : term66 = term39.
Proof. exact (TRANS (@lem7047824) (@lem7047828)). Qed.
Lemma lem7047831 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7047832 : term84 = term89.
Proof. exact (@lem7047831 term8 term8). Qed.
Lemma lem7047833 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7047834 : term69 = term8.
Proof. exact (EQ_MP (@lem7047833) (@lem940073)). Qed.
Lemma lem7047835 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7047836 : term67 = term39.
Proof. exact (MK_COMB (@lem7047835) (@lem7047834)). Qed.
Lemma lem7047837 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7047838 : term89 = term57.
Proof. exact (MK_COMB (@lem7047837) (@lem7047836)). Qed.
Lemma lem7047839 : term84 = term57.
Proof. exact (TRANS (@lem7047832) (@lem7047838)). Qed.
Lemma lem7047840 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7047841 : term90 = term91.
Proof. exact (MK_COMB (@lem7047840) (@lem7047839)). Qed.
Lemma lem7047842 : term86 = term58.
Proof. exact (MK_COMB (@lem7047841) (@lem7047829)). Qed.
Lemma lem7047843 : term85 = term58.
Proof. exact (TRANS (@lem7047821) (@lem7047842)). Qed.
Lemma lem7047844 : term84 = term58.
Proof. exact (TRANS (@lem7047820) (@lem7047843)). Qed.
Lemma lem7047846 (x : real) : (term73 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7047847 : term58 = term57.
Proof. exact (@lem7047846 term57). Qed.
Lemma lem7047848 : term84 = term57.
Proof. exact (TRANS (@lem7047844) (@lem7047847)). Qed.
Lemma lem7047851 (_94144 : int) : (term92 _94144) = (term92 _94144).
Proof. exact (eq_refl (term92 _94144)). Qed.
Lemma lem7047852 (_94144 : int) : (term82 _94144) = (term93 _94144).
Proof. exact (MK_COMB (@lem7047851 _94144) (@lem7047848)). Qed.
Lemma lem7047853 (_94144 : int) : (term81 _94144) = (term93 _94144).
Proof. exact (TRANS (@lem7047811 _94144) (@lem7047852 _94144)). Qed.
Lemma lem7047854 (_94144 : int) : (term40 _94144) = (term40 _94144).
Proof. exact (eq_refl (term40 _94144)). Qed.
Lemma lem7047855 (_94144 : int) : (term80 _94144) = (term94 _94144).
Proof. exact (MK_COMB (@lem7047854 _94144) (@lem7047853 _94144)). Qed.
Lemma lem7047856 (_94144 : int) : (term94 _94144) = (term95 _94144).
Proof. exact (@lem1982763 (real_of_int _94144) (term96 _94144) term57). Qed.
Lemma lem7047857 (_94144 : int) : (term97 _94144) = (term98 _94144).
Proof. exact (@lem1982715 term57 (real_of_int _94144)). Qed.
Lemma lem7047859 (x : nat) : (real_of_num x) = (term53 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7047860 : term39 = term83.
Proof. exact (@lem7047859 term8). Qed.
Lemma lem7047862 (x : nat) : (term55 x) = (term56 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7047863 : term57 = term58.
Proof. exact (@lem7047862 term8). Qed.
Lemma lem7047864 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7047865 : term99 = term100.
Proof. exact (MK_COMB (@lem7047864) (@lem7047863)). Qed.
Lemma lem7047866 : term101 = term102.
Proof. exact (MK_COMB (@lem7047865) (@lem7047860)). Qed.
Lemma lem7047867 : term103.
Proof. exact (@lem1981473 term57 term39 term39 term39 term24 term39). Qed.
Lemma lem7047869 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7047870 : term105 = term106.
Proof. exact (@lem7047869 (NUMERAL 0) term8). Qed.
Lemma lem7047871 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7047872 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7047873 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7047872 h1) (fun h1 : term106 = True => @lem7047871)). Qed.
Lemma lem7047874 : term106 = True.
Proof. exact (EQ_MP (@lem7047873) (@lem7047871)). Qed.
Lemma lem7047875 : term105 = True.
Proof. exact (TRANS (@lem7047870) (@lem7047874)). Qed.
Lemma lem7047876 : True = term105.
Proof. exact (SYM (@lem7047875)). Qed.
Lemma lem7047877 : term105.
Proof. exact (EQ_MP (@lem7047876) (@lem0)). Qed.
Lemma lem7047878 : term108.
Proof. exact (@lem7047867 (@lem7047877)). Qed.
Lemma lem7047880 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7047881 : term105 = term106.
Proof. exact (@lem7047880 (NUMERAL 0) term8). Qed.
Lemma lem7047882 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7047883 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7047884 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7047883 h1) (fun h1 : term106 = True => @lem7047882)). Qed.
Lemma lem7047885 : term106 = True.
Proof. exact (EQ_MP (@lem7047884) (@lem7047882)). Qed.
Lemma lem7047886 : term105 = True.
Proof. exact (TRANS (@lem7047881) (@lem7047885)). Qed.
Lemma lem7047887 : True = term105.
Proof. exact (SYM (@lem7047886)). Qed.
Lemma lem7047888 : term105.
Proof. exact (EQ_MP (@lem7047887) (@lem0)). Qed.
Lemma lem7047889 : term109.
Proof. exact (@lem7047878 (@lem7047888)). Qed.
Lemma lem7047891 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7047892 : term105 = term106.
Proof. exact (@lem7047891 (NUMERAL 0) term8). Qed.
Lemma lem7047893 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7047894 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7047895 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7047894 h1) (fun h1 : term106 = True => @lem7047893)). Qed.
Lemma lem7047896 : term106 = True.
Proof. exact (EQ_MP (@lem7047895) (@lem7047893)). Qed.
Lemma lem7047897 : term105 = True.
Proof. exact (TRANS (@lem7047892) (@lem7047896)). Qed.
Lemma lem7047898 : True = term105.
Proof. exact (SYM (@lem7047897)). Qed.
Lemma lem7047899 : term105.
Proof. exact (EQ_MP (@lem7047898) (@lem0)). Qed.
Lemma lem7047900 : term110.
Proof. exact (@lem7047889 (@lem7047899)). Qed.
Lemma lem7047902 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7047903 : term66 = term67.
Proof. exact (@lem7047902 term8 term8). Qed.
Lemma lem7047904 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7047905 : term69 = term8.
Proof. exact (EQ_MP (@lem7047904) (@lem940073)). Qed.
Lemma lem7047906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7047907 : term67 = term39.
Proof. exact (MK_COMB (@lem7047906) (@lem7047905)). Qed.
Lemma lem7047908 : term66 = term39.
Proof. exact (TRANS (@lem7047903) (@lem7047907)). Qed.
Lemma lem7047910 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7047911 : term84 = term89.
Proof. exact (@lem7047910 term8 term8). Qed.
Lemma lem7047912 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7047913 : term69 = term8.
Proof. exact (EQ_MP (@lem7047912) (@lem940073)). Qed.
Lemma lem7047914 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7047915 : term67 = term39.
Proof. exact (MK_COMB (@lem7047914) (@lem7047913)). Qed.
Lemma lem7047916 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7047917 : term89 = term57.
Proof. exact (MK_COMB (@lem7047916) (@lem7047915)). Qed.
Lemma lem7047918 : term84 = term57.
Proof. exact (TRANS (@lem7047911) (@lem7047917)). Qed.
Lemma lem7047919 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7047920 : term111 = term99.
Proof. exact (MK_COMB (@lem7047919) (@lem7047918)). Qed.
Lemma lem7047921 : term112 = term101.
Proof. exact (MK_COMB (@lem7047920) (@lem7047908)). Qed.
Lemma lem7047923 (m : nat) : (term113 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7047924 : term101 = term24.
Proof. exact (@lem7047923 term8). Qed.
Lemma lem7047925 : term112 = term24.
Proof. exact (TRANS (@lem7047921) (@lem7047924)). Qed.
Lemma lem7047926 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7047927 : term114 = term115.
Proof. exact (MK_COMB (@lem7047926) (@lem7047925)). Qed.
Lemma lem7047928 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem7047929 : term116 = term117.
Proof. exact (MK_COMB (@lem7047927) (@lem7047928)). Qed.
Lemma lem7047931 (x : nat) : (term118 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7047932 : term117 = term24.
Proof. exact (@lem7047931 term8). Qed.
Lemma lem7047933 : term116 = term24.
Proof. exact (TRANS (@lem7047929) (@lem7047932)). Qed.
Lemma lem7047935 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7047936 : term66 = term67.
Proof. exact (@lem7047935 term8 term8). Qed.
Lemma lem7047937 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7047938 : term69 = term8.
Proof. exact (EQ_MP (@lem7047937) (@lem940073)). Qed.
Lemma lem7047939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7047940 : term67 = term39.
Proof. exact (MK_COMB (@lem7047939) (@lem7047938)). Qed.
Lemma lem7047941 : term66 = term39.
Proof. exact (TRANS (@lem7047936) (@lem7047940)). Qed.
Lemma lem7047942 : term115 = term115.
Proof. exact (eq_refl term115). Qed.
Lemma lem7047943 : term119 = term117.
Proof. exact (MK_COMB (@lem7047942) (@lem7047941)). Qed.
Lemma lem7047945 (x : nat) : (term118 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7047946 : term117 = term24.
Proof. exact (@lem7047945 term8). Qed.
Lemma lem7047947 : term119 = term24.
Proof. exact (TRANS (@lem7047943) (@lem7047946)). Qed.
Lemma lem7047948 : term24 = term119.
Proof. exact (SYM (@lem7047947)). Qed.
Lemma lem7047949 : term116 = term119.
Proof. exact (TRANS (@lem7047933) (@lem7047948)). Qed.
Lemma lem7047950 : term102 = term54.
Proof. exact (@lem7047900 (@lem7047949)). Qed.
Lemma lem7047951 : term101 = term54.
Proof. exact (TRANS (@lem7047866) (@lem7047950)). Qed.
Lemma lem7047953 (x : real) : (term73 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7047954 : term54 = term24.
Proof. exact (@lem7047953 term24). Qed.
Lemma lem7047955 : term101 = term24.
Proof. exact (TRANS (@lem7047951) (@lem7047954)). Qed.
Lemma lem7047956 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7047957 : term120 = term115.
Proof. exact (MK_COMB (@lem7047956) (@lem7047955)). Qed.
Lemma lem7047958 (_94144 : int) : (real_of_int _94144) = (real_of_int _94144).
Proof. exact (eq_refl (real_of_int _94144)). Qed.
Lemma lem7047959 (_94144 : int) : (term98 _94144) = (term121 _94144).
Proof. exact (MK_COMB (@lem7047957) (@lem7047958 _94144)). Qed.
Lemma lem7047960 (_94144 : int) : (term97 _94144) = (term121 _94144).
Proof. exact (TRANS (@lem7047857 _94144) (@lem7047959 _94144)). Qed.
Lemma lem7047961 (_94144 : int) : (term121 _94144) = term24.
Proof. exact (@lem1982719 (real_of_int _94144)). Qed.
Lemma lem7047962 (_94144 : int) : (term97 _94144) = term24.
Proof. exact (TRANS (@lem7047960 _94144) (@lem7047961 _94144)). Qed.
Lemma lem7047963 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7047964 (_94144 : int) : (term122 _94144) = term123.
Proof. exact (MK_COMB (@lem7047963) (@lem7047962 _94144)). Qed.
Lemma lem7047965 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem7047966 (_94144 : int) : (term95 _94144) = term124.
Proof. exact (MK_COMB (@lem7047964 _94144) (@lem7047965)). Qed.
Lemma lem7047967 (_94144 : int) : (term94 _94144) = term124.
Proof. exact (TRANS (@lem7047856 _94144) (@lem7047966 _94144)). Qed.
Lemma lem7047968 : term124 = term57.
Proof. exact (@lem1982721 term57). Qed.
Lemma lem7047969 (_94144 : int) : (term94 _94144) = term57.
Proof. exact (TRANS (@lem7047967 _94144) (@lem7047968)). Qed.
Lemma lem7047970 (_94144 : int) : (term80 _94144) = term57.
Proof. exact (TRANS (@lem7047855 _94144) (@lem7047969 _94144)). Qed.
Lemma lem7047972 (_94144 : int) : (term79 _94144) = term57.
Proof. exact (TRANS (@lem7047810 _94144) (@lem7047970 _94144)). Qed.
Lemma lem7047973 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7047974 (_94144 : int) : (term125 _94144) = term126.
Proof. exact (MK_COMB (@lem7047973) (@lem7047972 _94144)). Qed.
Lemma lem7047975 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7047976 (_94144 : int) : (term78 _94144) = term127.
Proof. exact (MK_COMB (@lem7047974 _94144) (@lem7047975)). Qed.
Lemma lem7047977 (_94144 : int) : (term44 _94144) = term127.
Proof. exact (TRANS (@lem7047798 _94144) (@lem7047976 _94144)). Qed.
Lemma lem7047978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7047979 (_94144 : int) : (term46 _94144) = (term128 _94144).
Proof. exact (MK_COMB (@lem7047978) (@lem7047797 _94144)). Qed.
Lemma lem7047980 (_94144 : int) : (term47 _94144) = (term129 _94144).
Proof. exact (MK_COMB (@lem7047979 _94144) (@lem7047977 _94144)). Qed.
Lemma lem7047995 (_94144 : int) : (term49 _94144) = (term129 _94144).
Proof. exact (TRANS (@lem7047749 _94144) (@lem7047980 _94144)). Qed.
Lemma lem7047999 (_94144 : int) (h1 : term129 _94144) : term129 _94144.
Proof. exact (h1). Qed.
Lemma lem7048000 (_94144 : int) (h1 : term129 _94144) : term127.
Proof. exact (proj2 (@lem7047999 _94144 h1)). Qed.
Lemma lem7048003 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7048004 : term127 = term130.
Proof. exact (@lem7048003 term24 term57). Qed.
Lemma lem7048006 (x : nat) : (term55 x) = (term56 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7048007 : term57 = term58.
Proof. exact (@lem7048006 term8). Qed.
Lemma lem7048009 (x : nat) : (real_of_num x) = (term53 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7048010 : term24 = term54.
Proof. exact (@lem7048009 (NUMERAL 0)). Qed.
Lemma lem7048011 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7048012 : term26 = term131.
Proof. exact (MK_COMB (@lem7048011) (@lem7048010)). Qed.
Lemma lem7048013 : term130 = term132.
Proof. exact (MK_COMB (@lem7048012) (@lem7048007)). Qed.
Lemma lem7048014 : term133.
Proof. exact (@lem1980026 term24 term39 term57 term39). Qed.
Lemma lem7048016 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7048017 : term105 = term106.
Proof. exact (@lem7048016 (NUMERAL 0) term8). Qed.
Lemma lem7048018 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7048019 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7048020 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7048019 h1) (fun h1 : term106 = True => @lem7048018)). Qed.
Lemma lem7048021 : term106 = True.
Proof. exact (EQ_MP (@lem7048020) (@lem7048018)). Qed.
Lemma lem7048022 : term105 = True.
Proof. exact (TRANS (@lem7048017) (@lem7048021)). Qed.
Lemma lem7048023 : True = term105.
Proof. exact (SYM (@lem7048022)). Qed.
Lemma lem7048024 : term105.
Proof. exact (EQ_MP (@lem7048023) (@lem0)). Qed.
Lemma lem7048025 : term134.
Proof. exact (@lem7048014 (@lem7048024)). Qed.
Lemma lem7048027 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7048028 : term105 = term106.
Proof. exact (@lem7048027 (NUMERAL 0) term8). Qed.
Lemma lem7048029 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7048030 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7048031 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7048030 h1) (fun h1 : term106 = True => @lem7048029)). Qed.
Lemma lem7048032 : term106 = True.
Proof. exact (EQ_MP (@lem7048031) (@lem7048029)). Qed.
Lemma lem7048033 : term105 = True.
Proof. exact (TRANS (@lem7048028) (@lem7048032)). Qed.
Lemma lem7048034 : True = term105.
Proof. exact (SYM (@lem7048033)). Qed.
Lemma lem7048035 : term105.
Proof. exact (EQ_MP (@lem7048034) (@lem0)). Qed.
Lemma lem7048036 : term132 = term135.
Proof. exact (@lem7048025 (@lem7048035)). Qed.
Lemma lem7048038 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7048039 : term84 = term89.
Proof. exact (@lem7048038 term8 term8). Qed.
Lemma lem7048040 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7048041 : term69 = term8.
Proof. exact (EQ_MP (@lem7048040) (@lem940073)). Qed.
Lemma lem7048042 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7048043 : term67 = term39.
Proof. exact (MK_COMB (@lem7048042) (@lem7048041)). Qed.
Lemma lem7048044 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7048045 : term89 = term57.
Proof. exact (MK_COMB (@lem7048044) (@lem7048043)). Qed.
Lemma lem7048046 : term84 = term57.
Proof. exact (TRANS (@lem7048039) (@lem7048045)). Qed.
Lemma lem7048048 (x : nat) : (term118 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7048049 : term117 = term24.
Proof. exact (@lem7048048 term8). Qed.
Lemma lem7048050 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7048051 : term136 = term26.
Proof. exact (MK_COMB (@lem7048050) (@lem7048049)). Qed.
Lemma lem7048052 : term135 = term130.
Proof. exact (MK_COMB (@lem7048051) (@lem7048046)). Qed.
Lemma lem7048054 (m : nat) (n : nat) : (term137 m n) = (term138 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7048055 : term130 = term139.
Proof. exact (@lem7048054 (NUMERAL 0) term8). Qed.
Lemma lem7048056 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7048057 (h1 : term107 = (BIT1 0)) : (term8 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7048058 : (term107 = (BIT1 0)) = ((term8 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7048057 h1) (fun h1 : (term8 = (NUMERAL 0)) = False => @lem7048056)). Qed.
Lemma lem7048059 : (term8 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7048058) (@lem7048056)). Qed.
Lemma lem7048060 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7048061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7048062 : term140 = (and True).
Proof. exact (MK_COMB (@lem7048061) (@lem7048060)). Qed.
Lemma lem7048063 : term139 = (True /\ False).
Proof. exact (MK_COMB (@lem7048062) (@lem7048059)). Qed.
Lemma lem7048065 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7048066 : term139 = False.
Proof. exact (TRANS (@lem7048063) (@lem7048065)). Qed.
Lemma lem7048067 : term130 = False.
Proof. exact (TRANS (@lem7048055) (@lem7048066)). Qed.
Lemma lem7048068 : term135 = False.
Proof. exact (TRANS (@lem7048052) (@lem7048067)). Qed.
Lemma lem7048069 : term132 = False.
Proof. exact (TRANS (@lem7048036) (@lem7048068)). Qed.
Lemma lem7048070 : term130 = False.
Proof. exact (TRANS (@lem7048013) (@lem7048069)). Qed.
Lemma lem7048071 : term127 = False.
Proof. exact (TRANS (@lem7048004) (@lem7048070)). Qed.
Lemma lem7048072 (_94144 : int) (h1 : term129 _94144) : False.
Proof. exact (EQ_MP (@lem7048071) (@lem7048000 _94144 h1)). Qed.
Lemma lem7048074 (_94144 : int) (h1 : term129 _94144) : term129 _94144.
Proof. exact (h1). Qed.
Lemma lem7048075 (_94144 : int) (h1 : term129 _94144) : (term129 _94144) = False.
Proof. exact (prop_ext (fun h2 : term129 _94144 => @lem7048072 _94144 h1) (fun h2 : False => @lem7048074 _94144 h1)). Qed.
Lemma lem7048076 (_94144 : int) (h1 : term129 _94144) : False.
Proof. exact (EQ_MP (@lem7048075 _94144 h1) (@lem7048074 _94144 h1)). Qed.
Lemma lem7048077 (_94144 : int) (h1 : term49 _94144) : term49 _94144.
Proof. exact (h1). Qed.
Lemma lem7048078 (_94144 : int) (h1 : term49 _94144) : term129 _94144.
Proof. exact (EQ_MP (@lem7047995 _94144) (@lem7048077 _94144 h1)). Qed.
Lemma lem7048079 (_94144 : int) (h1 : term49 _94144) : (term129 _94144) = False.
Proof. exact (prop_ext (fun h2 : term129 _94144 => @lem7048076 _94144 h2) (fun h2 : False => @lem7048078 _94144 h1)). Qed.
Lemma lem7048080 (_94144 : int) (h1 : term49 _94144) : False.
Proof. exact (EQ_MP (@lem7048079 _94144 h1) (@lem7048078 _94144 h1)). Qed.
Lemma lem7048081 (_94144 : int) : term141 _94144.
Proof. exact (fun h0 : term49 _94144 => @lem7048080 _94144 h0). Qed.
Lemma lem7048082 (_94144 : int) : term142 _94144.
Proof. exact (@lem1386578 (term143 _94144)). Qed.
Lemma lem7048085 (_94144 : int) : term143 _94144.
Proof. exact (@lem7048082 _94144 (@lem7048081 _94144)). Qed.
Lemma lem7048086 (_94144 : int) : (term47 _94144) = (term15 _94144).
Proof. exact (SYM (@lem7047729 _94144)). Qed.
Lemma lem7048087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7048088 (_94144 : int) : (term143 _94144) = (term13 _94144).
Proof. exact (MK_COMB (@lem7048087) (@lem7048086 _94144)). Qed.
Lemma lem7048089 (_94144 : int) : term13 _94144.
Proof. exact (EQ_MP (@lem7048088 _94144) (@lem7048085 _94144)). Qed.
Lemma lem7048090 (_94144 : int) : term14 _94144.
Proof. exact (EQ_MP (@lem7047668 _94144) (@lem7048089 _94144)). Qed.
Lemma lem7048091 (x : nat) : term144 x.
Proof. exact (@lem7048090 (int_of_num x)). Qed.
Lemma lem7048092 (x : nat) : term10 x.
Proof. exact (@lem7048091 x (@lem7047667 x)). Qed.
Lemma lem7048093 (x : nat) : (term10 x) = (term1 x).
Proof. exact (SYM (@lem7047664 x)). Qed.
Lemma lem7048094 (x : nat) : term1 x.
Proof. exact (EQ_MP (@lem7048093 x) (@lem7048092 x)). Qed.
Lemma lem7048095 (x : nat) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem7048097 (m : nat) : term145 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7048098 (m : nat) : (term145 m) = (term146 m).
Proof. exact (eq_refl (term145 m)). Qed.
Lemma lem7048099 (m : nat) : term146 m.
Proof. exact (EQ_MP (@lem7048098 m) (@lem7048097 m)). Qed.
Lemma lem7048100 (m : nat) (n : nat) : term147 m n.
Proof. exact (@lem7048099 m n). Qed.
Lemma lem7048101 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (eq_refl (term147 m n)). Qed.
Lemma lem7048102 (m : nat) (n : nat) : term148 m n.
Proof. exact (EQ_MP (@lem7048101 m n) (@lem7048100 m n)). Qed.
Lemma lem7048103 (m : nat) (n : nat) : (term148 m n) = ((term148 m n) = True).
Proof. exact (@lem7 (term148 m n)). Qed.
Lemma lem7048105 (m : nat) : term149 m.
Proof. exact (@lem5451441 m). Qed.
Lemma lem7048106 (m : nat) : (term149 m) = (term150 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem7048107 (m : nat) : term150 m.
Proof. exact (EQ_MP (@lem7048106 m) (@lem7048105 m)). Qed.
Lemma lem7048108 (m : nat) (n : nat) : term151 m n.
Proof. exact (@lem7048107 m n). Qed.
Lemma lem7048109 (n : nat) (m : nat) : (term151 m n) = (term152 n m).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem7048110 (n : nat) (m : nat) : term152 n m.
Proof. exact (EQ_MP (@lem7048109 n m) (@lem7048108 m n)). Qed.
Lemma lem7048111 (n : nat) (m : nat) (p : nat) : term153 n m p.
Proof. exact (@lem7048110 n m p). Qed.
Lemma lem7048112 (n : nat) (m : nat) (p : nat) : (term153 n m p) = (term154 n m p).
Proof. exact (eq_refl (term153 n m p)). Qed.
Lemma lem7048113 (n : nat) (m : nat) (p : nat) : term154 n m p.
Proof. exact (EQ_MP (@lem7048112 n m p) (@lem7048111 n m p)). Qed.
Lemma lem7048114 (n : nat) (m : nat) (p : nat) (q : nat) : term155 n m p q.
Proof. exact (@lem7048113 n m p q). Qed.
Lemma lem7048115 (n : nat) (m : nat) (q : nat) (p : nat) : (term155 n m p q) = ((term156 m n p q) = (term157 n m q p)).
Proof. exact (eq_refl (term155 n m p q)). Qed.
Lemma lem7048117 {_126551 : Type'} (f : _126551 -> nat) : term158 _126551 f.
Proof. exact (@lem6925097 _126551 f). Qed.
Lemma lem7048118 {_126551 : Type'} (f : _126551 -> nat) : (term158 _126551 f) = (term159 _126551 f).
Proof. exact (eq_refl (term158 _126551 f)). Qed.
Lemma lem7048119 {_126551 : Type'} (f : _126551 -> nat) : term159 _126551 f.
Proof. exact (EQ_MP (@lem7048118 _126551 f) (@lem7048117 _126551 f)). Qed.
Lemma lem7048120 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) : term160 _126551 f s.
Proof. exact (@lem7048119 _126551 f s). Qed.
Lemma lem7048121 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : (term160 _126551 f s) = (term161 _126551 s f).
Proof. exact (eq_refl (term160 _126551 f s)). Qed.
Lemma lem7048122 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : term161 _126551 s f.
Proof. exact (EQ_MP (@lem7048121 _126551 s f) (@lem7048120 _126551 f s)). Qed.
Lemma lem7048123 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) (t : _126551 -> Prop) : term162 _126551 s f t.
Proof. exact (@lem7048122 _126551 s f t). Qed.
Lemma lem7048124 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : (term162 _126551 s f t) = (term163 _126551 s t f).
Proof. exact (eq_refl (term162 _126551 s f t)). Qed.
Lemma lem7048125 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : term163 _126551 s t f.
Proof. exact (EQ_MP (@lem7048124 _126551 s t f) (@lem7048123 _126551 s f t)). Qed.
Lemma lem7048126 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term164 _126551 s t) : term164 _126551 s t.
Proof. exact (h1). Qed.
Lemma lem7048127 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term164 _126551 s t) : (term165 _126551 s t f) = (term166 _126551 s t f).
Proof. exact (@lem7048125 _126551 s t f (@lem7048126 _126551 s t h1)). Qed.
Lemma lem7048133 (m : nat) : term167 m.
Proof. exact (@lem5459080 m). Qed.
Lemma lem7048134 (m : nat) : (term167 m) = (term168 m).
Proof. exact (eq_refl (term167 m)). Qed.
Lemma lem7048135 (m : nat) : term168 m.
Proof. exact (EQ_MP (@lem7048134 m) (@lem7048133 m)). Qed.
Lemma lem7048136 (m : nat) (n : nat) : term169 m n.
Proof. exact (@lem7048135 m n). Qed.
Lemma lem7048137 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (eq_refl (term169 m n)). Qed.
Lemma lem7048138 (m : nat) (n : nat) : term170 m n.
Proof. exact (EQ_MP (@lem7048137 m n) (@lem7048136 m n)). Qed.
Lemma lem7048139 (m : nat) (n : nat) (p : nat) : term171 m n p.
Proof. exact (@lem7048138 m n p). Qed.
Lemma lem7048140 (m : nat) (n : nat) (p : nat) : (term171 m n p) = (term172 m n p).
Proof. exact (eq_refl (term171 m n p)). Qed.
Lemma lem7048141 (m : nat) (n : nat) (p : nat) : term172 m n p.
Proof. exact (EQ_MP (@lem7048140 m n p) (@lem7048139 m n p)). Qed.
Lemma lem7048142 (m : nat) (n : nat) (h1 : term173 m n) : term173 m n.
Proof. exact (h1). Qed.
Lemma lem7048143 (p : nat) (m : nat) (n : nat) (h1 : term173 m n) : (term174 m n p) = (term175 m n p).
Proof. exact (@lem7048141 m n p (@lem7048142 m n h1)). Qed.
Lemma lem7048168 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term176 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7048169 (p : Prop) (q : Prop) (p' : Prop) : term177 p q p'.
Proof. exact (fun q' : Prop => @lem7048168 p q p' q'). Qed.
Lemma lem7048170 (p : Prop) (q : Prop) : term178 p q.
Proof. exact (fun p' : Prop => @lem7048169 p q p'). Qed.
Lemma lem7048171 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : term179 m n p f.
Proof. exact (@lem7048170 (term173 m n) ((term180 m n p f) = (term181 m n p f))). Qed.
Lemma lem7048172 (m : nat) (n : nat) (p : nat) (f : nat -> nat) (p' : Prop) : term182 m n p f p'.
Proof. exact (@lem7048171 m n p f p'). Qed.
Lemma lem7048173 (m : nat) (n : nat) (p : nat) (f : nat -> nat) (p' : Prop) : (term182 m n p f p') = (term183 m n p f p').
Proof. exact (eq_refl (term182 m n p f p')). Qed.
Lemma lem7048174 (m : nat) (n : nat) (p : nat) (f : nat -> nat) (p' : Prop) : term183 m n p f p'.
Proof. exact (EQ_MP (@lem7048173 m n p f p') (@lem7048172 m n p f p')). Qed.
Lemma lem7048175 (m : nat) (n : nat) (p : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : term184 m n p f p' q'.
Proof. exact (@lem7048174 m n p f p' q'). Qed.
Lemma lem7048176 (m : nat) (n : nat) (p : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : (term184 m n p f p' q') = (term185 m n p f p' q').
Proof. exact (eq_refl (term184 m n p f p' q')). Qed.
Lemma lem7048177 (m : nat) (n : nat) (p : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : term185 m n p f p' q'.
Proof. exact (EQ_MP (@lem7048176 m n p f p' q') (@lem7048175 m n p f p' q')). Qed.
Lemma lem7048178 (m : nat) (n : nat) : (term173 m n) = (term173 m n).
Proof. exact (eq_refl (term173 m n)). Qed.
Lemma lem7048179 (p : nat) (f : nat -> nat) (m : nat) (n : nat) (q' : Prop) : term186 p f m n q'.
Proof. exact (@lem7048177 m n p f (term173 m n) q'). Qed.
Lemma lem7048180 (p : nat) (f : nat -> nat) (m : nat) (n : nat) (q' : Prop) : term187 p f m n q'.
Proof. exact (@lem7048179 p f m n q' (@lem7048178 m n)). Qed.
Lemma lem7048181 (m : nat) (n : nat) (h1 : term173 m n) : term173 m n.
Proof. exact (h1). Qed.
Lemma lem7048182 (m : nat) (n : nat) : (term173 m n) = ((term173 m n) = True).
Proof. exact (@lem7 (term173 m n)). Qed.
Lemma lem7048187 (m : nat) (n : nat) (p : nat) : term172 m n p.
Proof. exact (fun h0 : term173 m n => @lem7048143 p m n h0). Qed.
Lemma lem7048189 (m : nat) (n : nat) (h1 : term173 m n) : (term173 m n) = True.
Proof. exact (EQ_MP (@lem7048182 m n) (@lem7048181 m n h1)). Qed.
Lemma lem7048190 (m : nat) (n : nat) (h1 : term173 m n) : True = (term173 m n).
Proof. exact (SYM (@lem7048189 m n h1)). Qed.
Lemma lem7048191 (m : nat) (n : nat) (h1 : term173 m n) : term173 m n.
Proof. exact (EQ_MP (@lem7048190 m n h1) (@lem0)). Qed.
Lemma lem7048192 (p : nat) (m : nat) (n : nat) (h1 : term173 m n) : (term174 m n p) = (term175 m n p).
Proof. exact (@lem7048187 m n p (@lem7048191 m n h1)). Qed.
Lemma lem7048198 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7048199 (p : nat) (m : nat) (n : nat) (h1 : term173 m n) : (term188 m n p) = (term189 m n p).
Proof. exact (MK_COMB (@lem7048198) (@lem7048192 p m n h1)). Qed.
Lemma lem7048205 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7048206 (p : nat) (f : nat -> nat) (m : nat) (n : nat) (h1 : term173 m n) : (term180 m n p f) = (term190 m n p f).
Proof. exact (MK_COMB (@lem7048199 p m n h1) (@lem7048205 f)). Qed.
Lemma lem7048208 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : term163 _126551 s t f.
Proof. exact (fun h0 : term164 _126551 s t => @lem7048127 _126551 f s t h0). Qed.
Lemma lem7048209 (s : nat -> Prop) (t : nat -> Prop) (f : nat -> nat) : term191 s t f.
Proof. exact (@lem7048208 nat s t f). Qed.
Lemma lem7048210 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : term192 m n p f.
Proof. exact (@lem7048209 (dotdot m n) (term193 n p) f). Qed.
Lemma lem7048214 (m : nat) (n : nat) : (term148 m n) = True.
Proof. exact (EQ_MP (@lem7048103 m n) (@lem7048102 m n)). Qed.
Lemma lem7048215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7048216 (m : nat) (n : nat) : (term194 m n) = (and True).
Proof. exact (MK_COMB (@lem7048215) (@lem7048214 m n)). Qed.
Lemma lem7048220 (m : nat) (n : nat) : (term148 m n) = True.
Proof. exact (EQ_MP (@lem7048103 m n) (@lem7048102 m n)). Qed.
Lemma lem7048221 (n : nat) (p : nat) : (term195 n p) = True.
Proof. exact (@lem7048220 (term3 n) (Nat.add n p)). Qed.
Lemma lem7048222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7048223 (n : nat) (p : nat) : (term196 n p) = (and True).
Proof. exact (MK_COMB (@lem7048222) (@lem7048221 n p)). Qed.
Lemma lem7048225 (n : nat) (m : nat) (q : nat) (p : nat) : (term156 m n p q) = (term157 n m q p).
Proof. exact (EQ_MP (@lem7048115 n m q p) (@lem7048114 n m p q)). Qed.
Lemma lem7048226 (m : nat) (p : nat) (n : nat) : (term197 m n p) = (term198 m p n).
Proof. exact (@lem7048225 n m (Nat.add n p) (term3 n)). Qed.
Lemma lem7048230 (x : nat) : (term1 x) = True.
Proof. exact (EQ_MP (@lem7048095 x) (@lem7048094 x)). Qed.
Lemma lem7048231 (n : nat) : (term1 n) = True.
Proof. exact (@lem7048230 n). Qed.
Lemma lem7048232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7048233 (n : nat) : (term199 n) = (or True).
Proof. exact (MK_COMB (@lem7048232) (@lem7048231 n)). Qed.
Lemma lem7048240 (m : nat) (p : nat) (n : nat) : (term200 m p n) = (term200 m p n).
Proof. exact (eq_refl (term200 m p n)). Qed.
Lemma lem7048241 (m : nat) (p : nat) (n : nat) : (term198 m p n) = (term201 m p n).
Proof. exact (MK_COMB (@lem7048233 n) (@lem7048240 m p n)). Qed.
Lemma lem7048243 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7048244 (m : nat) (p : nat) (n : nat) : (term201 m p n) = True.
Proof. exact (@lem7048243 (term200 m p n)). Qed.
Lemma lem7048245 (m : nat) (p : nat) (n : nat) : (term198 m p n) = True.
Proof. exact (TRANS (@lem7048241 m p n) (@lem7048244 m p n)). Qed.
Lemma lem7048246 (m : nat) (n : nat) (p : nat) : (term197 m n p) = True.
Proof. exact (TRANS (@lem7048226 m p n) (@lem7048245 m p n)). Qed.
Lemma lem7048247 (m : nat) (n : nat) (p : nat) : (term202 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem7048223 n p) (@lem7048246 m n p)). Qed.
Lemma lem7048249 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7048250 : (True /\ True) = True.
Proof. exact (@lem7048249 True). Qed.
Lemma lem7048251 (m : nat) (n : nat) (p : nat) : (term202 m n p) = True.
Proof. exact (TRANS (@lem7048247 m n p) (@lem7048250)). Qed.
Lemma lem7048252 (m : nat) (n : nat) (p : nat) : (term203 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem7048216 m n) (@lem7048251 m n p)). Qed.
Lemma lem7048254 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7048255 : (True /\ True) = True.
Proof. exact (@lem7048254 True). Qed.
Lemma lem7048256 (m : nat) (n : nat) (p : nat) : (term203 m n p) = True.
Proof. exact (TRANS (@lem7048252 m n p) (@lem7048255)). Qed.
Lemma lem7048257 (m : nat) (n : nat) (p : nat) : True = (term203 m n p).
Proof. exact (SYM (@lem7048256 m n p)). Qed.
Lemma lem7048258 (m : nat) (n : nat) (p : nat) : term203 m n p.
Proof. exact (EQ_MP (@lem7048257 m n p) (@lem0)). Qed.
Lemma lem7048259 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : (term190 m n p f) = (term181 m n p f).
Proof. exact (@lem7048210 m n p f (@lem7048258 m n p)). Qed.
Lemma lem7048265 (p : nat) (f : nat -> nat) (m : nat) (n : nat) (h1 : term173 m n) : (term180 m n p f) = (term181 m n p f).
Proof. exact (TRANS (@lem7048206 p f m n h1) (@lem7048259 m n p f)). Qed.
Lemma lem7048266 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7048267 (p : nat) (f : nat -> nat) (m : nat) (n : nat) (h1 : term173 m n) : (term204 m n p f) = (term205 m n p f).
Proof. exact (MK_COMB (@lem7048266) (@lem7048265 p f m n h1)). Qed.
Lemma lem7048278 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : (term181 m n p f) = (term181 m n p f).
Proof. exact (eq_refl (term181 m n p f)). Qed.
Lemma lem7048279 (p : nat) (f : nat -> nat) (m : nat) (n : nat) (h1 : term173 m n) : ((term180 m n p f) = (term181 m n p f)) = ((term181 m n p f) = (term181 m n p f)).
Proof. exact (MK_COMB (@lem7048267 p f m n h1) (@lem7048278 m n p f)). Qed.
Lemma lem7048281 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7048282 (x : nat) : (x = x) = True.
Proof. exact (@lem7048281 nat x). Qed.
Lemma lem7048283 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : ((term181 m n p f) = (term181 m n p f)) = True.
Proof. exact (@lem7048282 (term181 m n p f)). Qed.
Lemma lem7048284 (p : nat) (f : nat -> nat) (m : nat) (n : nat) (h1 : term173 m n) : ((term180 m n p f) = (term181 m n p f)) = True.
Proof. exact (TRANS (@lem7048279 p f m n h1) (@lem7048283 m n p f)). Qed.
Lemma lem7048285 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : term206 m n p f.
Proof. exact (fun h0 : term173 m n => @lem7048284 p f m n h0). Qed.
Lemma lem7048286 (p : nat) (f : nat -> nat) (m : nat) (n : nat) : term207 p f m n.
Proof. exact (@lem7048180 p f m n True). Qed.
Lemma lem7048287 (p : nat) (f : nat -> nat) (m : nat) (n : nat) : (term208 m n p f) = (term209 m n).
Proof. exact (@lem7048286 p f m n (@lem7048285 m n p f)). Qed.
Lemma lem7048289 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7048290 (m : nat) (n : nat) : (term209 m n) = True.
Proof. exact (@lem7048289 (term173 m n)). Qed.
Lemma lem7048291 (m : nat) (n : nat) (p : nat) (f : nat -> nat) : (term208 m n p f) = True.
Proof. exact (TRANS (@lem7048287 p f m n) (@lem7048290 m n)). Qed.
Lemma lem7048292 (m : nat) (n : nat) (f : nat -> nat) : (term210 m n f) = term211.
Proof. exact (fun_ext (fun p : nat => @lem7048291 m n p f)). Qed.
Lemma lem7048293 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048294 (m : nat) (n : nat) (f : nat -> nat) : (term212 m n f) = term213.
Proof. exact (MK_COMB (@lem7048293) (@lem7048292 m n f)). Qed.
Lemma lem7048296 {A : Type'} (t : Prop) : (term214 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048297 (t : Prop) : (term215 t) = t.
Proof. exact (@lem7048296 nat t). Qed.
Lemma lem7048298 : term213 = True.
Proof. exact (@lem7048297 True). Qed.
Lemma lem7048299 (m : nat) (n : nat) (f : nat -> nat) : (term212 m n f) = True.
Proof. exact (TRANS (@lem7048294 m n f) (@lem7048298)). Qed.
Lemma lem7048300 (m : nat) (f : nat -> nat) : (term216 m f) = term211.
Proof. exact (fun_ext (fun n : nat => @lem7048299 m n f)). Qed.
Lemma lem7048301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048302 (m : nat) (f : nat -> nat) : (term217 m f) = term213.
Proof. exact (MK_COMB (@lem7048301) (@lem7048300 m f)). Qed.
Lemma lem7048304 {A : Type'} (t : Prop) : (term214 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048305 (t : Prop) : (term215 t) = t.
Proof. exact (@lem7048304 nat t). Qed.
Lemma lem7048306 : term213 = True.
Proof. exact (@lem7048305 True). Qed.
Lemma lem7048307 (m : nat) (f : nat -> nat) : (term217 m f) = True.
Proof. exact (TRANS (@lem7048302 m f) (@lem7048306)). Qed.
Lemma lem7048308 (f : nat -> nat) : (term218 f) = term211.
Proof. exact (fun_ext (fun m : nat => @lem7048307 m f)). Qed.
Lemma lem7048309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048310 (f : nat -> nat) : (term219 f) = term213.
Proof. exact (MK_COMB (@lem7048309) (@lem7048308 f)). Qed.
Lemma lem7048312 {A : Type'} (t : Prop) : (term214 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048313 (t : Prop) : (term215 t) = t.
Proof. exact (@lem7048312 nat t). Qed.
Lemma lem7048314 : term213 = True.
Proof. exact (@lem7048313 True). Qed.
Lemma lem7048315 (f : nat -> nat) : (term219 f) = True.
Proof. exact (TRANS (@lem7048310 f) (@lem7048314)). Qed.
Lemma lem7048316 : term220 = term221.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7048315 f)). Qed.
Lemma lem7048317 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7048318 : term222 = term223.
Proof. exact (MK_COMB (@lem7048317) (@lem7048316)). Qed.
Lemma lem7048320 {A : Type'} (t : Prop) : (term214 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048321 (t : Prop) : (term224 t) = t.
Proof. exact (@lem7048320 (nat -> nat) t). Qed.
Lemma lem7048322 : term223 = True.
Proof. exact (@lem7048321 True). Qed.
Lemma lem7048323 : term222 = True.
Proof. exact (TRANS (@lem7048318) (@lem7048322)). Qed.
Lemma lem7048324 : True = term222.
Proof. exact (SYM (@lem7048323)). Qed.
Lemma lem7048325 : term222.
Proof. exact (EQ_MP (@lem7048324) (@lem0)). Qed.
